import LeanFastapi.RepoImpl.Dependencies

/-!
# RepoImpl: path operations

A path operation function becomes an `App` (`get_request_handler` in
`fastapi/routing.py`):

1. read the body, when the operation or one of its dependencies has a body
   parameter (`readBody`);
2. solve the operation's dependency tree (the application's dependencies
   first, then the route's and the function's, with the overrides in force
   compiled in) and parameters (`solve_dependencies`); any error is a
   `RequestValidationError` carrying all of them;
3. call the function with the values;
4. turn what it returned into a response: a `Response` is sent as it is;
   any other value is converted to JSON (`jsonable_encoder`) and, when the
   operation has a `response_model`, validated against it and dumped
   (`serialize_response`), else sent as a `JSONResponse`;
5. unwind the exit stacks of `yield` dependencies around all of it
   (`finish`).

`Handler α` is the monad path operation functions run in: Starlette's
`AppM` (`IO` with `Exception`s), so a function `throw`s an `HTTPException`.

`APIRoute` keeps the compiled `App` together with everything the OpenAPI
generator reads: the parameter descriptions, the response model's schema
and the operation's metadata.
-/

namespace LeanFastapi

open LeanJson (Json)
open LeanPydantic (FromJson ToJson JsonSchema)
open LeanStarlette (Request Response Exception App AppM)

/-- What a path operation function returns: a value FastAPI serialises, or a
response it sends unchanged. -/
inductive EndpointResult where
  | json (j : Json)
  | response (r : Response)

/-- Types a path operation can return. Every type with a JSON form is one
(`jsonable_encoder`); a `Response` is sent unchanged. -/
class IntoResult (γ : Type) where
  intoResult : γ → EndpointResult

instance (priority := low) {γ : Type} [LeanJson.IntoJson γ] : IntoResult γ := ⟨fun x => .json (LeanJson.intoJson x)⟩
instance : IntoResult Response := ⟨.response⟩

/-- A pydantic value is returned as its round-trip dump (by alias, non-finite
floats kept as `Infinity`/`NaN`), which a response model then validates
again: FastAPI validates the returned object itself, so nothing the value
holds is lost on the way. -/
instance {γ : Type} [LeanPydantic.ToJson γ] : IntoResult γ :=
  ⟨fun x => .json (LeanPydantic.toJson { LeanPydantic.DumpOpts.roundTrip with ser_json_inf_nan := .constants } x)⟩

instance : IntoResult Json := ⟨.json⟩

/-- A response model: its JSON Schema, and `serialize_response`: validate the
returned value against the model (errors under `"response"`), then dump the
validated value. -/
structure ResponseModel where
  schema : LeanPydantic.Schema
  serialize : Json → Except (List RequestError) Json

/-- The dump options of `response_model_include`, `response_model_exclude`,
`response_model_by_alias` (FastAPI's default `True`),
`response_model_exclude_unset`, `response_model_exclude_defaults` and
`response_model_exclude_none`. -/
def responseDumpOpts (incl : Option (List String) := none) (excl : List String := [])
    (by_alias : Bool := true) (exclude_unset exclude_defaults exclude_none : Bool := false) :
    LeanPydantic.DumpOpts :=
  { «include» := incl, exclude := excl, by_alias, exclude_unset, exclude_defaults, exclude_none }

/-- The response model for the type `β`, dumped with `opts`
(`response_model_exclude_none` and the others; by alias, as FastAPI). -/
def ResponseModel.of (β : Type) [FromJson β] [ToJson β] [JsonSchema β]
    (opts : LeanPydantic.DumpOpts := responseDumpOpts) :
    ResponseModel where
  schema := JsonSchema.schema β
  serialize j :=
    match LeanPydantic.fromJson (α := β) fastapiCfg j with
    | .ok b => .ok (LeanPydantic.toJson opts b)
    | .error es => .error (es.map fun e => Keel.Located.within (.key "response") (RequestError.ofDetails e))

/-- A status code with its validity, as a route stores it. -/
abbrev Status := {n : Nat // LeanStarlette.StatusCode.Valid n}

/-- The response for a returned value (`serialize_response` and the
response class). -/
def renderResult (model : Option ResponseModel) (status : Status) : EndpointResult → AppM Response
  | .response r => pure r
  | .json j =>
    match model with
    | none => pure (LeanStarlette.JSONResponse j status.val (h := status.property))
    | some m =>
      match m.serialize j with
      | .ok out =>
        pure (Response.make (LeanStarlette.Responses.jsonBody out) status.val [] (some "application/json") status.property)
      | .error es => throw (ResponseValidationError es)

/-- A path operation: its dependency tree, whose root is the operation's own
arguments (`Dep`, with cache slots `σ`), its function, its response model
and status code. -/
structure Endpoint (σ : List Type) (β γ : Type) where
  dep : Dep σ β
  call : β → Handler γ
  response_model : Option ResponseModel := none
  status_code : Status := ⟨200, by decide⟩

/-! ## The parameters of a dependency tree -/

/-- What `_get_openapi_dependency_data` collects: the cache keys visited,
the parameters (outside the body) in the order met, and the security
requirements (scheme name, scheme, scopes). -/
structure FlatDeps where
  visited : List CacheKey := []
  params : List ParamInfo := []
  security : List (String × SecurityScheme × List String) := []

/-- The scopes `a`, then those of `b` not already there (`_get_oauth_scopes`). -/
def mergeScopes (a b : List String) : List String :=
  b.foldl (fun acc s => if acc.contains s then acc else acc ++ [s]) a

/-- The parameters at one level of a tree. -/
def ownParams : List DepInfo → List ParamInfo
  | [] => []
  | .param p :: ds => p :: ownParams ds
  | .sub .. :: ds => ownParams ds

mutual

/-- Visit one sub-dependency, under the scopes `scopes` of the way to it:
skipped when its key was visited; otherwise its parameters, its scheme (with
the scopes on the way to it) and then its own sub-dependencies. -/
def FlatDeps.node (scopes : List String) : DepInfo → FlatDeps → FlatDeps
  | .param _, w => w
  | .sub key own scheme args, w =>
    if w.visited.contains key then w
    else
      let s := mergeScopes scopes own
      FlatDeps.list s args
        { w with visited := w.visited ++ [key], params := w.params ++ ownParams args,
                 security := w.security ++ (scheme.map fun (n, m) => (n, m, s)).toList }

/-- Visit sub-dependencies in order. -/
def FlatDeps.list (scopes : List String) : List DepInfo → FlatDeps → FlatDeps
  | [], w => w
  | d :: ds, w => FlatDeps.list scopes ds (FlatDeps.node scopes d w)

end

/-- **`_get_openapi_dependency_data`**: a preorder walk of the tree (the
root's parameters, then each sub-dependency's, depth first), each cache key
once. -/
def FlatDeps.of (root : List DepInfo) : FlatDeps :=
  FlatDeps.list [] root { params := ownParams root }

mutual

/-- `_get_flat_body_params`: every body parameter, depth first (each use of
a dependency counts). -/
def bodyParamsOf : DepInfo → List ParamInfo
  | .param p => if p.source == .body then [p] else []
  | .sub _ _ _ args => bodyParamsList args

def bodyParamsList : List DepInfo → List ParamInfo
  | [] => []
  | d :: ds => bodyParamsOf d ++ bodyParamsList ds

end

/-- The body parameters of a tree, the dependant's own first. -/
def flatBodyParams (root : List DepInfo) : List ParamInfo :=
  (ownParams root).filter (·.source == .body) ++
    bodyParamsList (root.filter fun | .sub .. => true | .param _ => false)

/-- **The operation's parameters** (`get_flat_params` and the body): path,
query, header and cookie parameters of the whole tree, each kind in the
order met, then the body parameters. -/
def flatParams (root : List DepInfo) : List ParamInfo :=
  let ps := (FlatDeps.of root).params.filter (·.source != .body)
  ps.mergeSort (fun a b => a.source.rank ≤ b.source.rank) ++ flatBodyParams root

namespace Endpoint

variable {σ : List Type} {β γ : Type}

/-- Whether the operation reads the body. -/
def hasBody (e : Endpoint σ β γ) : Bool := !(flatBodyParams e.dep.info).isEmpty

/-- Whether its body is a form (`is_body_form`). -/
def hasForm (e : Endpoint σ β γ) : Bool := (flatBodyParams e.dep.info).any (isFormMediaType ·.media_type)

/-- The body the operation reads: nothing, a form (`readForm`), or what
`readBody` gives. -/
def body (e : Endpoint σ β γ) (req : Request) : Except BodyError BodyInput :=
  if e.hasForm then readForm req else if e.hasBody then readBody req else .ok .none

/-- The operation's tree: its values, or `none` when something failed to
validate. -/
def solve (e : Endpoint σ β γ) : SolveM σ (Option β) := e.dep.run

/-- After the solve: when nothing failed, call the function and render its
result; otherwise raise `RequestValidationError` with every error. -/
def respond [IntoResult γ] (e : Endpoint σ β γ) (v? : Option β) : SolveM σ Response := do
  let errors := (← get).shared.errors
  match v?, errors with
  | some v, [] => do
    let out ← SolveM.lift (e.call v)
    SolveM.lift (renderResult e.response_model e.status_code (IntoResult.intoResult out))
  | _, _ => throw (RequestValidationError errors)

/-- What a route's solve reads: the request and its inputs. -/
def ctx (req : Request) (body : BodyInput) : Ctx :=
  { env := { request := req, inputs := Inputs.ofRequest req body } }

/-- **The solve of a request**, from an empty cache and empty exit stacks:
the values (or `none`), or an exception a dependency raised, and the state
it leaves (errors, exits, cache). -/
def solveIO (e : Endpoint σ β γ) (req : Request) (body : BodyInput) :
    IO (Except Exception (Option β) × SolveState σ) :=
  ((e.solve.run (ctx req body)).run).run { shared := {}, cache := Cache.empty σ }

/-- **The operation as an application**: read the body; solve; respond; then
unwind the exit stacks (`finish`) with the outcome. -/
def app [IntoResult γ] (e : Endpoint σ β γ) : App := fun req =>
  match e.body req with
  | .error (.invalid err) => throw (RequestValidationError [err])
  | .error .unparsable => throw (HTTPException 400 "There was an error parsing the body")
  | .error (.badForm detail) => throw (HTTPException 400 detail)
  | .ok body => ExceptT.mk do
    let (r, st) ← e.solveIO req body
    let (outcome, st) ← match r with
      | .ok v? => (((e.respond v?).run (ctx req body)).run).run st
      | .error ex => pure (.error ex, st)
    (finish outcome st.shared).run

end Endpoint

/-- A path operation as the application's router and the OpenAPI generator
see it (`fastapi.routing.APIRoute`). -/
structure APIRoute where
  /-- The path template, e.g. `/items/{item_id}`. -/
  path : String
  /-- The HTTP methods, upper-case. -/
  methods : List String
  /-- `route.name`: the function's name. -/
  name : String
  /-- The application. -/
  endpoint : App
  /-- The application dependencies and overrides it was compiled with
  (`FastAPI.signature`): an application serves it only under the same
  ones, so an override is never silently ignored. -/
  compiledWith : List String := []
  /-- The dependency tree: the operation's parameters and sub-dependencies. -/
  deps : List DepInfo := []
  /-- The parameters of the whole tree (`flatParams deps`). -/
  params : List ParamInfo := []
  /-- The response model's schema. -/
  response_model : Option LeanPydantic.Schema := none
  status_code : Option Nat := none
  tags : List String := []
  summary : Option String := none
  description : Option String := none
  response_description : String := "Successful Response"
  deprecated : Bool := false
  operation_id : Option String := none
  include_in_schema : Bool := true

/-- The route of an endpoint, with the operation's metadata
(`APIRoute.__init__`). Methods are upper-cased. -/
def APIRoute.make {σ : List Type} {β γ : Type} [IntoResult γ] (e : Endpoint σ β γ) (path : String) (methods : List String)
    (name : String) (explicitStatus : Bool := false) (tags : List String := []) (summary : Option String := none)
    (description : Option String := none) (response_description : String := "Successful Response")
    (deprecated : Bool := false) (operation_id : Option String := none) (include_in_schema : Bool := true) :
    APIRoute where
  path
  methods := methods.map String.toUpper
  name
  endpoint := e.app
  deps := e.dep.info
  params := flatParams e.dep.info
  response_model := e.response_model.map (·.schema)
  status_code := if explicitStatus then some e.status_code.val else none
  tags
  summary
  description
  response_description
  deprecated
  operation_id
  include_in_schema

/-- The route as compiled for an application with the dependencies and
overrides `sig` (`signatureOf`). -/
def APIRoute.compiled (sig : List String) (r : APIRoute) : APIRoute := { r with compiledWith := sig }

/-- The security requirements of the route's tree. -/
def APIRoute.security (r : APIRoute) : List (String × SecurityScheme × List String) :=
  (FlatDeps.of r.deps).security

end LeanFastapi
