import LeanFastapi.RepoImpl.Exceptions

/-!
# RepoImpl: path operations

A path operation function becomes an `App` (`get_request_handler` in
`fastapi/routing.py`):

1. read the body, when the operation has a body parameter (`readBody`);
2. extract and validate every parameter (`Params.extract`); any error is a
   `RequestValidationError` carrying all of them;
3. call the function with the values;
4. turn what it returned into a response: a `Response` is sent as it is;
   any other value is converted to JSON (`jsonable_encoder`) and, when the
   operation has a `response_model`, validated against it and dumped
   (`serialize_response`), else sent as a `JSONResponse`.

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

/-- The monad of path operation functions. -/
abbrev Handler (α : Type) : Type := AppM α

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
    match LeanPydantic.fromJson (α := β) {} j with
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

/-- A path operation: its parameters, its function, its response model and
status code. -/
structure Endpoint (β γ : Type) where
  params : Params β
  call : β → Request → Handler γ
  response_model : Option ResponseModel := none
  status_code : Status := ⟨200, by decide⟩

namespace Endpoint

variable {β γ : Type}

/-- Whether the operation reads the body. -/
def hasBody (e : Endpoint β γ) : Bool := e.params.infos.any (·.source == .body)

/-- The body the operation reads: nothing, or what `readBody` gives. -/
def body (e : Endpoint β γ) (req : Request) : Except BodyError BodyInput :=
  if e.hasBody then readBody req else .ok .none

/-- **The operation as an application.** -/
def app [IntoResult γ] (e : Endpoint β γ) : App := fun req =>
  match e.body req with
  | .error (.invalid err) => throw (RequestValidationError [err])
  | .error .unparsable => throw (HTTPException 400 "There was an error parsing the body")
  | .ok body =>
    match e.params.extract (Inputs.ofRequest req body) with
    | .error es => throw (RequestValidationError es)
    | .ok v => do
      let out ← e.call v req
      renderResult e.response_model e.status_code (IntoResult.intoResult out)

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
  endpoint : App
  /-- The parameters, in `Source.rank` order. -/
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
def APIRoute.make {β γ : Type} [IntoResult γ] (e : Endpoint β γ) (path : String) (methods : List String)
    (name : String) (explicitStatus : Bool := false) (tags : List String := []) (summary : Option String := none)
    (description : Option String := none) (response_description : String := "Successful Response")
    (deprecated : Bool := false) (operation_id : Option String := none) (include_in_schema : Bool := true) :
    APIRoute where
  path
  methods := methods.map String.toUpper
  name
  endpoint := e.app
  params := e.params.infos
  response_model := e.response_model.map (·.schema)
  status_code := if explicitStatus then some e.status_code.val else none
  tags
  summary
  description
  response_description
  deprecated
  operation_id
  include_in_schema

end LeanFastapi
