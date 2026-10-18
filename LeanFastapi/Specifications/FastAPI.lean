import LeanFastapi.RepoImpl

/-!
# Specifications: what lean-fastapi promises

Each property is stated about the public functions, for every application,
route, parameter list or response model; `Proofs/Verified.lean` holds a
proof of each.
-/

namespace LeanFastapi

open LeanJson (Json)
open LeanPydantic (FromJson ToJson JsonSchema LawfulJson Conforms)

namespace Spec

/-! ## Parameters and extraction -/

/-- `params_to_args_loc`: every error is located under a declared parameter. -/
def ParamsToArgsLoc : Prop :=
  ∀ {β : Type} (ps : Params β) (inp : Inputs) (es : List RequestError),
    ps.extract inp = .error es → ∀ e ∈ es, ∃ i ∈ ps.infos, i.loc <+: e.loc

/-- `extract_sound`: a parameter's value is its validated raw value, or its
default when absent. -/
def ExtractSound : Prop :=
  ∀ {α : Type} [FromJson α] (p : Param α) (inp : Inputs) (a : α),
    p.validator inp = .ok a ↔
      match p.raw inp with
      | none => p.default = some a
      | some v => LeanPydantic.fromJson fastapiCfg v = .ok a

/-- Extraction of a product succeeds exactly when each parameter's does. -/
def ExtractConsOkIff : Prop :=
  ∀ {α β : Type} [FromJson α] [ToJson α] [JsonSchema α] (p : Param α) (rest : Params β) (inp : Inputs) (a : α)
    (b : β), (Params.cons p rest).extract inp = .ok (a, b) ↔ p.validator inp = .ok a ∧ rest.extract inp = .ok b

/-- `extract_422`: a solve that records validation errors (and enters no
`yield` dependency) is a 422 carrying exactly its errors. -/
def Extract422 : Prop :=
  ∀ {σ : List Type} {β γ : Type} [IntoResult γ] (e : Endpoint σ β γ) (env : RouteEnv)
    (req : LeanStarlette.Request) (b : BodyInput) (v? : Option β) (st : SolveState σ) (es : List RequestError),
    e.body req = .ok b → e.solveIO env req b = pure (.ok v?, st) → st.shared = { errors := es } → es ≠ [] →
      LeanStarlette.exceptionMiddleware defaultExceptionHandlers (e.app env) req =
        pure (validationErrorResponse (errorsJson es))

/-- `infer_param`: FastAPI's classification of an unwrapped argument. -/
def InferParam : Prop :=
  ∀ (name : String) (inPath isModel : Bool),
    inferParam { name, inPath, isModel } = .param (if inPath then .path else if isModel then .body else .query)

/-- `header_alias_hyphen`: a header parameter's wire name. -/
def HeaderAliasHyphen : Prop :=
  ∀ name : String,
    headerParamAlias name none true = String.ofList (name.toList.map fun c => if c = '_' then '-' else c)

/-! ## Response models -/

/-- `serialize_response_conforms`: what a response model sends conforms to
its schema. -/
def SerializeResponseConforms : Prop :=
  ∀ (β : Type) [FromJson β] [ToJson β] [JsonSchema β] [LawfulJson β] (j out : Json),
    (ResponseModel.of β).serialize j = .ok out → Conforms (JsonSchema.schema β) out

/-! ## OpenAPI, for every application -/

/-- `openapi_all_routes`: the document's operations are the routes'. -/
def OpenapiAllRoutes : Prop :=
  ∀ (app : FastAPI) (p m : String),
    (p, m) ∈ app.openapiSchema.keys ↔
      ∃ r ∈ app.routes, r.include_in_schema = true ∧ pathFormat r.path = p ∧ m ∈ r.methods.map String.toLower

/-- `openapi_refs_resolve`: every `$ref` names a component. -/
def OpenapiRefsResolve : Prop :=
  ∀ (app : FastAPI), ∀ n ∈ app.openapiSchema.refs, n ∈ app.openapiSchema.componentNames

/-- `openapi_components_sorted`: components sorted by name, each once. -/
def OpenapiComponentsSorted : Prop :=
  ∀ (app : FastAPI), app.openapiSchema.componentNames.Pairwise (· < ·)

/-- `operationId_unique`: distinct route operation ids stay distinct. -/
def OperationIdUnique : Prop :=
  ∀ (app : FastAPI), ((app.routes.flatMap APIRoute.operations).map (·.2.2.operationId)).Nodup →
    app.openapiSchema.operationIds.Nodup

/-- Every operation of the document is a route's. -/
def OpenapiOperationOfRoute : Prop :=
  ∀ (app : FastAPI), ∀ e ∈ app.openapiSchema.paths,
    ∃ r ∈ app.routes, r.include_in_schema = true ∧ ∃ m ∈ r.methods, e = (pathFormat r.path, m.toLower, r.operation m)

/-- `openapi_422_iff`: the `422` response exactly for validating routes. -/
def Openapi422Iff : Prop :=
  ∀ (r : APIRoute) (m : String), "422" ∈ (r.operation m).responses.map Prod.fst ↔ r.params ≠ [] ∨ r.statusKey = "422"

/-- `openapi_params_match`: documented parameters are the declared ones. -/
def OpenapiParamsMatch : Prop :=
  ∀ (r : APIRoute) (m : String) (i : Source) (n : String),
    (i, n) ∈ (r.operation m).parameters.map Parameter.key ↔
      ∃ p ∈ r.params, p.source ≠ .body ∧ p.include_in_schema = true ∧ p.source = i ∧ p.alias = n

/-! ## Dependencies -/

/-- `solve_order`: a dependant's parts are solved in order, each from the
state the previous left, the later even after the earlier failed. -/
def SolveOrder : Prop :=
  ∀ {σ : List Type} {α β : Type} (a : Dep σ α) (b : Dep σ β) (c : Ctx) (s s₁ s₂ : SolveState σ) (x : Option α)
    (y : Option β), a.runAt c s = pure (.ok x, s₁) → b.runAt c s₁ = pure (.ok y, s₂) →
    (Dep.both a b).runAt c s = pure (.ok (do Pure.pure (← x, ← y)), s₂)

/-- A dependant's parameters record exactly their extraction's errors. -/
def ParamsErrors : Prop :=
  ∀ {σ : List Type} {α : Type} (ps : Params α) (c : Ctx) (s : SolveState σ) (es : List RequestError),
    ps.extract c.env.inputs = .error es →
    (Dep.params ps).runAt c s = pure (.ok none, { s with shared := { s.shared with errors := s.shared.errors ++ es } })

/-- `cache_same_key`: a cached key is not called again. -/
def CacheSameKey : Prop :=
  ∀ {σ : List Type} {α : Type} (slot : Slot σ α) (compute : SolveM σ α) (c : Ctx) (s : SolveState σ) (v : α),
    s.cache.get slot = some v → (Dep.cached slot true compute).runAt c s = pure (.ok (some v), s)

/-- A computed value is cached under its key. -/
def CachedStores : Prop :=
  ∀ {σ : List Type} {α : Type} (slot : Slot σ α) (useCache : Bool) (compute : SolveM σ α) (c : Ctx)
    (s s₁ : SolveState σ) (v : α), s.cache.get slot = none → compute.runAt c s = pure (.ok v, s₁) →
    s₁.cache.get slot = none →
    (Dep.cached slot useCache compute).runAt c s = pure (.ok (some v), { s₁ with cache := s₁.cache.set slot v })

/-- `override_replaces`: with an override, the dependency's own function and
arguments play no part. -/
def OverrideReplaces : Prop :=
  ∀ {σ : List Type} {α β β' : Type} [LeanPydantic.FromJson α] (key : CacheKey) (slot : Slot σ α) (useCache : Bool)
    (own : List String) (scheme : Option (String × SecurityScheme)) (f : Dep.Invoke β α) (arg : Dep σ β)
    (f' : Dep.Invoke β' α) (arg' : Dep σ β') (c : Ctx) (o : ErasedRun) (s : SolveState σ),
    c.overrides.lookup key.call = some o →
    (Dep.call key slot useCache own scheme f arg).runAt c s = (Dep.call key slot useCache own scheme f' arg').runAt c s

/-- `cleanup_reverse`: exits run in the reverse of the order entered. -/
def CleanupReverse : Prop :=
  ∀ (r : Exit → Option LeanStarlette.Exception → Except LeanStarlette.Exception Unit) (sh : Shared) (xs : List Exit)
    (e : Option LeanStarlette.Exception),
    ((closeWith (tracedRun r) (xs.foldl (fun sh x => sh.push .request x) sh).request e).run []).2 =
      xs.reverse ++ sh.request

/-- `function_scope_not_outlive`: function-scoped exits all run before any
request-scoped one, each once, whatever the outcome. -/
def FunctionScopeNotOutlive : Prop :=
  ∀ {ε : Type} (r : ε → Option LeanStarlette.Exception → Except LeanStarlette.Exception Unit)
    (outcome : Except LeanStarlette.Exception LeanStarlette.Response) (function request : List ε),
    ((finishWith (tracedRun r) outcome function request).run []).2 = function ++ request

/-- `security_scopes_accumulate`: a scheme's requirement carries the scopes
of the way to it, then its own. -/
def SecurityScopesAccumulate : Prop :=
  ∀ (scopes own : List String) (key : CacheKey) (n : String) (m : SecurityScheme) (args : List DepInfo)
    (w : FlatDeps), key ∉ w.visited →
    (n, m, mergeScopes scopes own) ∈ (FlatDeps.node scopes (.sub key own (some (n, m)) args) w).security

/-- Accumulated scopes are those of either list. -/
def MergeScopesMem : Prop :=
  ∀ (a b : List String) (s : String), s ∈ mergeScopes a b ↔ s ∈ a ∨ s ∈ b

/-! ## Security -/

/-- `bearer_parse`: `get_authorization_scheme_param` splits at the first
space and strips the parameter. -/
def BearerParse : Prop :=
  ∀ (scheme param : String), ' ' ∉ scheme.toList →
    authorizationSchemeParam (some (scheme ++ " " ++ param)) = (scheme, pyStrip param)

/-- `basic_base64_roundtrip`: `HTTPBasic` reads back the credentials a
client encodes. -/
def BasicBase64Roundtrip : Prop :=
  ∀ (username password : String), (∀ c ∈ username.toList, c.toNat < 128) →
    (∀ c ∈ password.toList, c.toNat < 128) → ':' ∉ username.toList →
    basicCredentials (basicToken username password) = some { username, password }

/-- `apikey_sources`: an API key is read where a parameter of its location
is. -/
def ApikeySources : Prop :=
  ∀ (location : APIKeyIn) (name : String) (req : LeanStarlette.Request) (body : BodyInput),
    (apiKeyValue location name req).map .str = (Inputs.ofRequest req body).lookup location.source name

end Spec

end LeanFastapi
