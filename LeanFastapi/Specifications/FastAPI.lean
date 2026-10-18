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
      | some v => LeanPydantic.fromJson {} v = .ok a

/-- Extraction of a product succeeds exactly when each parameter's does. -/
def ExtractConsOkIff : Prop :=
  ∀ {α β : Type} [FromJson α] [ToJson α] [JsonSchema α] (p : Param α) (rest : Params β) (inp : Inputs) (a : α)
    (b : β), (Params.cons p rest).extract inp = .ok (a, b) ↔ p.validator inp = .ok a ∧ rest.extract inp = .ok b

/-- `extract_422`: failed extraction is a 422 carrying exactly its errors. -/
def Extract422 : Prop :=
  ∀ {β γ : Type} [IntoResult γ] (e : Endpoint β γ) (req : LeanStarlette.Request) (b : BodyInput)
    (es : List RequestError), e.body req = .ok b → e.params.extract (Inputs.ofRequest req b) = .error es →
      LeanStarlette.exceptionMiddleware defaultExceptionHandlers e.app req =
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

end Spec

end LeanFastapi
