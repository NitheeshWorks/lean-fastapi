import LeanFastapi.DataTypes.Params

/-!
# DataTypes: the OpenAPI document

The part of OpenAPI 3.1 (`fastapi/openapi/models.py`) that FastAPI emits for
the supported path operations, as an abstract syntax:

* `OSchema` is a JSON Schema as it appears in the document: pydantic's
  schemas with every model replaced by a `$ref` to `#/components/schemas/`
  (`OSchema.ref`), plus the two shapes of the validation-error components
  (`array`, `objectAny`);
* `Operation`, `Parameter`, `RequestBody`, `ResponseSpec`, `Info` are the
  OpenAPI objects;
* `Components.schemas` is sorted by name, strictly, so names are unique: the
  invariant is the field `sorted` (`openapi_components_sorted`);
* `OpenAPI.paths` lists the operations as `(path, method, operation)`; the
  JSON form groups them by path.

`OpenAPI.toJson` (`RepoImpl/OpenApi.lean`) prints the document in the key
order FastAPI's `app.openapi()` has.
-/

namespace LeanFastapi

open LeanJson (Json)
open LeanPydantic (Keyword)

/-- Field-level annotations of a schema. `explicitTitle` says the title was
given by the user (`Path(title=...)`), which pydantic writes before the
other annotations; a title FastAPI computes is written last. -/
structure Annotations where
  title : Option String := none
  explicitTitle : Bool := false
  description : Option String := none
  deprecated : Bool := false
  default : Option Json := none

/-- A JSON Schema inside an OpenAPI document. -/
inductive OSchema where
  /-- `{}` -/
  | any
  | null
  | boolean
  | integer (kws : List Keyword)
  | number (kws : List Keyword)
  | string (kws : List Keyword)
  | anyOf (alts : List OSchema)
  | array (items : OSchema)
  /-- A model's own schema (a component's body). -/
  | object (title : String) (props : List (String × OSchema)) (required : List String)
  /-- `{"type": "object"}` -/
  | objectAny
  /-- `{"$ref": "#/components/schemas/<name>"}` -/
  | ref (name : String)
  | ann (s : OSchema) (a : Annotations)

instance : Inhabited OSchema := ⟨.any⟩

/-- An operation parameter (`Parameter`). -/
structure Parameter where
  name : String
  «in» : Source
  required : Bool
  schema : OSchema
  description : Option String := none
  deprecated : Bool := false

/-- `content: {media_type: {schema: ...}}` with one media type. -/
structure MediaContent where
  mediaType : String := "application/json"
  schema : OSchema

/-- An operation's `requestBody`. -/
structure RequestBody where
  content : MediaContent
  required : Bool

/-- One entry of an operation's `responses`. -/
structure ResponseSpec where
  description : String
  content : Option MediaContent := none

/-- An `Operation` object. -/
structure Operation where
  tags : List String := []
  summary : String
  description : Option String := none
  operationId : String
  parameters : List Parameter := []
  requestBody : Option RequestBody := none
  /-- By status code, as strings (`"200"`, `"422"`). -/
  responses : List (String × ResponseSpec) := []
  deprecated : Bool := false

/-- The `info` object. -/
structure Info where
  title : String
  version : String
  summary : Option String := none
  description : Option String := none

/-- `components.schemas`, sorted by name with no name twice. -/
structure Components where
  schemas : List (String × OSchema) := []
  sorted : (schemas.map Prod.fst).Pairwise (· < ·) := by simp

/-- An OpenAPI document. -/
structure OpenAPI where
  openapi : String := "3.1.0"
  info : Info
  /-- The operations, as `(path, method, operation)`, `method` lower-case. -/
  paths : List (String × String × Operation)
  components : Components

end LeanFastapi
