import LeanFastapi.DataTypes.OpenApi
import LeanFastapi.RepoImpl.Names
import LeanFastapi.RepoImpl.Sorted

/-!
# RepoImpl: generating and printing the OpenAPI document

`fastapi/openapi/utils.py`, `get_openapi`, for the supported operations:

* every model a route mentions (in a parameter, the body or the response
  model, at any depth) becomes a component under its name, and every use of
  it a `$ref` (`OSchema.ofSchema`, `OSchema.models`);
* each included route contributes one operation per method, under its path
  format; a later route with the same path and method replaces the earlier
  operation in place (`paths.setdefault(path, {}).update(...)`);
* an operation gets the `422` response, and the document the
  `ValidationError` and `HTTPValidationError` components, when the route has
  any parameter;
* components are sorted by name.

`OpenAPI.toJson` prints it as `app.openapi()` does after
`jsonable_encoder(OpenAPI(**output), by_alias=True, exclude_none=True)`:
component schemas go through the `Schema` model, so their keys follow its
field order and its numeric keywords are floats; schemas inside operations
stay pydantic's dicts (keywords in pydantic's order, a computed title last);
`None` values are dropped everywhere, `default: null` included.
-/

namespace LeanFastapi

open LeanJson (Json)
open LeanPydantic (Schema Keyword fieldTitle)

namespace OSchema

mutual
/-- A pydantic schema inside a document: models as references. -/
def ofSchema : Schema → OSchema
  | .any => .any
  | .null => .null
  | .boolean => .boolean
  | .integer k => .integer k
  | .number k => .number k
  | .string k => .string k
  | .anyOf alts => .anyOf (ofSchemas alts)
  | .object t _ _ => .ref t
  | .annotated s t d => .ann (ofSchema s) { title := t, explicitTitle := true, default := d }

def ofSchemas : List Schema → List OSchema
  | [] => []
  | s :: ss => ofSchema s :: ofSchemas ss

def ofProps : List (String × Schema) → List (String × OSchema)
  | [] => []
  | (k, s) :: ps => (k, ofSchema s) :: ofProps ps
end

mutual
/-- The components a pydantic schema needs: every model in it, with its own
schema. -/
def models : Schema → List (String × OSchema)
  | .anyOf alts => modelsList alts
  | .object t props req => (t, .object t (ofProps props) req) :: modelsProps props
  | .annotated s _ _ => models s
  | _ => []

def modelsList : List Schema → List (String × OSchema)
  | [] => []
  | s :: ss => models s ++ modelsList ss

def modelsProps : List (String × Schema) → List (String × OSchema)
  | [] => []
  | (_, s) :: ps => models s ++ modelsProps ps
end

mutual
/-- The component names a schema refers to. -/
def refs : OSchema → List String
  | .anyOf alts => refsList alts
  | .array i => refs i
  | .object _ props _ => refsProps props
  | .ref n => [n]
  | .ann s _ => refs s
  | _ => []

def refsList : List OSchema → List String
  | [] => []
  | s :: ss => refs s ++ refsList ss

def refsProps : List (String × OSchema) → List String
  | [] => []
  | (_, s) :: ps => refs s ++ refsProps ps
end

/-! ## Printing -/

/-- Schemas inside operations are pydantic's dicts; component schemas are
dumped through FastAPI's `Schema` model. -/
inductive Mode where
  | raw
  | model
  deriving DecidableEq

/-- The position of a keyword in pydantic's output (`update_with_validations`). -/
def keywordRank : Keyword → Nat
  | .multipleOf _ => 0
  | .maximum _ => 1
  | .minimum _ => 2
  | .exclusiveMaximum _ => 3
  | .exclusiveMinimum _ => 4
  | .minLength _ => 5
  | .maxLength _ => 6
  | .pattern _ => 7

/-- The position of a key in FastAPI's `Schema` model. -/
def keyRank (k : String) : Nat :=
  match ["$ref", "anyOf", "items", "properties", "type", "multipleOf", "maximum", "exclusiveMaximum",
      "minimum", "exclusiveMinimum", "maxLength", "minLength", "pattern", "required", "title",
      "description", "default", "deprecated"].idxOf? k with
  | some i => i
  | none => 100

/-- Insertion sort, stable. -/
def sortBy {α : Type} (rank : α → Nat) (l : List α) : List α :=
  l.foldr (fun x acc => ins x acc) []
where
  ins (x : α) : List α → List α
    | [] => [x]
    | y :: ys => if rank y ≤ rank x then y :: ins x ys else x :: y :: ys

/-- Python `dict` semantics for a list of members: a key keeps its first
position and its last value. -/
def pyDict (kvs : List (String × Json)) : List (String × Json) :=
  kvs.foldl (fun acc (k, v) => if acc.any (·.1 == k) then acc.map (fun p => if p.1 == k then (k, v) else p)
    else acc ++ [(k, v)]) []

mutual
/-- `jsonable_encoder(..., exclude_none=True)`: members whose value is `null`
are dropped, at every depth. -/
def stripNone : Json → Json
  | .obj kvs => jobj (stripNoneFields kvs)
  | .arr xs => jarr (stripNoneList xs)
  | j => j

def stripNoneList : List Json → List Json
  | [] => []
  | x :: xs => stripNone x :: stripNoneList xs

def stripNoneFields : List (String × Json) → List (String × Json)
  | [] => []
  | (_, .null) :: kvs => stripNoneFields kvs
  | (k, v) :: kvs => (k, stripNone v) :: stripNoneFields kvs
end

/-- A keyword's member; the `Schema` model holds numeric bounds as floats. -/
def keywordMember (m : Mode) (k : Keyword) : String × Json :=
  match m, k.toPair with
  | .model, (n, .num (.int i)) =>
    if n == "maxLength" || n == "minLength" then (n, .num (.int i))
    else (n, .num (.float (LeanPydantic.Dec.ofInt i)))
  | _, p => p

def scalar (m : Mode) (ty : String) (kws : List Keyword) : List (String × Json) :=
  ("type", .str ty) :: (sortBy keywordRank kws).map (keywordMember m)

def annMembers (a : Annotations) : List (String × Json) :=
  let title := match a.title with | some t => [("title", .str t)] | none => []
  (if a.explicitTitle then title else []) ++
  (match a.description with | some d => [("description", .str d)] | none => []) ++
  (if a.deprecated then [("deprecated", .bool true)] else []) ++
  (match a.default with | some .null | none => [] | some d => [("default", stripNone d)]) ++
  (if a.explicitTitle then [] else title)

def arrange (m : Mode) (kvs : List (String × Json)) : List (String × Json) :=
  match m with
  | .raw => pyDict kvs
  | .model => sortBy (fun p => keyRank p.1) (pyDict kvs)

mutual
def members (m : Mode) : OSchema → List (String × Json)
  | .any => []
  | .null => [("type", .str "null")]
  | .boolean => [("type", .str "boolean")]
  | .integer k => scalar m "integer" k
  | .number k => scalar m "number" k
  | .string k => scalar m "string" k
  | .anyOf alts => [("anyOf", jarr (toJsonList m alts))]
  | .array i => [("items", toJson m i), ("type", .str "array")]
  | .object t props req =>
    [("properties", jobj (toJsonProps m props)), ("type", .str "object")] ++
      (if req.isEmpty then [] else [("required", jarr (req.map .str))]) ++ [("title", .str t)]
  | .objectAny => [("type", .str "object")]
  | .ref n => [("$ref", .str ("#/components/schemas/" ++ n))]
  | .ann s a => members m s ++ annMembers a

/-- The schema as JSON. -/
def toJson (m : Mode) (s : OSchema) : Json := jobj (arrange m (members m s))

def toJsonList (m : Mode) : List OSchema → List Json
  | [] => []
  | s :: ss => toJson m s :: toJsonList m ss

def toJsonProps (m : Mode) : List (String × OSchema) → List (String × Json)
  | [] => []
  | (k, s) :: ps => (k, toJson m s) :: toJsonProps m ps
end

end OSchema

/-! ## The validation-error components -/

/-- `validation_error_definition`. -/
def validationErrorSchema : OSchema :=
  .object "ValidationError"
    [("loc", .ann (.array (.anyOf [.string [], .integer []])) { title := "Location" }),
     ("msg", .ann (.string []) { title := "Message" }),
     ("type", .ann (.string []) { title := "Error Type" }),
     ("input", .ann .any { title := "Input" }),
     ("ctx", .ann .objectAny { title := "Context" })]
    ["loc", "msg", "type"]

/-- `validation_error_response_definition`. -/
def httpValidationErrorSchema : OSchema :=
  .object "HTTPValidationError" [("detail", .ann (.array (.ref "ValidationError")) { title := "Detail" })] []

def validationDefinitions : List (String × OSchema) :=
  [("ValidationError", validationErrorSchema), ("HTTPValidationError", httpValidationErrorSchema)]

/-- The `422` response every validating operation documents. -/
def validationErrorResponseSpec : ResponseSpec :=
  { description := "Validation Error", content := some { schema := .ref "HTTPValidationError" } }

/-! ## Operations -/

/-- `METHODS_WITH_BODY`. -/
def methodsWithBody : List String := ["GET", "HEAD", "POST", "PUT", "DELETE", "PATCH"]

/-- `get_schema_from_model_field`: a field's schema, with the title FastAPI
gives a schema that is not a `$ref`. -/
def fieldSchema (s : Schema) (a : Annotations) (autoTitle : String) : OSchema :=
  match OSchema.ofSchema s with
  | .ref n => .ref n
  | o => .ann o { a with title := some (a.title.getD autoTitle), explicitTitle := a.title.isSome }

/-- A parameter's OpenAPI object. -/
def ParamInfo.toParameter (p : ParamInfo) : Parameter where
  name := p.alias
  «in» := p.source
  required := p.required
  schema := fieldSchema p.schema
    { title := p.title, description := p.description, deprecated := p.deprecated, default := p.default }
    (fieldTitle p.alias)
  description := p.description
  deprecated := p.deprecated

/-- The `(in, name)` key of a parameter. -/
def Parameter.key (p : Parameter) : Source × String := (p.in, p.name)

/-- `all_parameters`: one parameter per `(in, name)`, in first-seen
position; a required one wins over an optional one, otherwise the last one
wins. -/
def dedupParams (ps : List Parameter) : List Parameter :=
  ps.foldl (fun acc p =>
    if acc.any (fun q => q.key == p.key) then
      acc.map fun q => if q.key == p.key && (p.required || !q.required) then p else q
    else acc ++ [p]) []

namespace APIRoute

/-- The status code key of the operation's main response. -/
def statusKey (r : APIRoute) : String := toString (r.status_code.getD 200)

/-- The operation id for a method: `operation_id`, else `generate_unique_id`. -/
def operationId (r : APIRoute) (method : String) : String :=
  r.operation_id.getD (generateUniqueId r.name r.path method)

/-- Whether the route validates input, so documents a `422`. -/
def validates (r : APIRoute) : Bool := !r.params.isEmpty && r.statusKey != "422"

/-- The documented parameters. -/
def parameters (r : APIRoute) : List Parameter :=
  dedupParams ((r.params.filter fun p => p.source != .body && p.include_in_schema).map ParamInfo.toParameter)

/-- The request body, for a method that has one. -/
def requestBody (r : APIRoute) (method : String) : Option RequestBody :=
  if methodsWithBody.contains method then
    match r.params.filter (·.source == .body) with
    | b :: _ =>
      some { required := b.required
             content := { mediaType := b.media_type
                          schema := fieldSchema b.schema { title := b.title, description := b.description }
                            (fieldTitle b.alias) } }
    | [] => none
  else none

/-- The main response's schema: the response model's, or `{}`. -/
def responseSchema (r : APIRoute) (method : String) : OSchema :=
  match r.response_model with
  | some s => fieldSchema s {} (fieldTitle ("Response_" ++ r.operationId method))
  | none => .any

/-- The operation for one of the route's methods. -/
def operation (r : APIRoute) (method : String) : Operation where
  tags := r.tags
  summary := r.summary.getD (fieldTitle r.name)
  description := r.description
  operationId := r.operationId method
  parameters := r.parameters
  requestBody := r.requestBody method
  responses :=
    [(r.statusKey, { description := r.response_description
                     content := if isBodyAllowedForStatusCode (r.status_code.getD 200) then
                       some ({ schema := r.responseSchema method } : MediaContent) else none })] ++
    (if r.validates then [("422", validationErrorResponseSpec)] else [])
  deprecated := r.deprecated

/-- The pydantic schemas a route mentions. -/
def schemas (r : APIRoute) : List Schema := r.params.map (·.schema) ++ r.response_model.toList

/-- The route's operations, as `(path, method, operation)`. -/
def operations (r : APIRoute) : List (String × String × Operation) :=
  if r.include_in_schema then r.methods.map fun m => (pathFormat r.path, m.toLower, r.operation m) else []

end APIRoute

/-- Insert an operation under its `(path, method)` key: a key already present
keeps its position and takes the new operation. -/
def upsertOp (acc : List (String × String × Operation)) (e : String × String × Operation) :
    List (String × String × Operation) :=
  if acc.any (fun x => x.1 == e.1 && x.2.1 == e.2.1) then
    acc.map fun x => if x.1 == e.1 && x.2.1 == e.2.1 then e else x
  else acc ++ [e]

/-- The document's operations for a list of routes. -/
def openapiPaths (routes : List APIRoute) : List (String × String × Operation) :=
  (routes.flatMap APIRoute.operations).foldl upsertOp []

/-- The document's component definitions for a list of routes, before
sorting. -/
def openapiDefinitions (routes : List APIRoute) : List (String × OSchema) :=
  let included := routes.filter (·.include_in_schema)
  included.flatMap (fun r => r.schemas.flatMap OSchema.models) ++
    (if included.any APIRoute.validates then validationDefinitions else [])

/-- `get_openapi(title=, version=, routes=, ...)`. -/
def getOpenapi (info : Info) (routes : List APIRoute) : OpenAPI where
  info
  paths := openapiPaths routes
  components := { schemas := Sorted.ofListSorted (openapiDefinitions routes)
                  sorted := Sorted.ofListSorted_sorted _ }

/-! ## Printing the document -/

namespace OpenAPI

def mediaJson (c : MediaContent) : Json :=
  jobj [(c.mediaType, jobj [("schema", c.schema.toJson .raw)])]

def parameterJson (p : Parameter) : Json :=
  jobj <| [("name", .str p.name), ("in", .str p.in.value), ("required", .bool p.required),
    ("schema", p.schema.toJson .raw)] ++
    (match p.description with | some d => [("description", .str d)] | none => []) ++
    (if p.deprecated then [("deprecated", .bool true)] else [])

/-- An operation. Under a path item FastAPI's `OpenAPI` model accepts
(`raw = false`), keys follow the `Operation` and `RequestBody` models; a path
item with a parameter anywhere is kept as the dict FastAPI built
(`raw = true`, confirmed on fastapi 0.143.3), whose keys are in insertion
order: `deprecated` after `operationId`, `required` before `content`. -/
def operationJson (raw : Bool) (o : Operation) : Json :=
  let deprecated := if o.deprecated then [("deprecated", .bool true)] else []
  let body := match o.requestBody with
    | some b =>
      let req := if b.required then [("required", .bool true)] else []
      [("requestBody", jobj (if raw then req ++ [("content", mediaJson b.content)]
        else [("content", mediaJson b.content)] ++ req))]
    | none => []
  jobj <| (if o.tags.isEmpty then [] else [("tags", jarr (o.tags.map .str))]) ++
    [("summary", .str o.summary)] ++
    (match o.description with | some d => if d.isEmpty then [] else [("description", .str d)] | none => []) ++
    [("operationId", .str o.operationId)] ++ (if raw then deprecated else []) ++
    (if o.parameters.isEmpty then [] else [("parameters", jarr (o.parameters.map parameterJson))]) ++
    body ++
    [("responses", jobj (o.responses.map fun (k, r) => (k, jobj ([("description", .str r.description)] ++
        (match r.content with | some c => [("content", mediaJson c)] | none => [])))))] ++
    (if raw then [] else deprecated)

/-- A path item's operations, as JSON. -/
def pathItemJson (ms : List (String × Operation)) : Json :=
  let raw := ms.any fun (_, o) => !o.parameters.isEmpty
  jobj (ms.map fun (m, o) => (m, operationJson raw o))

/-- The operations grouped by path, paths in first-seen order. -/
def groupPaths (ops : List (String × String × Operation)) : List (String × List (String × Operation)) :=
  ops.foldl (fun acc (p, m, o) =>
    if acc.any (·.1 == p) then acc.map fun e => if e.1 == p then (p, e.2 ++ [(m, o)]) else e
    else acc ++ [(p, [(m, o)])]) []

def infoJson (i : Info) : Json :=
  jobj <| [("title", .str i.title)] ++
    (match i.summary with | some s => if s.isEmpty then [] else [("summary", .str s)] | none => []) ++
    (match i.description with | some d => if d.isEmpty then [] else [("description", .str d)] | none => []) ++
    [("version", .str i.version)]

/-- The document as `app.openapi()` returns it. -/
def toJson (d : OpenAPI) : Json :=
  jobj <| [("openapi", .str d.openapi), ("info", infoJson d.info),
    ("paths", jobj ((groupPaths d.paths).map fun (p, ms) => (p, pathItemJson ms)))] ++
    (if d.components.schemas.isEmpty then []
     else [("components", jobj [("schemas", jobj (d.components.schemas.map fun (k, s) => (k, s.toJson .model)))])])

/-- The `(path, method)` keys of the document's operations. -/
def keys (d : OpenAPI) : List (String × String) := d.paths.map fun e => (e.1, e.2.1)

/-- The operation ids of the document. -/
def operationIds (d : OpenAPI) : List String := d.paths.map (·.2.2.operationId)

/-- The names of the components. -/
def componentNames (d : OpenAPI) : List String := d.components.schemas.map Prod.fst

end OpenAPI

namespace Operation

/-- The component names an operation refers to. -/
def refs (o : Operation) : List String :=
  o.parameters.flatMap (·.schema.refs) ++
    (match o.requestBody with | some b => b.content.schema.refs | none => []) ++
    o.responses.flatMap fun (_, r) => match r.content with | some c => c.schema.refs | none => []

end Operation

/-- Every component name the document refers to, from its operations and
from its components. -/
def OpenAPI.refs (d : OpenAPI) : List String :=
  d.paths.flatMap (·.2.2.refs) ++ d.components.schemas.flatMap (·.2.refs)

end LeanFastapi
