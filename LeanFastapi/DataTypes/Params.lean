import LeanPydantic
import LeanStarlette

/-!
# DataTypes: parameters, their inputs, and request errors

* `Source` is where a path operation reads a parameter: FastAPI's
  `ParamTypes` (`path`, `query`, `header`, `cookie`) and the body.
* `RequestError` is one entry of a 422 response's `detail` list: the dict
  FastAPI collects from pydantic's `errors(include_url=False)` (with the
  location prefixed by the source and the parameter's alias), or one it
  builds itself (`missing`, `json_invalid`).
* `ParamInfo` is what the OpenAPI generator needs to know about a
  parameter, and `Inputs` is what extraction reads from a request.
-/

namespace LeanFastapi

open LeanJson (Json)

/-- A JSON object from its members, in order. (Every object this library
builds goes through `jobj` and every array through `jarr`, so lean-json's
container representation is a detail of these two definitions.) -/
def jobj (kvs : List (String × Json)) : Json := .obj kvs

/-- A JSON array from its elements. -/
def jarr (xs : List Json) : Json := .arr xs

/-- The members of a JSON object. -/
def jfields? : Json → Option (List (String × Json))
  | .obj kvs => some kvs
  | _ => none

/-- Where a parameter comes from. -/
inductive Source where
  | path
  | query
  | header
  | cookie
  | body
  deriving DecidableEq, Repr, Inhabited

namespace Source

/-- The name FastAPI uses in locations and in OpenAPI's `in`. -/
def value : Source → String
  | .path => "path"
  | .query => "query"
  | .header => "header"
  | .cookie => "cookie"
  | .body => "body"

/-- The order `solve_dependencies` validates the sources in, and the order of
OpenAPI's `parameters`: path, query, header, cookie, then the body. -/
def rank : Source → Nat
  | .path => 0
  | .query => 1
  | .header => 2
  | .cookie => 3
  | .body => 4

end Source

/-- One validation error as FastAPI reports it in `{"detail": [...]}`:
`type`, `loc`, `msg`, `input` and, when there is one, `ctx`. -/
structure RequestError where
  type : String
  loc : Keel.Loc
  msg : String
  input : Json
  ctx : List (String × Json) := []
  deriving DecidableEq, Inhabited

instance : Keel.Located RequestError where
  loc e := e.loc
  within k e := { e with loc := k :: e.loc }
  loc_within _ _ := rfl

/-- What the OpenAPI generator knows about one parameter. -/
structure ParamInfo where
  source : Source
  /-- The Python parameter name. -/
  name : String
  /-- The name on the wire (`alias`, or the header name with hyphens). -/
  alias : String
  required : Bool
  /-- The parameter type's JSON Schema (pydantic's). -/
  schema : LeanPydantic.Schema
  /-- The default, dumped, when there is one. -/
  default : Option Json := none
  title : Option String := none
  description : Option String := none
  deprecated : Bool := false
  include_in_schema : Bool := true
  /-- The request media type of a body parameter (`Body(media_type=...)`). -/
  media_type : String := "application/json"
  deriving Inhabited

/-- A request body as FastAPI hands it to validation: absent (an empty body),
a parsed JSON value, or bytes that were not read as JSON (a body without a
JSON content type), which pydantic sees as text. -/
inductive BodyInput where
  | none
  | json (j : Json)
  | bytes (text : String)
  deriving Inhabited

/-- What parameters are read from: the request's converted path parameters,
query string, headers, cookies and body. -/
structure Inputs where
  path : List (String × String) := []
  query : LeanStarlette.QueryParams := ⟨[]⟩
  headers : LeanStarlette.Headers := ⟨[], by simp⟩
  cookies : List (String × String) := []
  body : BodyInput := .none

end LeanFastapi
