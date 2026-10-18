import LeanFastapi.DataTypes.Params
import LeanFastapi.RepoImpl.PyJson

/-!
# RepoImpl: reading and validating parameters

`fastapi/dependencies/utils.py`, `request_params_to_args` and
`request_body_to_args`, for parameters declared one by one:

* a parameter's raw value is `values.get(alias)` of its source (the last
  query value, the first header, the cookie, the body or one of its
  members); an absent value, or a JSON `null` body, takes the default or is
  `missing` (input `null`);
* a present value is validated by the parameter type's pydantic validator in
  Python (lax) mode, so `"42"` is an `int`;
* every error is located under `[source, alias]`, or under `["body"]` for a
  body that is not embedded (Keel's `Validator.atPath`).

`Params β` is a product of parameters, built with `Params.nil` and
`Params.cons`; its `extract` is Keel's `Validator.both` chain, so every
parameter is validated and all their errors are reported, in declaration
order. The endpoint macro declares parameters sorted by `Source.rank`, which
makes that order FastAPI's (path, query, header, cookie, body).
-/

namespace LeanFastapi

open LeanJson (Json)
open LeanPydantic (FromJson ToJson JsonSchema ErrorDetails)

/-- How FastAPI validates every parameter, body and response:
`validate_python(value, from_attributes=True)`, so a model given a
non-object reports `model_attributes_type`, at any depth. -/
def fastapiCfg : LeanPydantic.Cfg := { from_attributes := true }

namespace RequestError

/-- The error as FastAPI serialises it. -/
def toJson (e : RequestError) : Json :=
  jobj <| [("type", .str e.type), ("loc", ErrorDetails.locJson e.loc), ("msg", .str e.msg),
    ("input", e.input)] ++ (if e.ctx = [] then [] else [("ctx", jobj e.ctx)])

/-- A pydantic line error as FastAPI reports it (`errors(include_url=False)`). -/
def ofDetails (e : ErrorDetails) : RequestError :=
  { type := e.type, loc := e.loc, msg := e.msg, input := e.input, ctx := e.ctx }

/-- `get_missing_field_error`: a required parameter is absent. -/
def missing : RequestError := { type := "missing", loc := [], msg := "Field required", input := .null }

end RequestError

/-! ## Cookies -/

/-- Python's `str.strip()` on ASCII and Unicode whitespace. -/
def pyStrip (s : String) : String :=
  String.ofList ((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

/-- `http.cookies._unquote`: a value in double quotes loses them, and its
`\"`, `\\` and three-digit octal escapes are decoded. -/
def cookieUnquote (v : String) : String :=
  let cs := v.toList
  if cs.length < 2 || cs.head? ≠ some '"' || cs.getLast? ≠ some '"' then v
  else String.ofList (go ((cs.drop 1).take (cs.length - 2)))
where
  octal (c : Char) : Bool := '0' ≤ c && c ≤ '7'
  go : List Char → List Char
    | '\\' :: a :: b :: c :: rest =>
      if octal a && octal b && octal c then
        Char.ofNat ((a.toNat - 48) * 64 + (b.toNat - 48) * 8 + (c.toNat - 48)) :: go rest
      else a :: go (b :: c :: rest)
    | '\\' :: a :: rest => a :: go rest
    | c :: rest => c :: go rest
    | [] => []

/-- `starlette.requests.cookie_parser`: `name=value` chunks split on `;`,
stripped, a chunk without `=` having an empty name; later names win. -/
def cookieParser (header : String) : List (String × String) :=
  (header.splitOn ";").foldl (init := []) fun acc chunk =>
    let (k, v) := match chunk.splitOn "=" with
      | [] => ("", "")
      | [v] => ("", v)
      | k :: rest => (k, "=".intercalate rest)
    let (k, v) := (pyStrip k, pyStrip v)
    if k.isEmpty && v.isEmpty then acc
    else (acc.filter (·.1 != k)) ++ [(k, cookieUnquote v)]

/-! ## Reading a raw value -/

/-- An upload as the input of a validation error. FastAPI reports the
`UploadFile` object's attributes; this is their public part (filename,
size, headers): see CONTRIBUTING, deviations. -/
def uploadInputJson (d : LeanStarlette.UploadData) : Json :=
  jobj [("filename", match d.filename with | some f => .str f | none => .null),
        ("size", .num (.int d.data.size)),
        ("headers", jobj (d.headers.items.map fun (k, v) => (k, .str v)))]

/-- A form value as JSON (an upload as its `uploadInputJson`). -/
def FormInput.toJson : FormInput → Json
  | .text s => .str s
  | .file d _ => uploadInputJson d

namespace RawValue

/-- A raw value as JSON, for a validator that reads JSON. -/
def toJson : RawValue → Json
  | .json j => j
  | .file d _ => uploadInputJson d
  | .seq vs => jarr (vs.map toJson)

end RawValue

namespace Inputs

/-- `values.get(key)` for a source; the whole body for `body` is
`Inputs.wholeBody`. -/
def lookup (inp : Inputs) : Source → String → Option Json
  | .path, k => (inp.path.lookup k).map .str
  | .query, k => (inp.query.get? k).map .str
  | .header, k => (inp.headers.get? k).map .str
  | .cookie, k => (inp.cookies.lookup k).map .str
  | .body, k =>
    match inp.body with
    | .json j => (jfields? j).bind (LeanJson.Json.lookupLast k)
    | .form fs => (fs.reverse.lookup k).map FormInput.toJson
    | _ => none

/-- A form's values under `k`: the last one (`form.get(k)`), or every one
(`form.getlist(k)`, for a list parameter), as raw values. -/
def formRaw (fs : List (String × FormInput)) (k : String) (many : Bool) : Option RawValue :=
  let raw : FormInput → RawValue
    | .text s => .json (.str s)
    | .file d u => .file d u
  if many then
    match fs.filter (·.1 == k) with
    | [] => none
    | vs => some (.seq (vs.map (raw ·.2)))
  else (fs.reverse.lookup k).map raw

/-- The body as one value, `none` when there is none. A form is the object
of its keys, each with its last value. -/
def wholeBody (inp : Inputs) : Option Json :=
  match inp.body with
  | .none => none
  | .json j => some j
  | .bytes t => some (.str t)
  | .formItems _ => none
  | .form fs =>
    let keys := (fs.map (·.1)).eraseDups
    some (jobj (keys.filterMap fun k => ((fs.reverse.lookup k).map fun v => (k, v.toJson))))

end Inputs

/-! ## Parameters -/

/-- The form media types (`Form(...)`, `File(...)`). -/
def isFormMediaType (m : String) : Bool :=
  m == "application/x-www-form-urlencoded" || m == "multipart/form-data"

/-- **How a parameter's type reads its raw value**: pydantic's validator on
the JSON (every type with `FromJson`), or, for uploads, the file itself
(`UploadFile`), its bytes (`bytes`), and lists and options of those. -/
class ParamValue (α : Type) where
  read : RawValue → Except (List RequestError) α

instance (priority := low) {α : Type} [FromJson α] : ParamValue α :=
  ⟨fun v => (LeanPydantic.fromJson fastapiCfg v.toJson).mapError (List.map RequestError.ofDetails)⟩

/-- A declared parameter of type `α`: its source, Python name and wire name,
its default (`none`: required), and its OpenAPI metadata. -/
structure Param (α : Type) where
  source : Source
  name : String
  alias : String := name
  /-- A body parameter read from a member of the body (`Body(embed=True)`, or
  one of several body parameters) rather than from the whole body. -/
  embed : Bool := false
  default : Option α := none
  title : Option String := none
  description : Option String := none
  deprecated : Bool := false
  include_in_schema : Bool := true
  media_type : String := "application/json"
  /-- `json_schema_extra`. -/
  extra : List (String × Json) := []
  /-- The type is a list (`field_annotation_is_sequence`): a form gives it
  every value under its name. -/
  isSeq : Bool := false
  /-- The type is a model (FastAPI's non-scalar field). -/
  isModel : Bool := false
  /-- The type holds uploaded files. -/
  file : Option FileShape := none

namespace Param

variable {α : Type}

/-- Whether the parameter is the whole (not embedded) body. -/
def isWholeBody (p : Param α) : Bool := p.source == .body && !p.embed

/-- Where its errors are located: `[source, alias]`, or `["body"]`. -/
def loc (p : Param α) : Keel.Loc :=
  if p.isWholeBody then [.key "body"] else [.key p.source.value, .key p.alias]

/-- Whether it is a form field (`Form(...)`). -/
def isForm (p : Param α) : Bool := isFormMediaType p.media_type

/-- Its raw value in the inputs: the whole body, a form's value (every one
for a list), or the value under its alias. A JSON `null` is absent, as
Python's `None` is, and so are an empty form field and an empty list
(`_get_multidict_value`). -/
def raw (p : Param α) (inp : Inputs) : Option RawValue :=
  let v : Option RawValue :=
    if p.isWholeBody then inp.wholeBody.map .json
    else match p.source, inp.body with
      | .body, .form fs => Inputs.formRaw fs p.alias p.isSeq
      | _, _ => (inp.lookup p.source p.alias).map .json
  match v with
  | some (.json .null) => none
  | some (.json (.str "")) => if p.isForm then none else some (.json (.str ""))
  | some (.seq []) => none
  | v => v

/-- Validate the raw value, or take the default, before locating errors. -/
def read [ParamValue α] (p : Param α) : Keel.Validator RequestError Inputs α := fun inp =>
  match p.raw inp with
  | none =>
    match p.default with
    | some d => .ok d
    | none => .error [RequestError.missing]
  | some v => ParamValue.read v

/-- The parameter's validator: `read`, with every error under `loc`. -/
def validator [ParamValue α] (p : Param α) : Keel.Validator RequestError Inputs α :=
  p.read.atPath p.loc

/-- What OpenAPI needs to know about it. -/
def info [ToJson α] [JsonSchema α] (p : Param α) : ParamInfo where
  source := p.source
  name := p.name
  alias := p.alias
  required := p.default.isNone
  schema := JsonSchema.schema α
  default := p.default.map (LeanPydantic.toJson {})
  title := p.title
  description := p.description
  deprecated := p.deprecated
  include_in_schema := p.include_in_schema
  media_type := p.media_type
  embed := p.embed
  extra := p.extra
  loc := p.loc
  isModel := p.isModel
  file := p.file

/-- Every error of a parameter's validator is located under its `loc`. -/
theorem validator_loc [ParamValue α] (p : Param α) (inp : Inputs) (es : List RequestError)
    (h : p.validator inp = .error es) : ∀ e ∈ es, p.loc <+: e.loc :=
  Keel.Validator.prefix_loc_atPath p.loc p.read inp es h

end Param

/-- A product of declared parameters: their OpenAPI descriptions and their
joint validator, which locates every error under one of the parameters
(`extract_loc`, kept by `nil` and `cons`). -/
structure Params (β : Type) where
  infos : List ParamInfo
  extract : Keel.Validator RequestError Inputs β
  extract_loc : ∀ inp es, extract inp = .error es → ∀ e ∈ es, ∃ i ∈ infos, i.loc <+: e.loc

namespace Params

/-- No parameters. -/
def nil : Params Unit := ⟨[], fun _ => .ok (), fun _ _ h => by cases h⟩

/-- The parameter `p` before the parameters `rest`. -/
def cons {α β : Type} [ParamValue α] [ToJson α] [JsonSchema α] (p : Param α) (rest : Params β) :
    Params (α × β) where
  infos := p.info :: rest.infos
  extract := p.validator.both rest.extract
  extract_loc inp es h := by
    rw [Keel.Validator.both_error _ _ _ _ h]
    intro e he
    rcases List.mem_append.1 he with he | he
    · split at he
      · rename_i es' hv
        exact ⟨p.info, List.mem_cons_self, p.validator_loc inp es' hv e he⟩
      · simp at he
    · split at he
      · rename_i es' hr
        obtain ⟨i, hi, hl⟩ := rest.extract_loc inp es' hr e he
        exact ⟨i, List.mem_cons_of_mem _ hi, hl⟩
      · simp at he

end Params

end LeanFastapi
