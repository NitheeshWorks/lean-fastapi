import LeanFastapi.RepoImpl.Params

/-!
# RepoImpl: uploaded files as parameters

`UploadFile` and `bytes` parameters (`File()`, or an `UploadFile`
annotation, which FastAPI reads from the form without one):

* an `UploadFile` parameter gets the upload itself (Starlette's
  `UploadFile`, opened when the form is read); a text value is pydantic's
  `value_error` "Expected UploadFile, received: <class 'str'>";
* a `bytes` parameter gets the upload's content (`await value.read()` in
  `_extract_form_body`), or a text value's UTF-8 bytes (pydantic's `bytes`
  from `str`);
* `list[...]` of either reads every value under the name (`getlist`), each
  validated with its index in the location; `... | None` is optional.
-/

namespace LeanFastapi

open LeanJson (Json)

/-- `fastapi.UploadFile`: Starlette's, with `filename`, `content_type`,
`size`, `read`, `seek`, `write` and `close`. -/
abbrev UploadFile := LeanStarlette.UploadFile

/-- Python's `bytes`. -/
abbrev Bytes := ByteArray

namespace RawValue

/-- The Python class of a raw value, as pydantic names it in messages. -/
def pyClass : RawValue → String
  | .json (.str _) => "str"
  | .json (.num (.int _)) => "int"
  | .json (.num _) => "float"
  | .json (.bool _) => "bool"
  | .json .null => "NoneType"
  | .json (.arr _) => "list"
  | .json (.obj _) => "dict"
  | .file .. => "starlette.datastructures.UploadFile"
  | .seq _ => "list"

end RawValue

/-- `UploadFile._validate`'s error for anything but an upload. -/
def expectedUploadFile (v : RawValue) : RequestError :=
  { type := "value_error", loc := [], msg := s!"Value error, Expected UploadFile, received: <class '{v.pyClass}'>",
    input := v.toJson, ctx := [("error", jobj [])] }

/-- pydantic's `bytes_type`. -/
def bytesType (v : RawValue) : RequestError :=
  { type := "bytes_type", loc := [], msg := "Input should be a valid bytes", input := v.toJson }

instance : ParamValue UploadFile where
  read
    | .file _ u => .ok u
    | v => .error [expectedUploadFile v]

instance : ParamValue Bytes where
  read
    | .file d _ => .ok d.data
    | .json (.str s) => .ok s.toUTF8
    | v => .error [bytesType v]

/-- A list of uploads or of contents: every value, each under its index. -/
def readEach {α : Type} [ParamValue α] : RawValue → Except (List RequestError) (List α)
  | .seq vs => Keel.Validator.each (fun v => ParamValue.read v) vs
  | v => Keel.Validator.each (fun v => ParamValue.read v) [v]

instance : ParamValue (List UploadFile) := ⟨readEach⟩
instance : ParamValue (List Bytes) := ⟨readEach⟩
instance : ParamValue (Option UploadFile) := ⟨fun v => some <$> ParamValue.read v⟩
instance : ParamValue (Option Bytes) := ⟨fun v => some <$> ParamValue.read v⟩

/-! Serialisation and schema, for defaults and OpenAPI (a file's schema is
written by the OpenAPI generator: a binary string). -/

instance : LeanPydantic.ToJson UploadFile := ⟨fun _ f => jobj [("filename", match f.filename with
  | some n => .str n | none => .null)]⟩
instance : LeanPydantic.ToJson Bytes := ⟨fun _ b => .str (String.fromUTF8? b |>.getD "")⟩
instance : LeanPydantic.JsonSchema UploadFile := ⟨.string []⟩
instance : LeanPydantic.JsonSchema Bytes := ⟨.string []⟩

/-- **A `bytes` parameter from an upload is its content.** -/
theorem bytes_of_upload (d : LeanStarlette.UploadData) (u : UploadFile) :
    ParamValue.read (α := Bytes) (.file d u) = .ok d.data := rfl

/-- **An `UploadFile` parameter is the upload itself.** -/
theorem uploadFile_of_upload (d : LeanStarlette.UploadData) (u : UploadFile) :
    ParamValue.read (α := UploadFile) (.file d u) = .ok u := rfl

end LeanFastapi
