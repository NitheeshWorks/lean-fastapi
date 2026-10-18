import LeanFastapi.RepoImpl.Files

/-!
# RepoImpl: reading the request body and the other inputs

`get_request_handler` in `fastapi/routing.py` reads the body only when the
path operation has a body parameter, and then:

* an empty body is no body (`missing` for a required body);
* a body whose `content-type` is `application/json` or
  `application/*+json` is `json.loads`ed; a `JSONDecodeError` is a 422 with
  the single error `json_invalid` at `["body", pos]`, input `{}`, message
  `JSON decode error`, `ctx.error` the decoder's message; any other failure
  (`UnicodeDecodeError`, an integer too long for `int()`, a nesting too deep)
  is `400 There was an error parsing the body`;
* any other body, including one without a `content-type`
  (`strict_content_type=True`), is passed on as bytes.

The content type is parsed as `email.message.Message.get_content_type`
does: the part before `;`, stripped and lower-cased, and `text/plain` unless
it has exactly one `/`.
-/

namespace LeanFastapi

open LeanJson (Json)
open LeanStarlette (Request)

/-- `email.message.Message.get_content_type()` for a header value:
`(maintype, subtype)`. -/
def contentType (value : String) : String × String :=
  let ct := (pyStrip ((value.splitOn ";").headD "")).toList.map Char.toLower
  match (String.ofList ct).splitOn "/" with
  | [m, s] => (m, s)
  | _ => ("text", "plain")

/-- Whether FastAPI reads a body with this `content-type` as JSON. -/
def isJsonContentType : Option String → Bool
  | none => false
  | some v =>
    let (m, s) := contentType v
    m == "application" && (s == "json" || s.endsWith "+json")

/-- Why a body could not be read. -/
inductive BodyError where
  /-- `json.JSONDecodeError`: a 422 with this one error. -/
  | invalid (e : RequestError)
  /-- Any other failure: `400 There was an error parsing the body`. -/
  | unparsable
  /-- The form parser's own `400` (`MultiPartException`), with its message. -/
  | badForm (detail : String)
  deriving Inhabited

/-- The JSON nesting `json.loads` accepts in CPython 3.13 (9998 nested
arrays parse, 9999 raise `RecursionError`). -/
def maxJsonDepth : Nat := 9998

/-- The bytes without a UTF-8 byte-order mark. -/
def dropBom (b : ByteArray) : ByteArray :=
  if b.size ≥ 3 && b[0]! = 0xEF && b[1]! = 0xBB && b[2]! = 0xBF then b.extract 3 b.size else b

/-- The `json_invalid` error for a decode failure. -/
def jsonInvalid (msg : String) (pos : Nat) : RequestError :=
  { type := "json_invalid", loc := [.key "body", .index pos], msg := "JSON decode error"
    input := jobj [], ctx := [("error", .str msg)] }

/-- Whether the bytes hold a run of more than 4300 ASCII digits: the one
kind of text lean-json parses and `json.loads` rejects (`int()`'s digit
limit). One linear pass. -/
def hasLongDigitRun (b : ByteArray) : Bool :=
  (b.foldl (fun (acc : Bool × Nat) x =>
    if acc.1 then acc
    else if 48 ≤ x && x ≤ 57 then (acc.2 + 1 > 4300, acc.2 + 1) else (false, 0)) (false, 0)).1

/-- Read a request body as FastAPI does for a path operation with a body
parameter. lean-json parses first; `json.loads`'s verdict
(`PyJson.checkBytes`) is computed only where the two can differ: when
lean-json rejects (for Python's message and position) or when a digit run
exceeds Python's limit. Elsewhere they accept the same texts (tested,
`tests/Props.lean`). -/
def readBody (req : Request) : Except BodyError BodyInput :=
  if req.bodyBytes.size = 0 then .ok .none
  else if isJsonContentType (req.headers.get? "content-type") then
    -- `json.loads`'s verdict, with what to answer when it accepts.
    let python (accepted : Except BodyError BodyInput) : Except BodyError BodyInput :=
      match PyJson.checkBytes req.bodyBytes with
      | some (.decode msg pos) => .error (.invalid (jsonInvalid msg pos))
      | some .other => .error .unparsable
      | none => accepted
    match LeanJson.parseWith { maxIntLen := none, maxDepth := some maxJsonDepth } (dropBom req.bodyBytes) with
    | .ok j => if hasLongDigitRun req.bodyBytes then python (.ok (.json j.val)) else .ok (.json j.val)
    | .error _ => python (.error .unparsable)
  else .ok (.bytes (String.fromUTF8? req.bodyBytes |>.getD (String.ofList (req.bodyBytes.toList.map fun b => Char.ofNat b.toNat))))

/-- `max_files`, `max_fields` and `max_part_size` of `Request.form()`. -/
def formLimits : LeanMultipart.FormLimits := { maxFiles := 1000, maxFields := 1000, maxPartSize := 1024 * 1024 }

/-- **`await request.form()`** for a path operation with form (or file)
parameters: lean-starlette's form parser (`multipart/form-data` with
Starlette's `MultiPartParser`, `application/x-www-form-urlencoded` with its
`FormParser`, any other content type an empty form), with Starlette's
default limits; a body over a limit, or malformed multipart, is Starlette's
`400` with its message. -/
def readForm (req : Request) : Except BodyError BodyInput :=
  match LeanStarlette.formItems formLimits (req.headers.get? "content-type") req.bodyBytes with
  | .ok items => .ok (.formItems items)
  | .error e => .error (.badForm (LeanStarlette.formErrorMessage e))

/-- Open a parsed form's uploads as `UploadFile`s (Starlette's `FormData`,
what the path operation's parameters read). -/
def BodyInput.load : BodyInput → IO BodyInput
  | .formItems items => do
    let fields ← items.mapM fun (k, v) => do
      match v with
      | .text s => pure (k, FormInput.text s)
      | .file d => do
        let u ← LeanStarlette.UploadFile.new d.data d.filename d.headers (some d.data.size)
        pure (k, FormInput.file d u)
    pure (.form fields)
  | b => pure b

/-- The inputs of a request, with an already read body. -/
def Inputs.ofRequest (req : Request) (body : BodyInput) : Inputs where
  path := req.path_params.items.map fun (k, p) => (k, p.text)
  query := req.queryParams
  headers := req.headers
  cookies := cookieParser ((req.headers.get? "cookie").getD "")
  body

end LeanFastapi
