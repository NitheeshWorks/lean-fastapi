import LeanFastapi
import tests.apps.FirstSteps001
import tests.apps.PathParams002
import tests.apps.PathParams004
import tests.apps.QueryParams001
import tests.apps.QueryParams003
import tests.apps.QueryParams005
import tests.apps.Body001
import tests.apps.Body004
import tests.apps.HandlingErrors001
import tests.apps.HandlingErrors002
import tests.apps.Qpsv003
import tests.apps.Ppnv001
import tests.apps.Ppnv006
import tests.apps.HeaderParams001
import tests.apps.HeaderParams002
import tests.apps.CookieParams001
import tests.apps.ResponseModel
import demo.App

/-!
# Conformance cases

Each case re-expresses one upstream test (https://github.com/fastapi/fastapi,
`tests/`) in Lean and names it, so `docs/traceability.toml` can point at
both. The upstream suite is the behavioural specification; no upstream code
is copied.

Three groups:

* **golden exchanges**: `tests/golden/generate.py` sent each request to the
  real fastapi 0.143.3 app (the upstream tutorial module itself, or the
  Python twin of a fixture) through `TestClient` and recorded the response;
  here the same request, with the same headers, goes to the Lean twin
  (`tests/apps/`, `demo/App.lean`), and the status, the header list and the
  body must be equal byte for byte;
* **golden documents**: `app.openapi()` of each fixture against the Lean
  app's document, as structurally equal JSON (numbers by value, objects as
  maps) and as equal bytes (compact `/openapi.json`);
* **golden `json.loads` errors**: CPython's `JSONDecodeError` position and
  message on a corpus of near-JSON texts, against `PyJson.checkText`.

Known deviations are listed in `knownDeviations` with their reason; such a
case passes only if everything except the deviation matches.

Run with `lake exe conformance`.
-/

open LeanFastapi

structure Case where
  /-- Upstream test this mirrors, e.g. `tests/test_path.py::test_int`. -/
  upstream : String
  name : String
  run : IO Bool

/-! ## Fixtures -/

def fixtures : List (String × FastAPI) :=
  [("first_steps_001", Tests.FirstSteps001.app.complete),
   ("path_params_002", Tests.PathParams002.app.complete),
   ("path_params_004", Tests.PathParams004.app.complete),
   ("query_params_001", Tests.QueryParams001.app.complete),
   ("query_params_003", Tests.QueryParams003.app.complete),
   ("query_params_005", Tests.QueryParams005.app.complete),
   ("body_001", Tests.Body001.app.complete),
   ("body_004", Tests.Body004.app.complete),
   ("handling_errors_001", Tests.HandlingErrors001.app.complete),
   ("handling_errors_002", Tests.HandlingErrors002.app.complete),
   ("qpsv_003", Tests.Qpsv003.app.complete),
   ("ppnv_001", Tests.Ppnv001.app.complete),
   ("ppnv_006", Tests.Ppnv006.app.complete),
   ("header_params_001", Tests.HeaderParams001.app.complete),
   ("header_params_002", Tests.HeaderParams002.app.complete),
   ("cookie_params_001", Tests.CookieParams001.app.complete),
   ("demo", Demo.app.complete),
   ("response_model", Tests.ResponseModel.app.complete)]

/-- Cases where the port differs from upstream on purpose, by fixture,
method and URL, with the header that differs and why. -/
def knownDeviations : List (String × String × String × String × String) :=
  [("first_steps_001", "POST", "/", "allow",
    "lean-starlette adds HEAD to every GET route (h_head), so the 405 Allow lists HEAD; requested on yjguppahlgt4")]

/-! ## JSON helpers -/

def field? (j : Json) (k : String) : Option Json := (jfields? j).bind (LeanJson.Json.lookupLast k)
def str? (j : Json) (k : String) : Option String := (field? j k).bind LeanJson.Json.getStr?
def arr? (j : Json) (k : String) : List Json := ((field? j k).bind LeanJson.Json.getArr?).getD []
def pairs (j : Json) (k : String) : List (String × String) :=
  (arr? j k).filterMap fun p => match LeanJson.Json.getArr? p with
    | some [a, b] => (do pure (← a.getStr?, ← b.getStr?))
    | _ => none

/-- A number's value as an exact rational key: `0` and `0.0` are equal, as
in Python. -/
def numKey (n : LeanJson.Number) : String :=
  match n with
  | .int i => toString (LeanPydantic.Dec.ofInt i |>.mant) ++ "e" ++ toString (LeanPydantic.Dec.ofInt i |>.exp) ++
      (if i < 0 then "-" else "")
  | .float d => toString d.mant ++ "e" ++ toString d.exp ++ (if d.neg && d.mant ≠ 0 then "-" else "")
  | n => reprStr n

mutual
/-- Structural equality: objects as maps (last value wins), numbers by
value. (Test code; `partial` keeps it short.) -/
partial def jsonEq : Json → Json → Bool
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .num a, .num b => numKey a == numKey b
  | .str a, .str b => a == b
  | .arr a, .arr b => listEq a b
  | .obj a, .obj b => fieldsEq a b b && fieldsEq b a a
  | _, _ => false

partial def listEq : List Json → List Json → Bool
  | [], [] => true
  | a :: as, b :: bs => jsonEq a b && listEq as bs
  | _, _ => false

/-- Every key of the first object has an equal value in `other`. -/
partial def fieldsEq : List (String × Json) → List (String × Json) → List (String × Json) → Bool
  | [], _, _ => true
  | (k, v) :: rest, other, all =>
    (match lookupLastIn k other with
      | some w => jsonEq v w
      | none => false) && fieldsEq rest other all

partial def lookupLastIn (k : String) : List (String × Json) → Option Json
  | [] => none
  | (k', v) :: rest => match lookupLastIn k rest with
    | some w => some w
    | none => if k' = k then some v else none
end

/-! ## Golden exchanges -/

def requestOf (e : Json) : LeanStarlette.Request :=
  let (path, query_string) := LeanStarlette.splitTarget ((str? e "url").getD "/")
  { method := (str? e "method").getD "GET", path, query_string
    headers := LeanStarlette.Headers.ofList (pairs e "request_headers")
    bodyBytes := ((str? e "body").getD "").toUTF8
    server := some ("testserver", 80) }

def goldenCases (doc : Json) : List Case :=
  (arr? doc "exchanges").map fun e =>
    let fx := (str? e "fixture").getD ""
    let method := (str? e "method").getD ""
    let url := (str? e "url").getD ""
    ⟨(str? e "upstream").getD "", s!"golden {fx} {method} {url} (tests/golden/fastapi.json)", do
      let some app := fixtures.lookup fx | throw (IO.userError s!"no Lean fixture {fx}")
      let r ← app.call (requestOf e)
      let wantStatus := (field? e "status").bind (fun | .num (.int i) => some i.toNat | _ => none)
      let wantHeaders := pairs e "headers"
      let wantBody := (str? e "response").getD ""
      let dev := knownDeviations.find? fun d => d.1 == fx && d.2.1 == method && d.2.2.1 == url
      let drop (h : List (String × String)) := match dev with
        | some (_, _, _, name, _) => h.filter (fun (p : String × String) => p.1 != name)
        | none => h
      let ok := some r.status_code == wantStatus && drop r.headers.raw == drop wantHeaders && r.text == wantBody
      unless ok do
        IO.println s!"      want {wantStatus} {wantHeaders} {wantBody.take 300}"
        IO.println s!"      got  {r.status_code} {r.headers.raw} {r.text.take 300}"
      if let some (_, _, _, h, why) := dev then
        IO.println s!"      known deviation in `{h}`: {why}"
      pure ok⟩

def openapiCases (doc : Json) : List Case :=
  (arr? doc "openapi").map fun e =>
    let fx := (str? e "fixture").getD ""
    ⟨"tests/test_tutorial/*::test_openapi_schema", s!"openapi {fx} (tests/golden/fastapi.json)", do
      let some app := fixtures.lookup fx | throw (IO.userError s!"no Lean fixture {fx}")
      let want := (field? e "openapi").getD .null
      let got := app.openapiJson
      let ok := jsonEq got want
      let sameBytes := LeanJson.printStr got == LeanJson.printStr want
      if ok && !sameBytes then
        IO.println s!"      {fx}: structurally equal; the bytes differ (key order or number spelling)"
      let ok := ok && sameBytes
      unless ok do
        IO.println s!"      want {LeanJson.printStr want}"
        IO.println s!"      got  {LeanJson.printStr got}"
      pure ok⟩

/-! ## Golden `json.loads` errors -/

def pyjsonCase (corpus : List Json) : Case :=
  ⟨"tests/test_tutorial/test_body/test_tutorial001.py::test_post_broken_body",
   s!"json.loads errors on {corpus.length} texts (tests/golden/pyjson.json)", do
    let mut bad := 0
    for e in corpus do
      let text := (str? e "text").getD ""
      let want : Option PyJson.Failure :=
        if field? e "ok" == some (.bool true) then none
        else match str? e "msg", field? e "pos" with
          | some m, some (.num (.int p)) => some (.decode m p.toNat)
          | _, _ => some .other
      let got := PyJson.checkText text.toList.toArray
      if got != want then
        bad := bad + 1
        if bad ≤ 5 then IO.println s!"      {repr text}: want {repr want}, got {repr got}"
    pure (bad == 0)⟩

/-! ## Unit cases -/

def unitCases : List Case :=
  [⟨"tests/test_tutorial/test_header_params/test_tutorial002.py::test", "header alias user_agent is user-agent",
     pure (headerParamAlias "user_agent" none true == "user-agent")⟩,
   ⟨"tests/test_tutorial/test_path_params/test_tutorial004.py::test_file_path", "path format drops convertors",
     pure (pathFormat "/files/{file_path:path}" == "/files/{file_path}")⟩,
   ⟨"tests/test_generate_unique_id_function.py::test_top_level_generate_unique_id", "generate_unique_id",
     pure (generateUniqueId "read_item" "/items/{item_id}" "GET" == "read_item_items__item_id__get")⟩,
   ⟨"tests/test_tutorial/test_first_steps/test_tutorial001_tutorial002_tutorial003.py::test_get_path",
     "snake case of a Lean name", pure (snakeCase "readUserItem" == "read_user_item" && snakeCase "root" == "root")⟩]

def main : IO UInt32 := do
  let golden ← IO.FS.readFile "tests/golden/fastapi.json"
  let .ok doc := LeanJson.parseStr golden | throw (IO.userError "tests/golden/fastapi.json does not parse")
  let pyj ← IO.FS.readFile "tests/golden/pyjson.json"
  let .ok corpus := LeanJson.parseStr pyj | throw (IO.userError "tests/golden/pyjson.json does not parse")
  let cases := unitCases ++ goldenCases doc.val ++ openapiCases doc.val ++
    [pyjsonCase ((LeanJson.Json.getArr? corpus.val).getD [])]
  let mut failures := 0
  for c in cases do
    let ok ← try c.run catch e => do IO.println s!"      {e}"; pure false
    IO.println s!"{if ok then "ok  " else "FAIL"}  {c.name}  [{c.upstream}]"
    unless ok do failures := failures + 1
  IO.println s!"{cases.length} cases, {failures} failing"
  return if failures == 0 then 0 else 1
