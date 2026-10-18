import LeanFastapi

/-!
# Property tests: fast feedback where there is no proof

Generates values with a seeded generator and checks the properties that are
tested rather than proved. Not a substitute for the theorems; the check that
runs in under a second so a mistake surfaces while the change is still in
your head.

Run with `lake exe props`, or a different seed with `lake exe props 12345`.
A failure prints the seed and the value, so it reproduces exactly.
-/

/-- xorshift64*: four lines, no dependency, deterministic from the seed. -/
structure Rng where
  s : UInt64
  deriving Inhabited

def Rng.next (r : Rng) : UInt64 × Rng :=
  let x := r.s
  let x := x ^^^ (x >>> 12)
  let x := x ^^^ (x <<< 25)
  let x := x ^^^ (x >>> 27)
  (x * 2685821657736338717, { s := x })

def Rng.nat (r : Rng) (bound : Nat) : Nat × Rng :=
  let (v, r) := r.next
  (if bound == 0 then 0 else v.toNat % bound, r)

/-- A property: a name and a check that, given a generator, either passes or
returns a description of the failing value. -/
structure Property where
  name : String
  check : Rng → Option String × Rng

def Rng.pick (r : Rng) (xs : List α) [Inhabited α] : α × Rng :=
  let (i, r) := r.nat xs.length
  (xs[i]!, r)

open LeanFastapi

/-! ## Generators -/

/-- A random JSON text from the grammar Python's `json` accepts: no `\u`
escapes, small exponents, nesting at most `d`. -/
def genJson (r : Rng) : Nat → String × Rng
  | 0 => genScalar r
  | d + 1 =>
    let (k, r) := r.nat 6
    match k with
    | 0 =>
      let (n, r) := r.nat 4
      let (items, r) := (List.range n).foldl (fun (acc, r) _ => let (j, r) := genJson r d; (acc ++ [j], r)) ([], r)
      ("[" ++ ", ".intercalate items ++ "]", r)
    | 1 =>
      let (n, r) := r.nat 4
      let (items, r) := (List.range n).foldl (fun (acc, r) _ =>
        let (key, r) := genStr r
        let (j, r) := genJson r d
        (acc ++ [key ++ ":" ++ j], r)) ([], r)
      ("{" ++ ",".intercalate items ++ "}", r)
    | _ => genScalar r
where
  genStr (r : Rng) : String × Rng :=
    let (n, r) := r.nat 5
    let (cs, r) := (List.range n).foldl (fun (acc, r) _ =>
      let (c, r) := r.pick ["a", "Z", " ", "\\n", "\\\"", "\\\\", "\\/", "é", "€"]; (acc ++ c, r)) ("", r)
    ("\"" ++ cs ++ "\"", r)
  genScalar (r : Rng) : String × Rng :=
    let (k, r) := r.nat 8
    match k with
    | 0 => ("null", r) | 1 => ("true", r) | 2 => ("false", r)
    | 3 => genStr r
    | 4 => r.pick ["NaN", "Infinity", "-Infinity"]
    | _ =>
      let (i, r) := r.nat 100000
      let (neg, r) := r.nat 2
      let (frac, r) := r.nat 3
      let (ex, r) := r.nat 3
      let s := (if neg = 0 then "-" else "") ++ toString i
      let s := s ++ (match frac with | 0 => s!".{i % 97}" | _ => "")
      let s := s ++ (match ex with | 0 => s!"e{i % 9}" | 1 => s!"E-{i % 7}" | _ => "")
      (s, r)

/-- One random edit of a text: delete, duplicate or replace a character. -/
def mutate (r : Rng) (s : String) : String × Rng :=
  let cs := s.toList
  let (i, r) := r.nat (cs.length + 1)
  let (k, r) := r.nat 3
  let (c, r) := r.pick ['[', ']', '{', '}', ',', ':', '"', '\\', '.', 'e', '-', '0', '1', ' ', 'n', 'x', '\x01']
  let out := match k with
    | 0 => cs.take i ++ cs.drop (i + 1)
    | 1 => cs.take i ++ [c] ++ cs.drop i
    | _ => cs.take i ++ [c] ++ cs.drop (i + 1)
  (String.ofList out, r)

def genIdent (r : Rng) (alphabet : List Char) : String × Rng :=
  let (n, r) := r.nat 8
  let (cs, r) := (List.range n).foldl (fun (acc, r) _ => let (c, r) := r.pick alphabet; (acc ++ [c], r)) ([], r)
  (String.ofList cs, r)

def check (ok : Bool) (why : String) : Option String := if ok then none else some why

/-- `readBody`'s answer in brief: accepted, a 422 at a position with a
message, or a 400. -/
def bodyVerdict : Except BodyError BodyInput → String
  | .ok _ => "ok"
  | .error (.invalid e) => s!"422 {e.ctx} {e.toJson.compress}"
  | .error .unparsable => "400"

/-- The reference order: `json.loads`'s verdict first, then lean-json. -/
def pythonFirst (b : ByteArray) : String :=
  match PyJson.checkBytes b with
  | some (.decode msg pos) => bodyVerdict (.error (.invalid (jsonInvalid msg pos)))
  | some .other => "400"
  | none => match LeanJson.parseWith { maxIntLen := none, maxDepth := some maxJsonDepth } (dropBom b) with
    | .ok _ => "ok"
    | .error _ => "400"

def jsonRequest (t : String) : LeanStarlette.Request :=
  { method := "POST", path := "/", query_string := ""
    headers := LeanStarlette.Headers.ofList [("content-type", "application/json")], bodyBytes := t.toUTF8 }

/-! ## Properties -/

def properties : List Property := [
  { name := "PyJson accepts every generated JSON text"
    check := fun r =>
      let (t, r) := genJson r 4
      (check (PyJson.checkText t.toList.toArray).isNone s!"rejected {t.quote}", r) },
  { name := "PyJson accepts exactly what lean-json parses, on edited texts"
    check := fun r =>
      let (t, r) := genJson r 3
      let (t, r) := mutate r t
      let py := (PyJson.checkText t.toList.toArray).isNone
      let lj := (LeanJson.parseStr t).toOption.isSome
      (check (py == lj) s!"{t.quote}: json.loads {py}, lean-json {lj}", r) },
  { name := "readBody (lean-json first) answers as json.loads first would, on edited texts"
    check := fun r =>
      let (t, r) := genJson r 3
      let (t, r) := mutate r t
      let (k, r) := r.nat 4
      -- sometimes a digit run past Python's 4300-digit limit, in or out of a string
      let t := match k with
        | 0 => "[" ++ String.ofList (List.replicate 4301 '7') ++ "," ++ t ++ "]"
        | 1 => "[\"" ++ String.ofList (List.replicate 4301 '7') ++ "\"," ++ t ++ "]"
        | _ => t
      let got := bodyVerdict (readBody (jsonRequest t))
      let want := pythonFirst t.toUTF8
      (check (got == want) s!"{(String.ofList (t.toList.take 80)).quote}: {got} vs {want}", r) },
  { name := "PyJson error positions are within the text"
    check := fun r =>
      let (t, r) := genJson r 3
      let (t, r) := mutate r t
      let ok := match PyJson.checkText t.toList.toArray with
        | some (.decode _ pos) => pos ≤ t.length
        | _ => true
      (check ok s!"{t.quote}", r) },
  { name := "cookieParser: names are unique and the last value wins"
    check := fun r =>
      let (n, r) := r.nat 5
      let (pairs, r) := (List.range n).foldl (fun (acc, r) _ =>
        let (k, r) := genIdent r ['a', 'b', 'c']
        let (v, r) := genIdent r ['x', 'y', '1']
        (acc ++ [(if k.isEmpty then "k" else k, v)], r)) ([], r)
      let header := "; ".intercalate (pairs.map fun (k, v) => k ++ "=" ++ v)
      let got := cookieParser header
      let keys := got.map (·.1)
      let ok := keys.eraseDups.length == keys.length &&
        pairs.all fun (k, _) => got.lookup k == (pairs.reverse.lookup k)
      (check ok s!"{header.quote} -> {got}", r) },
  { name := "cookieUnquote is the identity on unquoted values"
    check := fun r =>
      let (v, r) := genIdent r ['a', '\\', '1', ' ']
      (check (cookieUnquote v == v) s!"{v.quote}", r) },
  { name := "pathFormat is idempotent and keeps the parameter names"
    check := fun r =>
      let (segs, r) := (List.range 3).foldl (fun (acc, r) _ =>
        let (name, r) := genIdent r ['a', 'b', '_']
        let (conv, r) := r.pick ["", ":int", ":path", ":str"]
        let (lit, r) := genIdent r ['x', '-', '.']
        (acc ++ [lit, "{" ++ name ++ conv ++ "}"], r)) ([], r)
      let p := "/" ++ "/".intercalate segs
      let f := pathFormat p
      let ok := pathFormat f == f &&
        pathParamNames f == (pathParamNames p).map (fun n => (n.splitOn ":").headD n)
      (check ok s!"{p} -> {f}", r) },
  { name := "snakeCase is idempotent and fixes lower-case names"
    check := fun r =>
      let (n, r) := genIdent r ['a', 'B', '1', '_', 'Z']
      let (m, r) := genIdent r ['a', 'b', '_', '2']
      (check (snakeCase (snakeCase n) == snakeCase n && snakeCase m == m) s!"{n} {m}", r) },
  { name := "generateUniqueId yields word characters only"
    check := fun r =>
      let (n, r) := genIdent r ['a', '-', '.', '_', 'é']
      let (p, r) := genIdent r ['/', '{', '}', 'x', ':']
      let (m, r) := r.pick ["GET", "POST", "delete"]
      let id := generateUniqueId n p m
      (check (id.toList.all isWordChar) id, r) },
  { name := "headerAlias writes no underscore and changes nothing else"
    check := fun r =>
      let (n, r) := genIdent r ['a', '_', '-', 'B']
      let h := headerAlias n
      (check (!h.contains '_' && h.length == n.length && h.replace "-" "_" == n.replace "-" "_") h, r) },
  { name := "isJsonContentType: application/json and +json, any case and parameters"
    check := fun r =>
      let (base, r) := r.pick ["application/json", "Application/JSON", "application/vnd.api+json", "text/plain", "application/jsonx", "application/x-www-form-urlencoded"]
      let (params, r) := r.pick ["", "; charset=utf-8", " ;q=1"]
      let want := ["application/json", "application/vnd.api+json"].contains (base.toLower)
      (check (isJsonContentType (some (base ++ params)) == want) s!"{base}{params}", r) }
]

def main (args : List String) : IO UInt32 := do
  let seed := (args.head? >>= String.toNat?).getD 88172645463325252
  let cases := 200
  let mut rng : Rng := { s := UInt64.ofNat seed }
  let mut failures := 0
  for p in properties do
    let mut failed : Option String := none
    for _ in [0:cases] do
      if failed.isSome then break
      let (res, rng') := p.check rng
      rng := rng'
      failed := res
    match failed with
    | none => IO.println s!"ok    {p.name} ({cases} cases)"
    | some why =>
      failures := failures + 1
      IO.println s!"FAIL  {p.name}: {why}  (seed {seed})"
  IO.println s!"{properties.length} properties, {failures} failing (seed {seed})"
  return if failures == 0 then 0 else 1
