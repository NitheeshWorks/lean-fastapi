/-!
# RepoImpl: where Python's `json.loads` rejects a request body

FastAPI reads a JSON request body with Starlette's `await request.json()`,
which is `json.loads(body)`. When that raises `json.JSONDecodeError`,
FastAPI answers 422 with one `json_invalid` error whose location is
`["body", e.pos]` and whose `ctx.error` is `e.msg`
(`fastapi/routing.py`, `get_request_handler`). Reproducing that body byte
for byte needs the position and the message CPython's C scanner
(`Modules/_json.c`) reports, so this module is a recogniser that answers
exactly that question: does the text parse, and if not, where and why.

It does not build a value; lean-json parses accepted bodies. The rules,
confirmed against CPython 3.13 (`tests/golden/pyjson.json`):

* whitespace is ` \t\n\r` only;
* a value is a string, object, array, `null`, `true`, `false`, `NaN`,
  `Infinity`, `-Infinity`, or a number `-?(0|[1-9][0-9]*)(\.[0-9]+)?([eE][-+]?[0-9]+)?`
  (the fraction and exponent are taken only when complete, so `1.` is the
  number `1` followed by `.`);
* inside a string a control character (`< 0x20`) is an error at its own
  position, an unknown escape is `Invalid \escape` at the backslash, and a
  `\u` escape needs four hex digits and at least one more character after
  them, else `Invalid \uXXXX escape` at the `u`;
* a trailing comma before `]` or `}` is reported at the comma;
* an integer literal of more than 4300 digits makes `int()` raise
  `ValueError`, not `JSONDecodeError` (`other`), which FastAPI turns into
  `400 There was an error parsing the body`.

Nesting is followed with a step budget of three steps per input character
(plus three): each character opens at most three nested calls (`value`,
`arrayFirst`/`objectFirst`, the item loop), so the budget is never the
reason for an answer on a real input. Python's own recursion limit is
not modelled (lean-json's depth limit applies to accepted bodies).
-/

namespace LeanFastapi

namespace PyJson

/-- Why `json.loads` failed. -/
inductive Failure where
  /-- `json.JSONDecodeError(msg, doc, pos)`. -/
  | decode (msg : String) (pos : Nat)
  /-- Any other exception (`ValueError` from `int()`, `UnicodeDecodeError`). -/
  | other
  deriving DecidableEq, Repr, Inhabited

abbrev Result := Except Failure Nat

def isWs (c : Char) : Bool := c = ' ' || c = '\t' || c = '\n' || c = '\r'
def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
def isHex (c : Char) : Bool := isDigit c || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def at? (s : Array Char) (i : Nat) : Option Char := s[i]?

def is (s : Array Char) (i : Nat) (p : Char → Bool) : Bool :=
  match s[i]? with
  | some c => p c
  | none => false

/-- The index after the whitespace at `i`. -/
def skipWs (s : Array Char) (i : Nat) : Nat :=
  if h : i < s.size then (if isWs s[i] then skipWs s (i + 1) else i) else i
termination_by s.size - i

/-- The index after the digits at `i`. -/
def skipDigits (s : Array Char) (i : Nat) : Nat :=
  if h : i < s.size then (if isDigit s[i] then skipDigits s (i + 1) else i) else i
termination_by s.size - i

/-- Whether the text at `i` starts with `lit`. -/
def startsWith (s : Array Char) (i : Nat) (lit : String) : Bool :=
  (s.extract i (i + lit.length)).toList == lit.toList

/-- `_match_number_unicode`: the end of the number at `start`, `none` when
there is none (`StopIteration`), or `other` for an integer literal too long
for `int()`. -/
def number (s : Array Char) (start : Nat) : Option Result :=
  let i := if at? s start = some '-' then start + 1 else start
  let intEnd? : Option Nat :=
    match at? s i with
    | some c => if '1' ≤ c && c ≤ '9' then some (skipDigits s (i + 1)) else if c = '0' then some (i + 1) else none
    | none => none
  match intEnd? with
  | none => none
  | some e =>
    let afterFrac := if at? s e = some '.' && is s (e + 1) isDigit then skipDigits s (e + 2) else e
    let afterExp :=
      if at? s afterFrac = some 'e' || at? s afterFrac = some 'E' then
        let j := afterFrac + 1
        let j := if at? s j = some '+' || at? s j = some '-' then j + 1 else j
        if is s j isDigit then skipDigits s (j + 1) else afterFrac
      else afterFrac
    let isFloat := afterExp != e
    if !isFloat && e - i > 4300 then some (.error .other) else some (.ok afterExp)

/-- `scanstring_unicode` from just after the opening quote at `begin`: the
index after the closing quote. -/
def string (s : Array Char) (begin : Nat) (i : Nat) : Result :=
  if h : i < s.size then
    let c := s[i]
    if c = '"' then .ok (i + 1)
    else if c = '\\' then
      match at? s (i + 1) with
      | none => .error (.decode "Unterminated string starting at" begin)
      | some 'u' =>
        let u := i + 1
        if u + 5 ≥ s.size || !((List.range 4).all fun k => is s (u + 1 + k) isHex) then
          .error (.decode "Invalid \\uXXXX escape" u)
        else string s begin (u + 5)
      | some e =>
        if "\"\\/bfnrt".toList.contains e then string s begin (i + 2)
        else .error (.decode "Invalid \\escape" i)
    else if c.toNat < 0x20 then .error (.decode "Invalid control character at" i)
    else string s begin (i + 1)
  else .error (.decode "Unterminated string starting at" begin)
termination_by s.size - i

def expectingValue (i : Nat) : Result := .error (.decode "Expecting value" i)

mutual
/-- `scan_once_unicode` at `i`: the end of the value there. -/
def value (s : Array Char) (i : Nat) : Nat → Result
  | 0 => .error .other
  | fuel + 1 =>
    match at? s i with
    | none => expectingValue i
    | some '"' => string s i (i + 1)
    | some '{' => objectFirst s (skipWs s (i + 1)) fuel
    | some '[' => arrayFirst s (skipWs s (i + 1)) fuel
    | some c =>
      let lit := if c = 'n' then some "null" else if c = 't' then some "true" else if c = 'f' then some "false"
        else if c = 'N' then some "NaN" else if c = 'I' then some "Infinity"
        else if c = '-' && startsWith s i "-Infinity" then some "-Infinity" else none
      match lit with
      | some l => if startsWith s i l then .ok (i + l.length) else (number s i).getD (expectingValue i)
      | none => (number s i).getD (expectingValue i)

/-- An array, just after `[` and its whitespace. -/
def arrayFirst (s : Array Char) (i : Nat) : Nat → Result
  | 0 => .error .other
  | fuel + 1 => if at? s i = some ']' then .ok (i + 1) else arrayItems s i fuel

/-- An array element at `i`, then `,` or `]`. -/
def arrayItems (s : Array Char) (i : Nat) : Nat → Result
  | 0 => .error .other
  | fuel + 1 =>
    match value s i fuel with
    | .error e => .error e
    | .ok j =>
      let j := skipWs s j
      if at? s j = some ']' then .ok (j + 1)
      else if at? s j ≠ some ',' then .error (.decode "Expecting ',' delimiter" j)
      else
        let k := skipWs s (j + 1)
        if at? s k = some ']' then .error (.decode "Illegal trailing comma before end of array" j)
        else arrayItems s k fuel

/-- An object, just after `{` and its whitespace. -/
def objectFirst (s : Array Char) (i : Nat) : Nat → Result
  | 0 => .error .other
  | fuel + 1 => if at? s i = some '}' then .ok (i + 1) else objectItems s i fuel

/-- An object member at `i` (its key), then `,` or `}`. -/
def objectItems (s : Array Char) (i : Nat) : Nat → Result
  | 0 => .error .other
  | fuel + 1 =>
    if at? s i ≠ some '"' then .error (.decode "Expecting property name enclosed in double quotes" i)
    else match string s i (i + 1) with
      | .error e => .error e
      | .ok j =>
        let j := skipWs s j
        if at? s j ≠ some ':' then .error (.decode "Expecting ':' delimiter" j)
        else match value s (skipWs s (j + 1)) fuel with
          | .error e => .error e
          | .ok k =>
            let k := skipWs s k
            if at? s k = some '}' then .ok (k + 1)
            else if at? s k ≠ some ',' then .error (.decode "Expecting ',' delimiter" k)
            else
              let m := skipWs s (k + 1)
              if at? s m = some '}' then .error (.decode "Illegal trailing comma before end of object" k)
              else objectItems s m fuel
end

/-- `json.loads(text)` on decoded text: `none` when it parses. -/
def checkText (s : Array Char) : Option Failure :=
  match value s (skipWs s 0) (3 * s.size + 3) with
  | .error e => some e
  | .ok j => let j := skipWs s j; if j = s.size then none else some (.decode "Extra data" j)

/-- `json.loads(body)` on bytes: decoded as UTF-8 (a leading byte-order mark
dropped, as `detect_encoding` picks `utf-8-sig`); undecodable bytes are
`UnicodeDecodeError`. UTF-16 and UTF-32 bodies are not detected. -/
def checkBytes (b : ByteArray) : Option Failure :=
  let b := if b.size ≥ 3 && b[0]! = 0xEF && b[1]! = 0xBB && b[2]! = 0xBF then b.extract 3 b.size else b
  match String.fromUTF8? b with
  | some t => checkText t.toList.toArray
  | none => some .other

end PyJson

end LeanFastapi
