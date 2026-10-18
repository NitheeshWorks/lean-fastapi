import LeanFastapi.RepoImpl.Endpoint

/-!
# RepoImpl: names FastAPI derives

* `pathFormat`: Starlette's `compile_path` path format, with convertors
  dropped (`/items/{item_id:int}` is `/items/{item_id}`);
* `pathParamNames`: `get_path_param_names`, the names between braces;
* `snakeCase`: a Lean function name as the Python name FastAPI would see
  (`readItem` is `read_item`), so summaries and operation ids match the
  upstream app's;
* `generateUniqueId`: `fastapi.utils.generate_unique_id`, per method (see
  `CONTRIBUTING.md`, deviation: upstream uses the first method of a set for
  every method of a route);
* `headerAlias`: a header parameter's name with `_` as `-`
  (`convert_underscores=True`).
-/

namespace LeanFastapi

/-- `compile_path(path)[1]`: the path with each `{name:convertor}` written
`{name}`. -/
def pathFormat (path : String) : String :=
  String.ofList (go false path.toList)
where
  go (inConv : Bool) : List Char → List Char
    | [] => []
    | '}' :: cs => '}' :: go false cs
    | ':' :: cs => if inConv then go true cs else ':' :: go false cs
    | '{' :: cs => '{' :: goName cs
    | c :: cs => if inConv then go true cs else c :: go false cs
  goName : List Char → List Char
    | [] => []
    | '}' :: cs => '}' :: go false cs
    | ':' :: cs => go true cs
    | c :: cs => c :: goName cs

/-- `get_path_param_names(path)`: the text of every `{...}`. -/
def pathParamNames (path : String) : List String :=
  go path.toList
where
  go : List Char → List String
    | [] => []
    | '{' :: cs =>
      let name := cs.takeWhile (· ≠ '}')
      if (cs.dropWhile (· ≠ '}')).isEmpty then [] else String.ofList name :: go (cs.drop (name.length + 1))
    | _ :: cs => go cs
  termination_by l => l.length
  decreasing_by all_goals simp_wf <;> omega

/-- A Lean (camel-case) function name in Python's snake case: an upper-case
letter after a lower-case letter or digit starts a new word. Names already in
snake case are unchanged. -/
def snakeCase (name : String) : String :=
  String.ofList (go none name.toList)
where
  go (prev : Option Char) : List Char → List Char
    | [] => []
    | c :: cs =>
      if c.isUpper then
        (match prev with
          | some p => if p.isLower || p.isDigit then ['_', c.toLower] else [c.toLower]
          | none => [c.toLower]) ++ go (some c) cs
      else c :: go (some c) cs

/-- A character of Python's `\w` (ASCII letters, digits, `_`; other
characters outside ASCII are taken as word characters). -/
def isWordChar (c : Char) : Bool := c.isAlphanum || c = '_' || c.toNat > 127

/-- `re.sub(r"\W", "_", s)`. -/
def sanitizeId (s : String) : String := String.ofList (s.toList.map fun c => if isWordChar c then c else '_')

/-- `generate_unique_id(route)` for one of the route's methods:
`{name}{path_format}` with non-word characters as `_`, then `_{method}`. -/
def generateUniqueId (name path method : String) : String :=
  sanitizeId (name ++ pathFormat path) ++ "_" ++ method.toLower

/-- A header parameter's wire name: `_` written `-`. -/
def headerAlias (name : String) : String := String.ofList (name.toList.map fun c => if c = '_' then '-' else c)

end LeanFastapi
