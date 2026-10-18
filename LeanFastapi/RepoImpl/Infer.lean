import LeanFastapi.RepoImpl.Applications

/-!
# RepoImpl: what kind of parameter a function argument is

`analyze_param` in `fastapi/dependencies/utils.py` decides, for each
argument of a path operation function, where its value comes from:

1. an argument of a special type (`Request`) is given the request;
2. a name in the path template is a path parameter (an explicit wrapper
   other than `Path` is an error: "Cannot use `Query` for path param");
3. an explicit `Path`, `Query`, `Header`, `Cookie` or `Body` says so;
4. otherwise a non-scalar type (a model, or an optional model) is the body,
   and anything else is a query parameter.

`inferParam` is that rule as a total function of the argument's shape; the
endpoint attribute computes the shape of each argument and calls it.
`ParamWrapper`s are the types the user writes (`Query (Option String)
(alias := "item-query")`): each is its argument type, with the metadata
FastAPI's `Query(...)` would take.
-/

namespace LeanFastapi

/-- An explicit parameter declaration. -/
inductive Wrapper where
  | none
  | path
  | query
  | header
  | cookie
  | body
  | form
  deriving DecidableEq, Repr, Inhabited

/-- What `analyze_param` looks at. -/
structure ParamShape where
  name : String
  /-- The name is one of the path template's parameters. -/
  inPath : Bool
  wrapper : Wrapper := .none
  /-- The type is a model, or an optional one (`not field_annotation_is_scalar`). -/
  isModel : Bool := false
  /-- The type is `Request`. -/
  isRequest : Bool := false
  deriving DecidableEq, Repr

/-- What an argument is. -/
inductive ParamKind where
  | param (source : Source)
  | request
  | invalid (message : String)
  deriving DecidableEq, Repr

/-- The source an explicit wrapper names. -/
def Wrapper.source : Wrapper → Source
  | .none | .query => .query
  | .path => .path
  | .header => .header
  | .cookie => .cookie
  | .body | .form => .body

/-- The Python class name of a wrapper, for messages. -/
def Wrapper.className : Wrapper → String
  | .none => "Param"
  | .path => "Path"
  | .query => "Query"
  | .header => "Header"
  | .cookie => "Cookie"
  | .body => "Body"
  | .form => "Form"

/-- **`analyze_param`'s rule.** -/
def inferParam (s : ParamShape) : ParamKind :=
  if s.isRequest then .request
  else if s.inPath then
    match s.wrapper with
    | .none | .path => .param .path
    | w => .invalid s!"Cannot use `{w.className}` for path param '{s.name}'"
  else
    match s.wrapper with
    | .none => .param (if s.isModel then .body else .query)
    | w => .param w.source

/-- A header parameter's wire name: its `alias`, else its name with `_` as
`-` when `convert_underscores` (the default), else its name. -/
def headerParamAlias (name : String) (alias : Option String) (convert_underscores : Bool) : String :=
  alias.getD (if convert_underscores then headerAlias name else name)

/-! ## The parameter wrappers -/

set_option linter.unusedVariables false in
/-- `Annotated[α, Path(...)]`. -/
@[reducible] def Path (α : Type) (title : Option String := none) (description : Option String := none)
    (deprecated : Bool := false) (include_in_schema : Bool := true) : Type := α

set_option linter.unusedVariables false in
/-- `Annotated[α, Query(...)]`. -/
@[reducible] def Query (α : Type) (alias : Option String := none) (title : Option String := none)
    (description : Option String := none) (deprecated : Bool := false) (include_in_schema : Bool := true) :
    Type := α

set_option linter.unusedVariables false in
/-- `Annotated[α, Header(...)]`. -/
@[reducible] def Header (α : Type) (alias : Option String := none) (convert_underscores : Bool := true)
    (title : Option String := none) (description : Option String := none) (deprecated : Bool := false)
    (include_in_schema : Bool := true) : Type := α

set_option linter.unusedVariables false in
/-- `Annotated[α, Cookie(...)]`. -/
@[reducible] def Cookie (α : Type) (alias : Option String := none) (title : Option String := none)
    (description : Option String := none) (deprecated : Bool := false) (include_in_schema : Bool := true) :
    Type := α

set_option linter.unusedVariables false in
/-- `Annotated[α, Body(...)]`. -/
@[reducible] def Body (α : Type) (embed : Bool := false) (media_type : String := "application/json")
    (alias : Option String := none) (title : Option String := none) (description : Option String := none) :
    Type := α

set_option linter.unusedVariables false in
/-- `Annotated[α, Form(...)]`: a field of an `application/x-www-form-urlencoded`
body. `json_schema_extra` adds members to its schema. -/
@[reducible] def Form (α : Type) (alias : Option String := none) (title : Option String := none)
    (description : Option String := none) (media_type : String := "application/x-www-form-urlencoded")
    (json_schema_extra : List (String × LeanJson.Json) := []) : Type := α

/-! ## The parameter of a wrapper -/

/-- The `Param` of an argument, from its source and its wrapper's metadata. -/
def mkParam {α : Type} (source : Source) (name : String) (default : Option α) (alias : Option String := none)
    (convert_underscores : Bool := true) (title : Option String := none) (description : Option String := none)
    (deprecated : Bool := false) (include_in_schema : Bool := true) (embed : Bool := false)
    (media_type : String := "application/json") (json_schema_extra : List (String × LeanJson.Json) := []) :
    Param α where
  source
  name
  alias := if source = .header then headerParamAlias name alias convert_underscores else alias.getD name
  embed
  default
  title
  description
  deprecated
  include_in_schema
  media_type
  extra := json_schema_extra

/-! ## Dependencies -/

set_option linter.unusedVariables false in
/-- The type of an argument declared `(commons : Depends commonParameters)`:
the dependency's value, marked with the dependency (`Depends(dependency,
use_cache=True, scope=None)`; `scope` is `""`, `"function"` or
`"request"`). The `Depends` notation computes `α`. -/
@[reducible] def DependsT {τ : Sort u} (dependency : τ) (α : Type) (use_cache : Bool) (scope : String) : Type := α

set_option linter.unusedVariables false in
/-- The type of an argument declared `(user : Security getCurrentUser
["items"])`: `Security(dependency, scopes=[...], use_cache=True)`. -/
@[reducible] def SecurityT {τ : Sort u} (dependency : τ) (α : Type) (scopes : List String) (use_cache : Bool) :
    Type := α

/-- `pure a` in `Handler`: a dependency that computes its value without
effects (a class dependency's constructor). -/
def handlerPure {α : Type} (a : α) : Handler α := pure a

/-! ## Documentation strings -/

/-- `inspect.cleandoc(doc).split("\f")[0].strip()`: a function's doc string
as an operation description. -/
def cleandoc (doc : String) : String :=
  let lines := (doc.splitOn "\n").map fun l => String.ofList (l.toList.reverse.dropWhile Char.isWhitespace).reverse
  let indent (l : String) : Option Nat :=
    if l.all Char.isWhitespace then none else some (l.toList.takeWhile (· = ' ')).length
  let rest := lines.drop 1
  let common := (rest.filterMap indent).foldl Nat.min (rest.filterMap indent |>.headD 0)
  let lines := match lines with
    | [] => []
    | l :: ls => pyStrip l :: ls.map fun x => String.ofList (x.toList.drop common)
  let text := "\n".intercalate lines
  pyStrip ((text.splitOn "\x0c").headD "")

end LeanFastapi
