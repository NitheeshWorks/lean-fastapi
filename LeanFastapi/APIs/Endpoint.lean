import Lean
import LeanFastapi.RepoImpl.Infer

/-!
# APIs: path operation attributes

```lean
@[get "/items/{item_id}"]
def readItem (item_id : Int) (q : Option String := none) : Handler Json :=
  return json% {"item_id": item_id, "q": q}
```

is FastAPI's `@app.get("/items/{item_id}")`. The attribute reads the
function's arguments and does what `get_dependant` and `analyze_param` do:
each argument's kind comes from `inferParam` (a name in the path template is
a path parameter, a model is the body, anything else is a query parameter,
and `Path`, `Query`, `Header`, `Cookie`, `Body` say so explicitly), its
default from the argument's own default, its type's validator, serialiser and
schema from its `FromJson`, `ToJson` and `JsonSchema` instances. It then
defines `readItem.route : APIRoute` and records it, so the application
declared in the same module serves it (`FastAPI.run` and the other
application functions collect the module's routes).

The return type `Handler γ` gives the response model, as FastAPI takes it
from the return annotation: a `γ` with a JSON Schema is validated and dumped
through it; `Json` and `Response` have none. `(response_model := T)`
overrides it.

Named arguments, as `@app.get(...)` takes them: `response_model`,
`status_code`, `tags`, `summary`, `description` (else the doc string),
`response_description`, `deprecated`, `operation_id`, `include_in_schema`,
`name` (else the function's name in snake case),
`response_model_exclude_none`, `response_model_exclude_defaults`,
`response_model_include`, `response_model_exclude`. `(response_model := none)`
keeps the return type out of validation and of the schema, as
`response_model=None` does. `@[api_route "/p"
(methods := ["GET", "POST"])]` takes several methods.

Everything here is total, like the rest of the library: the attribute is a
`MetaM` program over the function's type.
-/

namespace LeanFastapi

open Lean Meta Elab Term

/-- The routes declared in the current module, in declaration order. -/
initialize routeExt : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension { addEntryFn := Array.push, addImportedFn := fun _ => #[] }

/-- One `(name := value)` argument of a path operation attribute. -/
syntax routeArg := "(" ident " := " term ")"

namespace Attr
syntax (name := get) &"get " str (ppSpace routeArg)* : attr
syntax (name := put) &"put " str (ppSpace routeArg)* : attr
syntax (name := post) &"post " str (ppSpace routeArg)* : attr
syntax (name := delete) &"delete " str (ppSpace routeArg)* : attr
syntax (name := patch) &"patch " str (ppSpace routeArg)* : attr
syntax (name := options) &"options " str (ppSpace routeArg)* : attr
syntax (name := head) &"head " str (ppSpace routeArg)* : attr
syntax (name := trace) &"trace " str (ppSpace routeArg)* : attr
syntax (name := api_route) &"api_route " str (ppSpace routeArg)* : attr
end Attr

namespace Macro

/-- The wrapper an argument type is written with, and its arguments. -/
def wrapperOf (ty : Expr) : Wrapper × Array Expr :=
  let args := ty.getAppArgs
  match ty.getAppFn.constName? with
  | some ``LeanFastapi.Path => (.path, args)
  | some ``LeanFastapi.Query => (.query, args)
  | some ``LeanFastapi.Header => (.header, args)
  | some ``LeanFastapi.Cookie => (.cookie, args)
  | some ``LeanFastapi.Body => (.body, args)
  | _ => (.none, #[ty])

/-- Whether a type is FastAPI's non-scalar field, read from the body: a
model, a `Dict` or a `List` (optionally `Option` of one). -/
def isModelType (ty : Expr) : MetaM Bool := do
  let ty ← instantiateMVars ty
  let base := if ty.isAppOfArity ``Option 1 then ty.appArg! else ty
  if base.isAppOfArity ``LeanPydantic.Dict 1 || base.isAppOfArity ``List 1 then return true
  return (← synthInstance? (mkApp (Lean.mkConst ``LeanPydantic.Model) base)).isSome

/-- `none : Option String`. -/
def noneString : MetaM Expr := mkAppOptM ``Option.none #[some (Lean.mkConst ``String)]

/-- The `Source` constructor. -/
def sourceExpr : Source → Expr
  | .path => Lean.mkConst ``Source.path
  | .query => Lean.mkConst ``Source.query
  | .header => Lean.mkConst ``Source.header
  | .cookie => Lean.mkConst ``Source.cookie
  | .body => Lean.mkConst ``Source.body

/-- The `Param` of an argument. -/
def paramExpr (source : Source) (name : String) (w : Wrapper) (args : Array Expr) (α : Expr)
    (default : Option Expr) : MetaM Expr := do
  let ns ← noneString
  let arg (i : Nat) (d : Expr) : Expr := args.getD i d
  -- alias, convert_underscores, title, description, deprecated, include_in_schema, embed, media_type
  let (alias, conv, title, descr, depr, incl, embed, media) : Expr × Expr × Expr × Expr × Expr × Expr × Expr × Expr :=
    match w with
    | .path => (ns, toExpr true, arg 1 ns, arg 2 ns, arg 3 (toExpr false), arg 4 (toExpr true), toExpr false,
        toExpr "application/json")
    | .query | .cookie => (arg 1 ns, toExpr true, arg 2 ns, arg 3 ns, arg 4 (toExpr false), arg 5 (toExpr true),
        toExpr false, toExpr "application/json")
    | .header => (arg 1 ns, arg 2 (toExpr true), arg 3 ns, arg 4 ns, arg 5 (toExpr false), arg 6 (toExpr true),
        toExpr false, toExpr "application/json")
    | .body => (arg 3 ns, toExpr true, arg 4 ns, arg 5 ns, toExpr false, toExpr true, arg 1 (toExpr false),
        arg 2 (toExpr "application/json"))
    | .none => (ns, toExpr true, ns, ns, toExpr false, toExpr true, toExpr false, toExpr "application/json")
  let dflt ← match default with
    | some d => mkAppOptM ``Option.some #[some α, some d]
    | none => mkAppOptM ``Option.none #[some α]
  mkAppOptM ``LeanFastapi.mkParam
    #[some α, some (sourceExpr source), some (toExpr name), some dflt, some alias, some conv, some title,
      some descr, some depr, some incl, some embed, some media]

/-- `(v.2.2. ... .1)`: the `k`-th component of a right-nested product. -/
def projAt (v : Expr) : Nat → MetaM Expr
  | 0 => mkAppM ``Prod.fst #[v]
  | k + 1 => do projAt (← mkAppM ``Prod.snd #[v]) k

/-- The value type `γ` of `Handler γ`. -/
def handlerResult (body : Expr) : MetaM Expr := do
  let b ← whnfR body
  let b ← whnfR b
  if b.isAppOfArity ``ExceptT 3 then return b.appArg!
  throwError "a path operation function returns `Handler α`, not `{body}`"

/-- The named arguments of the attribute. -/
def namedArgs (stx : Syntax) : Array (Name × Syntax) :=
  stx[2].getArgs.map fun a => (a[1].getId.eraseMacroScopes, a[3])

/-- Elaborate a named argument at a type, or use the default. -/
def argOr (args : Array (Name × Syntax)) (n : Name) (ty : Expr) (dflt : TermElabM Expr) : TermElabM Expr := do
  match args.find? (·.1 == n) with
  | some (_, s) =>
    let e ← elabTermEnsuringType s ty
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  | none => dflt

/-- The known argument names. -/
def knownArgs : List Name :=
  [`response_model, `status_code, `tags, `summary, `description, `response_description, `deprecated,
   `operation_id, `include_in_schema, `name, `response_model_exclude_none, `response_model_exclude_defaults,
   `response_model_exclude_unset, `response_model_by_alias,
   `response_model_include, `response_model_exclude, `methods]

/-- An argument as the route macro sees it. -/
structure Arg where
  index : Nat
  name : String
  kind : ParamKind
  base : Expr
  param : Option Expr

/-- Build `decl.route` for a path operation attribute. -/
def mkRoute (decl : Name) (methodsDefault : List String) (stx : Syntax) : TermElabM Expr := do
  let path := stx[1].isStrLit?.getD ""
  let args := namedArgs stx
  for (n, s) in args do
    unless knownArgs.contains n do throwErrorAt s "unknown path operation argument `{n}`"
  let info ← getConstInfo decl
  let pathNames := pathParamNames (pathFormat path)
  forallTelescope info.type fun xs body => do
    let mut argsInfo : Array Arg := #[]
    for h : i in [0:xs.size] do
      let x := xs[i]
      let ld ← x.fvarId!.getDecl
      unless ld.binderInfo.isExplicit do
        throwError "path operation argument `{ld.userName}` must be explicit"
      let ty := ld.type
      let (ty, default) := match ty.getOptParamDefault? with
        | some d => (ty.appFn!.appArg!, some d)
        | none => (ty, none)
      if ty.hasFVar then throwError "the type of `{ld.userName}` depends on another argument"
      let name := ld.userName.eraseMacroScopes.toString
      let (w, wargs) := wrapperOf ty
      let base := wargs.getD 0 ty
      let isRequest := base.isConstOf ``LeanStarlette.Request
      let isModel ← isModelType base
      let kind := inferParam { name, inPath := pathNames.contains name, wrapper := w, isModel, isRequest }
      match kind with
      | .invalid msg => throwError msg
      | .request => argsInfo := argsInfo.push { index := i, name, kind, base, param := none }
      | .param src =>
        let p ← paramExpr src name w wargs base default
        argsInfo := argsInfo.push { index := i, name, kind, base, param := some p }
    -- FastAPI's order: path, query, header, cookie, body (stable)
    let srcRank : Arg → Nat := fun a => match a.kind with | .param s => s.rank | _ => 99
    let params := (argsInfo.filter (·.param.isSome)).toList.mergeSort (fun a b => srcRank a ≤ srcRank b)
    if (params.filter (srcRank · == Source.body.rank)).length > 1 then
      throwError "more than one body parameter: embedded bodies are not supported yet"
    -- the parameter product and its type
    let mut paramsE := Lean.mkConst ``LeanFastapi.Params.nil
    let mut β := Lean.mkConst ``Unit
    for a in params.reverse do
      paramsE ← mkAppOptM ``LeanFastapi.Params.cons #[some a.base, some β, none, none, none, a.param, some paramsE]
      β ← mkAppM ``Prod #[a.base, β]
    let γ ← handlerResult body
    let reqTy := Lean.mkConst ``LeanStarlette.Request
    let callE ← withLocalDeclD `v β fun v => withLocalDeclD `request reqTy fun req => do
      let mut callArgs : Array Expr := #[]
      for a in argsInfo do
        match a.kind with
        | .request => callArgs := callArgs.push req
        | _ =>
          let k := (params.findIdx? (·.index == a.index)).getD 0
          callArgs := callArgs.push (← projAt v k)
      mkLambdaFVars #[v, req] (mkAppN (← mkConstWithLevelParams decl) callArgs)
    -- the response model
    let jsonTy := Lean.mkConst ``LeanJson.Json
    let respTy := Lean.mkConst ``LeanStarlette.Response
    let rmTy? ← match args.find? (·.1 == `response_model) with
      | some (_, s) =>
        -- `response_model=None` turns the return type's model off, as in FastAPI
        if s.isIdent && s.getId.eraseMacroScopes == `none then pure none else some <$> elabType s
      | none =>
        if γ.isConstOf ``LeanJson.Json || γ.isConstOf ``LeanStarlette.Response then pure none
        else do
          let ok ← [``LeanPydantic.FromJson, ``LeanPydantic.ToJson, ``LeanPydantic.JsonSchema].allM fun c =>
            return (← synthInstance? (mkApp (Lean.mkConst c) γ)).isSome
          pure (if ok then some γ else none)
    let _ := (jsonTy, respTy)
    let boolTy := Lean.mkConst ``Bool
    let optsE ← do
      let exNone ← argOr args `response_model_exclude_none boolTy (pure (toExpr false))
      let exDef ← argOr args `response_model_exclude_defaults boolTy (pure (toExpr false))
      let exUnset ← argOr args `response_model_exclude_unset boolTy (pure (toExpr false))
      let byAlias ← argOr args `response_model_by_alias boolTy (pure (toExpr true))
      let listStr ← mkAppM ``List #[Lean.mkConst ``String]
      let optList ← mkAppM ``Option #[listStr]
      let incl ← argOr args `response_model_include optList (mkAppOptM ``Option.none #[some listStr])
      let excl ← argOr args `response_model_exclude listStr (mkAppOptM ``List.nil #[some (Lean.mkConst ``String)])
      mkAppM ``LeanFastapi.responseDumpOpts #[incl, excl, byAlias, exUnset, exDef, exNone]
    let rmE ← match rmTy? with
      | some t => do
        let m ← mkAppOptM ``LeanFastapi.ResponseModel.of #[some t, none, none, none, some optsE]
        mkAppM ``Option.some #[m]
      | none => mkAppOptM ``Option.none #[some (Lean.mkConst ``LeanFastapi.ResponseModel)]
    let statusE ← match args.find? (·.1 == `status_code) with
      | some (_, s) => do
        let e ← elabTermEnsuringType (← `((⟨$(⟨s⟩), by decide⟩ : LeanFastapi.Status))) (Lean.mkConst ``LeanFastapi.Status)
        synthesizeSyntheticMVarsNoPostponing
        instantiateMVars e
      | none => do
        let e ← elabTermEnsuringType (← `((⟨200, by decide⟩ : LeanFastapi.Status))) (Lean.mkConst ``LeanFastapi.Status)
        synthesizeSyntheticMVarsNoPostponing
        instantiateMVars e
    let endpointE ← mkAppOptM ``LeanFastapi.Endpoint.mk #[some β, some γ, some paramsE, some callE, some rmE, some statusE]
    -- route metadata
    let strTy := Lean.mkConst ``String
    let optStr ← mkAppM ``Option #[strTy]
    let listStr ← mkAppM ``List #[strTy]
    let methodsE ← argOr args `methods listStr (mkListLit strTy (methodsDefault.map toExpr))
    let nameE ← argOr args `name strTy (pure (toExpr (snakeCase (decl.componentsRev.headD `x).toString)))
    let doc? ← findDocString? (← getEnv) decl
    let descrE ← argOr args `description optStr (match doc? with
      | some d => mkAppM ``Option.some #[toExpr (cleandoc d)]
      | none => mkAppOptM ``Option.none #[some strTy])
    let tagsE ← argOr args `tags listStr (mkAppOptM ``List.nil #[some strTy])
    let summaryE ← argOr args `summary optStr (mkAppOptM ``Option.none #[some strTy])
    let respDescrE ← argOr args `response_description strTy (pure (toExpr "Successful Response"))
    let deprE ← argOr args `deprecated boolTy (pure (toExpr false))
    let opIdE ← argOr args `operation_id optStr (mkAppOptM ``Option.none #[some strTy])
    let inclE ← argOr args `include_in_schema boolTy (pure (toExpr true))
    let explicit := toExpr ((args.find? (·.1 == `status_code)).isSome)
    mkAppOptM ``LeanFastapi.APIRoute.make
      #[some β, some γ, none, some endpointE, some (toExpr path), some methodsE, some nameE, some explicit,
        some tagsE, some summaryE, some descrE, some respDescrE, some deprE, some opIdE, some inclE]

/-- Run the attribute: define and record `decl.route`. -/
def addRoute (decl : Name) (methods : List String) (stx : Syntax) : AttrM Unit := do
  let value ← (Term.TermElabM.run' do instantiateMVars (← mkRoute decl methods stx)).run'
  if value.hasMVar then throwError "could not build the route of `{decl}`"
  let routeName := decl ++ `route
  addAndCompile <| .defnDecl {
    name := routeName, levelParams := [], type := Lean.mkConst ``LeanFastapi.APIRoute, value
    hints := .abbrev, safety := .safe }
  modifyEnv (routeExt.addEntry · routeName)

end Macro

initialize
  for (attr, methods) in [(`get, ["GET"]), (`put, ["PUT"]), (`post, ["POST"]), (`delete, ["DELETE"]),
      (`patch, ["PATCH"]), (`options, ["OPTIONS"]), (`head, ["HEAD"]), (`trace, ["TRACE"]),
      (`api_route, ["GET"])] do
    registerBuiltinAttribute {
      name := attr
      descr := s!"FastAPI `@app.{attr}(path)`: declare a path operation"
      applicationTime := .afterCompilation
      add := fun decl stx _ => Macro.addRoute decl methods stx }

/-- The attribute kinds of path operations. -/
def routeAttrKinds : List Name :=
  [``Attr.get, ``Attr.put, ``Attr.post, ``Attr.delete, ``Attr.patch, ``Attr.options, ``Attr.head,
   ``Attr.trace, ``Attr.api_route]

/-- A path operation's arguments are read by FastAPI even when the function
body ignores them (a path parameter only validated, as in
`update_item(item_id, item)`), so the unused-variable linter leaves the
explicit arguments of a declaration carrying a path operation attribute
alone. -/
@[unused_variables_ignore_fn]
def ignorePathOperationArgs : Lean.Linter.IgnoreFunction := fun _ stack _ =>
  stack.any (fun (s, _) => s.isOfKind ``Lean.Parser.Term.explicitBinder) &&
  stack.any fun (s, _) =>
    s.isOfKind ``Lean.Parser.Command.declaration &&
      (s[0].find? fun a => routeAttrKinds.contains a.getKind).isSome

/-! ## The routes of an application -/

/-- The path operations declared (with `@[get ...]` and the others) in the
module of an application. -/
def DeclaredRoutes (_app : FastAPI) : Type := List APIRoute

instance (app : FastAPI) : EmptyCollection (DeclaredRoutes app) := ⟨([] : List APIRoute)⟩

/-- `declared_routes`: the routes declared in the module that declares the
application, in declaration order. An application that is not a named
declaration has none. -/
elab "declared_routes" : tactic => Tactic.withMainContext do
  let goal ← Tactic.getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let app := ty.appArg!
  let env ← getEnv
  let names : Array Name := match app.getAppFn.constName? with
    | some c =>
      match env.getModuleIdxFor? c with
      | some idx => routeExt.getModuleEntries env idx
      | none => routeExt.getState env
    | none => #[]
  goal.assign (← mkListLit (Lean.mkConst ``LeanFastapi.APIRoute) (names.toList.map mkConst))
  Tactic.replaceMainGoal []

end LeanFastapi
