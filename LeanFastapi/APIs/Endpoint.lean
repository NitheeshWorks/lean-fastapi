import Lean
import LeanFastapi.APIs.Depends

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
   `response_model_include, `response_model_exclude, `methods, `dependencies]

/-- The elements of a list literal, also once expanded to
`List.cons x (List.cons y List.nil)` (as attribute arguments arrive). -/
def listElems : Nat → Syntax → Option (List Syntax)
  | 0, _ => none
  | fuel + 1, s =>
    match s with
    | `([$xs,*]) => some (xs.getElems.toList.map (·.raw))
    | _ =>
      if s.isIdent && s.getId.eraseMacroScopes == ``List.nil then some []
      else if s.getKind == ``Lean.Parser.Term.app && s[0].isIdent && s[0].getId.eraseMacroScopes == ``List.cons &&
          s[1].getNumArgs == 2 then
        (listElems fuel s[1][1]).map (s[1][0] :: ·)
      else none

/-- The route-level `(dependencies := [Depends f, Security g ["s"]])`. -/
def routeDependencies (args : Array (Name × Syntax)) (pathNames : List String) : TermElabM (List Node) := do
  match args.find? (·.1 == `dependencies) with
  | none => return []
  | some (_, s) =>
    match listElems 10000 s with
    | some xs => xs.mapM fun x => do subOf maxDepth pathNames [] (← markOfSyntax x)
    | none => throwErrorAt s "`dependencies` is a list `[Depends f, ...]`"

/-- Build `decl.route` for a path operation attribute. -/
def mkRoute (decl : Name) (methodsDefault : List String) (stx : Syntax) : TermElabM Expr := do
  let path := stx[1].isStrLit?.getD ""
  let args := namedArgs stx
  for (n, s) in args do
    unless knownArgs.contains n do throwErrorAt s "unknown path operation argument `{n}`"
  let info ← getConstInfo decl
  let pathNames := pathParamNames (pathFormat path)
  let fnE ← mkConstWithLevelParams decl
  let routeDeps ← routeDependencies args pathNames
  let fnArgs ← argsOf maxDepth pathNames [] decl.toString false { fn := fnE, name := decl.toString }
  let all := routeDeps ++ fnArgs
  -- `_should_embed_body_fields`: several body parameters (by name) are read
  -- from members of the body
  let all := if (Node.bodyNamesList all).eraseDups.length > 1 then Node.embedBodiesList all else all
  let slots := keysOfList all []
  let σ ← cacheTypes slots
  let (depE, β, project) ← genArgs maxDepth σ slots all
  forallTelescope info.type fun _ body => do
    let γ ← handlerResult body
    if γ.hasFVar then throwError "the result type of `{decl}` depends on its arguments"
    let callE ← withLocalDeclD `v β fun v => do
      let vals ← project v
      mkLambdaFVars #[v] (mkAppN fnE (vals.drop routeDeps.length).toArray)
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
    let endpointE ← mkAppOptM ``LeanFastapi.Endpoint.mk #[some σ, some β, some γ, some depE, some callE, some rmE,
      some statusE]
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
      #[some σ, some β, some γ, none, some endpointE, some (toExpr path), some methodsE, some nameE, some explicit,
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
application, in declaration order. The application is the first named
`FastAPI` declaration the expression mentions (`app`, or
`app.overrideDependency ...`); without one there are none. -/
elab "declared_routes" : tactic => Tactic.withMainContext do
  let goal ← Tactic.getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let app := ty.appArg!
  let env ← getEnv
  -- the application is the first `FastAPI` constant in the expression
  -- (`app`, or `app.overrideDependency ...`)
  let fastapi := Lean.mkConst ``LeanFastapi.FastAPI
  let appConst? := (app.foldConsts #[] fun c acc => acc.push c).find? fun c =>
    match env.find? c with
    | some ci => ci.type == fastapi
    | none => false
  let names : Array Name := match appConst? with
    | some c =>
      match env.getModuleIdxFor? c with
      | some idx => routeExt.getModuleEntries env idx
      | none => routeExt.getState env
    | none => #[]
  goal.assign (← mkListLit (Lean.mkConst ``LeanFastapi.APIRoute) (names.toList.map mkConst))
  Tactic.replaceMainGoal []

end LeanFastapi
