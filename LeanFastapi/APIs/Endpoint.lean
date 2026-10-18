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

/-- What `declared_routes` needs to compile a route again under an
application's dependencies and overrides: the route's constant, its
function, its path and its own `dependencies`. -/
structure RouteRecord where
  route : Name
  decl : Name
  path : String
  deps : List Macro.Mark
  deriving Inhabited

/-- The routes declared in the current module, in declaration order. -/
initialize routeExt : SimplePersistentEnvExtension RouteRecord (Array RouteRecord) ←
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
def routeDependencies (args : Array (Name × Syntax)) : TermElabM (List Mark) := do
  match args.find? (·.1 == `dependencies) with
  | none => return []
  | some (_, s) =>
    match listElems 10000 s with
    | some xs => xs.mapM markOfSyntax
    | none => throwErrorAt s "`dependencies` is a list `[Depends f, ...]`"

/-- **A path operation's tree** (`get_dependant` on the function, under the
`dependencies` that head it: the application's, then the route's), with
the overrides `ovs` compiled in: its cache slots `σ`, the type `β` of its
values, its solve `Dep σ β`, and the call of the function on them. Whether
the bodies are embedded is decided on the tree without overrides, as
FastAPI decides it when the route is created. -/
def routeTree (decl : Name) (pathNames : List String) (heads : List Mark) (ovs : Overrides) :
    MetaM (Expr × Expr × Expr × Expr) := do
  let fnE ← mkConstWithLevelParams decl
  let pre ← heads.mapM (subOf maxDepth ovs pathNames [])
  let fnArgs ← argsOf maxDepth ovs pathNames [] decl.toString false { fn := fnE, name := decl.toString }
  let all := pre ++ fnArgs
  -- `_should_embed_body_fields`: several body parameters (by name) are read
  -- from members of the body
  let all := if (Node.bodyNamesList all).eraseDups.length > 1 then Node.embedBodiesList all else all
  let slots := keysOfList all []
  let σ ← cacheTypes slots
  let (depE, β, project) ← genArgs σ slots all
  let callE ← withLocalDeclD `v β fun v => do
    let vals ← project v
    mkLambdaFVars #[v] (mkAppN fnE (vals.drop pre.length).toArray)
  return (σ, β, depE, callE)

/-- Build `decl.route` for a path operation attribute, and the route's own
`dependencies`. -/
def mkRoute (decl : Name) (methodsDefault : List String) (stx : Syntax) : TermElabM (Expr × List Mark) := do
  let path := stx[1].isStrLit?.getD ""
  let args := namedArgs stx
  for (n, s) in args do
    unless knownArgs.contains n do throwErrorAt s "unknown path operation argument `{n}`"
  let info ← getConstInfo decl
  let pathNames := pathParamNames (pathFormat path)
  let routeDeps ← routeDependencies args
  let (σ, β, depE, callE) ← routeTree decl pathNames routeDeps []
  forallTelescope info.type fun _ body => do
    let γ ← handlerResult body
    if γ.hasFVar then throwError "the result type of `{decl}` depends on its arguments"
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
    let route ← mkAppOptM ``LeanFastapi.APIRoute.make
      #[some σ, some β, some γ, none, some endpointE, some (toExpr path), some methodsE, some nameE, some explicit,
        some tagsE, some summaryE, some descrE, some respDescrE, some deprE, some opIdE, some inclE]
    return (route, routeDeps)

/-- Run the attribute: define and record `decl.route`. -/
def addRoute (decl : Name) (methods : List String) (stx : Syntax) : AttrM Unit := do
  let (value, deps) ← (Term.TermElabM.run' do
    let (v, ds) ← mkRoute decl methods stx
    let ds ← ds.mapM fun m => do pure { m with dependency := ← instantiateMVars m.dependency }
    return (← instantiateMVars v, ds)).run'
  if value.hasMVar || deps.any (·.dependency.hasMVar) then throwError "could not build the route of `{decl}`"
  let routeName := decl ++ `route
  addAndCompile <| .defnDecl {
    name := routeName, levelParams := [], type := Lean.mkConst ``LeanFastapi.APIRoute, value
    hints := .abbrev, safety := .safe }
  modifyEnv (routeExt.addEntry · { route := routeName, decl, path := stx[1].isStrLit?.getD "", deps })

/-! ## Compiling routes for an application -/

/-- The application dependencies (mark and key) and the overrides (the
replaced dependency's name, the override's mark, both keys) of an
application term, read off the term: `FastAPI.new (dependencies := ...)`,
`overrideDependency`, `clearOverrides`, `withRoutes`, `{ app with ... }`,
and definitions of these. -/
abbrev AppDeps := List (Mark × Expr) × List (String × Mark × Expr × Expr)

mutual

def readApp (fuel : Nat) (e : Expr) : MetaM AppDeps := do
  match fuel with
  | 0 => throwError "could not read the dependencies of `{e}`"
  | fuel + 1 =>
    let e ← whnfCore (← instantiateMVars e)
    let args := e.getAppArgs
    match e.getAppFn.constName? with
    | some ``FastAPI.overrideDependency =>
      let (ds, os) ← readApp fuel args[1]!
      let some (om, ok) ← markOfDependency? args[2]! | throwError "`{args[2]!}` is not `Depends ...`"
      let some (vm, vk) ← markOfDependency? args[3]! | throwError "`{args[3]!}` is not `Depends ...`"
      let name := (← shapeOf om.dependency).name
      return (ds, os.filter (·.1 != name) ++ [(name, vm, ok, vk)])
    | some ``FastAPI.clearOverrides => return ((← readApp fuel args[0]!).1, [])
    | some ``FastAPI.withRoutes => readApp fuel args[0]!
    | some `LeanFastapi.FastAPI.new => return (← readDeps fuel args[10]!, [])
    | some ``FastAPI.mk => return (← readDeps fuel args[13]!, ← readOvs fuel args[14]!)
    | some _ =>
      match ← unfoldDefinition? e with
      | some e' => readApp fuel e'
      | none => throwError "the dependencies and overrides of the application `{e}` must be known when its routes are compiled"
    | none => throwError "the dependencies and overrides of the application `{e}` must be known when its routes are compiled"

/-- An application's `dependencies` list. -/
def readDeps (fuel : Nat) (e : Expr) : MetaM (List (Mark × Expr)) := do
  match fuel with
  | 0 => throwError "could not read the dependencies `{e}`"
  | fuel + 1 =>
    let e ← whnfCore (← instantiateMVars e)
    if e.isAppOfArity ``FastAPI.dependencies 1 then return (← readApp fuel e.appArg!).1
    if e.isAppOfArity ``List.nil 1 then return []
    if e.isAppOfArity ``List.cons 3 then
      let some d ← markOfDependency? e.appFn!.appArg! | throwError "`{e.appFn!.appArg!}` is not `Depends ...`"
      return d :: (← readDeps fuel e.appArg!)
    match ← unfoldDefinition? e with
    | some e' => readDeps fuel e'
    | none => throwError "the dependencies `{e}` must be a list of `Depends ...` known when the routes are compiled"

/-- An application's `dependency_overrides`, kept from another application
or cleared. -/
def readOvs (fuel : Nat) (e : Expr) : MetaM (List (String × Mark × Expr × Expr)) := do
  match fuel with
  | 0 => throwError "could not read the overrides `{e}`"
  | fuel + 1 =>
    let e ← whnfCore (← instantiateMVars e)
    if e.isAppOfArity ``FastAPI.dependency_overrides 1 then return (← readApp fuel e.appArg!).2
    if e.isAppOfArity ``List.nil 1 then return []
    throwError "the overrides `{e}` must come from `overrideDependency` on an application"

end

/-- **A route compiled for an application**: `route`'s tree again, headed
by the application's dependencies, with its overrides in force, and
marked with the application's `signatureOf`. -/
def compileRoute (r : RouteRecord) (deps : List (Mark × Expr)) (ovs : List (String × Mark × Expr × Expr)) :
    MetaM Expr := do
  let some v := (← getConstInfo r.route).value? | throwError "no route `{r.route}`"
  let a := v.getAppArgs
  unless v.isAppOfArity ``LeanFastapi.APIRoute.make 16 do throwError "`{r.route}` is not a compiled route"
  let epa := a[4]!.getAppArgs
  let (σ, β, dep, call) ← routeTree r.decl (pathParamNames (pathFormat r.path)) (deps.map (·.1) ++ r.deps)
    (ovs.map fun (n, m, _, _) => (n, m))
  let ep := mkAppN (Lean.mkConst ``LeanFastapi.Endpoint.mk) #[σ, β, a[2]!, dep, call, epa[5]!, epa[6]!]
  let route := mkAppN v.getAppFn (#[σ, β, a[2]!, a[3]!, ep] ++ a.extract 5 a.size)
  let anyTy := Lean.mkConst ``LeanFastapi.AnyDependency
  let keyTy := Lean.mkConst ``LeanFastapi.CacheKey
  let depsE ← mkListLit anyTy (deps.map fun (_, k) => mkApp (Lean.mkConst ``LeanFastapi.AnyDependency.mk) k)
  let ovsE ← mkListLit (← mkAppM ``Prod #[keyTy, keyTy]) (← ovs.mapM fun (_, _, ok, vk) => mkAppM ``Prod.mk #[ok, vk])
  let sig ← mkAppM ``LeanFastapi.signatureOf #[depsE, ovsE]
  mkAppM ``LeanFastapi.APIRoute.compiled #[sig, route]

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
  let records : Array RouteRecord := match appConst? with
    | some c =>
      match env.getModuleIdxFor? c with
      | some idx => routeExt.getModuleEntries env idx
      | none => routeExt.getState env
    | none => #[]
  let (deps, ovs) ← Macro.readApp 1000 app
  let routes ← if deps.isEmpty && ovs.isEmpty then pure (records.toList.map fun r => Lean.mkConst r.route)
    else records.toList.mapM fun r => Macro.compileRoute r deps ovs
  goal.assign (← mkListLit (Lean.mkConst ``LeanFastapi.APIRoute) routes)
  Tactic.replaceMainGoal []

end LeanFastapi
