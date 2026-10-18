import Lean
import LeanFastapi.RepoImpl.Infer
import LeanFastapi.RepoImpl.Security

/-!
# APIs: `Depends` and `Security`

```lean
def commonParameters (q : Option String := none) (skip : Nat := 0) (limit : Nat := 100) :
    Handler Commons :=
  return { q, skip, limit }

@[get "/items/"]
def readItems (commons : Depends commonParameters) : Handler Commons :=
  return commons
```

is FastAPI's `commons: Annotated[dict, Depends(common_parameters)]`. As the
type of an argument, `Depends f` is `f`'s value (`DependsT f α ...`, which
reduces to `α`); the path operation attribute reads the mark and solves `f`
before calling the function. As a value (`FastAPI.new (dependencies :=
[Depends verifyToken])`, `app.overrideDependency (Depends f) (Depends g)`),
it is the type-erased `Dependency`.

A dependency is:

* a function returning `Handler α` (or a plain `α`), whose arguments are
  read as a path operation's are (parameters, `Request`, `SecurityScopes`,
  and further `Depends`);
* a function returning `Yield α` (`yield` dependencies), whose exit runs
  after the response (`scope := "request"`, the default) or after the
  function returns (`(scope := "function")`);
* a structure type (`Depends CommonQueryParams`, a class dependency): its
  fields are the arguments, with their defaults;
* a value whose type has a `call` method (a callable instance, or a
  security scheme such as `OAuth2PasswordBearer`): the method's arguments
  after `self`.

`Security f ["items"]` is `Security(f, scopes=["items"])`. Named arguments:
`(use_cache := false)`, `(scope := "function")`.

Overrides (`app.overrideDependency (Depends f) (Depends g)`) and the
application's `dependencies` are compiled into each route's tree when the
application collects its routes (`declared_routes`): a dependency with an
override in force is solved with the override's callable and arguments (and
so, recursively, inside the override's own tree), under its own cache key
and scope (`Dep.call`'s `ov`).

The analysis is a `MetaM` program over the types, bounded by the depth of
the tree (`maxDepth`): no `partial`.
-/

namespace LeanFastapi

open Lean Meta Elab Term

/-- One `(name := value)` argument of `Depends` or `Security`. -/
syntax depArg := "(" ident " := " term ")"

/-- `Depends(dependency, use_cache=True, scope=None)`. -/
syntax (name := dependsStx) "Depends " term:max (ppSpace depArg)* : term

/-- `Security(dependency, scopes=[...], use_cache=True)`. -/
syntax (name := securityStx) "Security " term:max (ppSpace "[" str,* "]")? (ppSpace depArg)* : term

namespace Macro

/-! ## Shared helpers -/

/-- The wrapper an argument type is written with, and its arguments. -/
def wrapperOf (ty : Expr) : Wrapper × Array Expr :=
  let args := ty.getAppArgs
  match ty.getAppFn.constName? with
  | some ``LeanFastapi.Path => (.path, args)
  | some ``LeanFastapi.Query => (.query, args)
  | some ``LeanFastapi.Header => (.header, args)
  | some ``LeanFastapi.Cookie => (.cookie, args)
  | some ``LeanFastapi.Body => (.body, args)
  | some ``LeanFastapi.Form => (.form, args)
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
    | .form => (arg 1 ns, toExpr true, arg 2 ns, arg 3 ns, toExpr false, toExpr true, toExpr true,
        arg 4 (toExpr "application/x-www-form-urlencoded"))
    | .none => (ns, toExpr true, ns, ns, toExpr false, toExpr true, toExpr false, toExpr "application/json")
  let extra ← match w with
    | .form => pure (args.getD 5 (← mkAppOptM ``List.nil #[some (← mkAppM ``Prod #[Lean.mkConst ``String,
        Lean.mkConst ``LeanJson.Json])]))
    | _ => mkAppOptM ``List.nil #[some (← mkAppM ``Prod #[Lean.mkConst ``String, Lean.mkConst ``LeanJson.Json])]
  let dflt ← match default with
    | some d => mkAppOptM ``Option.some #[some α, some d]
    | none => mkAppOptM ``Option.none #[some α]
  mkAppOptM ``LeanFastapi.mkParam
    #[some α, some (sourceExpr source), some (toExpr name), some dflt, some alias, some conv, some title,
      some descr, some depr, some incl, some embed, some media, some extra]

/-- `(v.2.2. ... .1)`: the `k`-th component of a right-nested product. -/
def projAt (v : Expr) : Nat → MetaM Expr
  | 0 => mkAppM ``Prod.fst #[v]
  | k + 1 => do projAt (← mkAppM ``Prod.snd #[v]) k

/-- The value type `γ` of `Handler γ`, if the type is one. -/
def handlerResult? (body : Expr) : MetaM (Option Expr) := do
  let b ← whnfR body
  let b ← whnfR b
  if b.isAppOfArity ``ExceptT 3 then return some b.appArg!
  return none

/-- The value type `γ` of `Handler γ`. -/
def handlerResult (body : Expr) : MetaM Expr := do
  match ← handlerResult? body with
  | some γ => return γ
  | none => throwError "a path operation function returns `Handler α`, not `{body}`"

/-- `[a, b, ...] : List String`. -/
def strList (l : List String) : Expr := toExpr l

/-! ## What a dependency is -/

/-- How a dependency computes its value. -/
inductive Kind where
  | handler
  | yield
  | pure
  deriving DecidableEq, Inhabited

/-- A dependency's callable: the function its arguments are applied to, its
name (the cache key and override name), its security scheme, and the
defaults of a class dependency's fields. -/
structure Shape where
  fn : Expr
  name : String
  scheme : Option Expr := none
  defaults : List (Name × Expr) := []

/-- The name of a dependency expression: its declaration's name. -/
def depName (x : Expr) : MetaM String := do
  match x.getAppFn.constName? with
  | some c => return c.toString
  | none => return toString (← ppExpr x)

/-- **The callable of a dependency** (`Dependant.call`). -/
def shapeOf (x : Expr) : MetaM Shape := do
  let x ← instantiateMVars x
  let xTy ← whnfR (← inferType x)
  let env ← getEnv
  if xTy.isSort then
    -- a class dependency: the structure's constructor, with its field defaults
    let some s := x.getAppFn.constName? | throwError "`{x}` is not a dependency"
    unless isStructure env s && x.getAppNumArgs == 0 do
      throwError "a class dependency is a structure without parameters, not `{x}`"
    let ctor := (getStructureCtor env s).name
    let fields := getStructureFields env s
    let mut defaults := []
    for f in fields do
      if let some d := getDefaultFnForField? env s f then
        let v := (← getConstInfo d).value!
        let v := if v.isAppOfArity ``id 2 then v.appArg! else v
        if v.isLambda then throwError "the default of `{s}.{f}` depends on other fields"
        defaults := defaults ++ [(f, v)]
    return { fn := Lean.mkConst ctor, name := s.toString, defaults }
  match xTy.getAppFn.constName? with
  | some t =>
    if isStructure env t && env.contains (t ++ `call) then
      let fn ← mkAppM (t ++ `call) #[x]
      let scheme ← do
        match ← synthInstance? (← mkAppM ``SecurityBase #[xTy]) with
        | some _ => pure (some (← mkAppM ``Prod.mk #[← mkAppM ``SecurityBase.scheme_name #[x],
            ← mkAppM ``SecurityBase.model #[x]]))
        | none => pure none
      return { fn, name := ← depName x, scheme }
    return { fn := x, name := ← depName x }
  | none => return { fn := x, name := ← depName x }

/-- The kind and value type of a callable's result type. -/
def resultOf (r : Expr) : MetaM (Kind × Expr) := do
  let r ← instantiateMVars r
  match ← handlerResult? r with
  | some α =>
    if α.isAppOfArity ``LeanFastapi.Yielded 1 then return (.yield, ← whnfR α.appArg!)
    return (.handler, ← whnfR α)
  | none => return (.pure, r)

/-- The value type of a dependency. -/
def valueType (x : Expr) : MetaM Expr := do
  let s ← shapeOf x
  forallTelescope (← inferType s.fn) fun _ r => do
    let (_, α) ← resultOf r
    if α.hasFVar then throwError "the value type of `{x}` depends on its arguments"
    return α

/-! ## The dependency tree -/

/-- An argument of a dependant, as `get_dependant` classifies it. -/
inductive Node where
  | request
  | scopes (s : List String)
  | param (source : Source) (base : Expr) (param : Expr)
  /-- A sub-dependency: its cache key, value type, callable, kind, `use_cache`,
  computed scope, own scopes, scheme, and its own arguments; and the
  override in force for it, if any (`ovFn`): its callable, kind and
  arguments. -/
  | sub (key : CacheKey) (α : Expr) (fn : Expr) (kind : Kind) (useCache : Bool) (scope : String)
      (own : List String) (scheme : Option Expr) (args : List Node)
      (ovFn : Option Expr) (ovKind : Kind) (ovArgs : List Node)
  deriving Inhabited

/-- `_uses_scopes`. -/
def Node.usesScopes : Node → Bool
  | .scopes _ => true
  | .sub _ _ _ _ _ _ own scheme args _ _ _ => !own.isEmpty || scheme.isSome || usesList args
  | _ => false
where
  usesList : List Node → Bool
    | [] => false
    | n :: ns => n.usesScopes || usesList ns

/-- Scopes in order, each once. -/
def dedupScopes (l : List String) : List String := mergeScopes [] l

/-- What a dependency mark says: the dependency, `use_cache`, the explicit
scope and its own scopes. -/
structure Mark where
  dependency : Expr
  useCache : Bool
  scope : String
  own : List String
  deriving Inhabited

/-- The overrides in force while a tree is read: the replaced dependency's
name, and the override's mark. -/
abbrev Overrides := List (String × Mark)

/-- Read a `DependsT`/`SecurityT` mark off an argument type. -/
def markOf? (ty : Expr) : MetaM (Option Mark) := do
  let ty ← instantiateMVars ty
  let evalBool (e : Expr) : MetaM Bool := do
    match (← whnfD e).constName? with
    | some ``Bool.true => pure true
    | some ``Bool.false => pure false
    | _ => throwError "`use_cache` must be a literal, not `{e}`"
  let evalStr (e : Expr) : MetaM String := do
    match (← whnfD e) with
    | .lit (.strVal s) => pure s
    | _ => throwError "a scope must be a string literal, not `{e}`"
  let evalStrs (e : Expr) : MetaM (List String) := do
    match (← reduce e).listLit? with
    | some (_, xs) => xs.mapM evalStr
    | none => throwError "scopes must be a list literal, not `{e}`"
  if ty.isAppOfArity ``DependsT 5 then
    let a := ty.getAppArgs
    return some { dependency := a[1]!, useCache := ← evalBool a[3]!, scope := ← evalStr a[4]!, own := [] }
  if ty.isAppOfArity ``SecurityT 5 then
    let a := ty.getAppArgs
    return some { dependency := a[1]!, useCache := ← evalBool a[4]!, scope := "",
                  own := ← evalStrs a[3]! }
  return none

/-- How deep a dependency tree may be. -/
def maxDepth : Nat := 64

mutual

/-- **`get_dependant`**: the arguments of a callable (`shape`), under the
scopes of the way to it (`current`: the parent's, then its own). A
request-scoped `yield` dependency (`isYieldRequest`) may not depend on a
function-scoped one (`DependencyScopeError`). Each node holds closed
expressions. -/
def argsOf (fuel : Nat) (ovs : Overrides) (pathNames : List String) (current : List String) (name : String)
    (isYieldRequest : Bool) (shape : Shape) : MetaM (List Node) := do
  match fuel with
  | 0 => throwError "the dependency tree of `{name}` is deeper than {maxDepth}"
  | fuel + 1 =>
    forallTelescope (← inferType shape.fn) fun xs _ => do
      let mut nodes : List Node := []
      for x in xs do
        let ld ← x.fvarId!.getDecl
        unless ld.binderInfo.isExplicit do
          throwError "dependency argument `{ld.userName}` of `{name}` must be explicit"
        let ty := ld.type
        let argName := ld.userName.eraseMacroScopes
        let (ty, default) := match ty.getOptParamDefault? with
          | some d => (ty.appFn!.appArg!, some d)
          | none => (ty, (shape.defaults.lookup argName))
        if ty.hasFVar then throwError "the type of `{argName}` depends on another argument"
        if let some m ← markOf? ty then
          if isYieldRequest && m.scope == "function" then
            -- `call_name` is the function's own name, without its namespace
            throwError "The dependency \"{(name.splitOn ".").getLastD name}\" has a scope of \"request\", it cannot depend on dependencies with scope \"function\"."
          nodes := nodes ++ [← subOf fuel ovs pathNames current m]
          continue
        let base0 := ty
        if base0.isConstOf ``SecurityScopes then
          nodes := nodes ++ [.scopes (dedupScopes current)]
          continue
        let pname := argName.toString
        let (w, wargs) := wrapperOf ty
        let base := wargs.getD 0 ty
        let isRequest := base.isConstOf ``LeanStarlette.Request
        let isModel ← isModelType base
        match inferParam { name := pname, inPath := pathNames.contains pname, wrapper := w, isModel, isRequest } with
        | .invalid msg => throwError msg
        | .request => nodes := nodes ++ [.request]
        | .param src =>
          let p ← paramExpr src pname w wargs base default
          nodes := nodes ++ [.param src base p]
      return nodes

/-- The kind and value type of a callable. -/
def kindOf (shape : Shape) : MetaM (Kind × Expr) := do
  forallTelescope (← inferType shape.fn) fun _ r => do
    let (k, α) ← resultOf r
    if α.hasFVar then throwError "the value type of `{shape.name}` depends on its arguments"
    return (k, α)

/-- The node of a marked argument (`get_sub_dependant`), under the scopes
`parent`. With an override in force for it, the override's callable is
read too (`get_dependant(call=override, ...)` in `solve_dependencies`), its
arguments under the same scopes and overrides, and its value type must be
the dependency's. -/
def subOf (fuel : Nat) (ovs : Overrides) (pathNames : List String) (parent : List String) (m : Mark) :
    MetaM Node := do
  match fuel with
  | 0 => throwError "the dependency tree is deeper than {maxDepth}"
  | fuel + 1 =>
    let shape ← shapeOf m.dependency
    let (kind, α) ← kindOf shape
    let scope := if m.scope.isEmpty then (if kind == .yield then "request" else "") else m.scope
    let current := parent ++ m.own
    let args ← argsOf fuel ovs pathNames current shape.name (kind == .yield && scope == "request") shape
    let node0 := Node.sub {call := shape.name} α shape.fn kind m.useCache scope m.own shape.scheme args none .pure []
    let key : CacheKey := { call := shape.name, scope,
                            scopes := if node0.usesScopes then (dedupScopes current).mergeSort (· ≤ ·) else [] }
    let (ovFn, ovKind, ovArgs) ← match ovs.lookup shape.name with
      | none => pure (none, Kind.pure, [])
      | some om => do
        let oshape ← shapeOf om.dependency
        let (okind, oα) ← kindOf oshape
        unless ← isDefEq oα α do
          throwError "the override `{oshape.name}` of `{shape.name}` gives `{oα}`, not `{α}`"
        let oargs ← argsOf fuel ovs pathNames current oshape.name (okind == .yield && scope == "request") oshape
        pure (some oshape.fn, okind, oargs)
    return .sub key α shape.fn kind m.useCache scope m.own shape.scheme args ovFn ovKind ovArgs

end

mutual

/-- The body parameters of a tree, each use counted. -/
def Node.bodies : Node → Nat
  | .param .body _ _ => 1
  | .sub _ _ _ _ _ _ _ _ args _ _ _ => Node.bodiesList args
  | _ => 0

def Node.bodiesList : List Node → Nat
  | [] => 0
  | n :: ns => n.bodies + Node.bodiesList ns

end

/-- The name of a body parameter (`mkParam`'s third argument). -/
def paramName? (p : Expr) : Option String :=
  if p.isAppOfArity ``LeanFastapi.mkParam 13 then
    match p.getAppArgs[2]! with
    | .lit (.strVal s) => some s
    | _ => none
  else none

mutual

/-- The names of the body parameters of a tree, each use counted. -/
def Node.bodyNames : Node → List String
  | .param .body _ p => (paramName? p).toList
  | .sub _ _ _ _ _ _ _ _ args _ _ _ => Node.bodyNamesList args
  | _ => []

def Node.bodyNamesList : List Node → List String
  | [] => []
  | n :: ns => n.bodyNames ++ Node.bodyNamesList ns

/-- The tree with every body parameter read from a member of the body
(`embed_body_fields`). -/
def Node.embedBodies : Node → Node
  | .param .body b p =>
    .param .body b (if p.isAppOfArity ``LeanFastapi.mkParam 13 then mkAppN p.getAppFn (p.getAppArgs.set! 10 (toExpr true))
      else p)
  | .sub key α fn kind uc sc own sch args ovFn ovKind ovArgs =>
    .sub key α fn kind uc sc own sch (Node.embedBodiesList args) ovFn ovKind (Node.embedBodiesList ovArgs)
  | n => n

def Node.embedBodiesList : List Node → List Node
  | [] => []
  | n :: ns => n.embedBodies :: Node.embedBodiesList ns

end

/-- Read a `Depends x ...` or `Security x [...] ...` term as a mark. -/
def markOfSyntax (stx : Syntax) : TermElabM Mark := do
  let (x, own, named) ←
    if stx.getKind == ``dependsStx then pure (stx[1], none, stx[2].getArgs)
    else if stx.getKind == ``securityStx then
      let scopes : List String :=
        if stx[2].getNumArgs == 0 then [] else (stx[2][1].getSepArgs.filterMap (·.isStrLit?)).toList
      pure (stx[1], some scopes, stx[3].getArgs)
    else throwErrorAt stx "expected `Depends ...` or `Security ...`"
  let named := named.map fun a => (a[1].getId.eraseMacroScopes, a[3])
  let mut useCache := true
  let mut scope := ""
  for (n, s) in named do
    if n == `use_cache then
      match s with
      | `(true) => useCache := true
      | `(false) => useCache := false
      | _ => throwErrorAt s "`use_cache` is `true` or `false`"
    else if n == `scope && own.isNone then
      match s.isStrLit? with
      | some v =>
        unless v == "function" || v == "request" do throwErrorAt s "`scope` is \"function\" or \"request\""
        scope := v
      | none => throwErrorAt s "`scope` is a string literal"
    else throwErrorAt s "unknown argument `{n}`"
  -- a bare name is elaborated with `@`, so its optional arguments are not
  -- filled in; its leading implicit arguments are then left to unification
  let xE ← if x.isIdent then do
      let e ← elabTerm (← `(@$(⟨x⟩))) none
      let (ms, bis, _) ← forallMetaTelescopeReducing (← inferType e) (kind := .natural)
      let k := (bis.toList.takeWhile (· != .default)).length
      let e := mkAppN e (ms.extract 0 k)
      for m in ms.extract 0 k, bi in bis.extract 0 k do
        if bi == .instImplicit then
          m.mvarId!.assign (← synthInstance (← inferType m))
      pure e
    else elabTerm x none
  synthesizeSyntheticMVarsNoPostponing
  return { dependency := ← instantiateMVars xE, useCache, scope, own := own.getD [] }

/-! ## The typed cache -/

mutual

/-- The distinct cache keys of a tree (an override's too), first-seen order,
with their value types. -/
def keysOf : Node → List (CacheKey × Expr) → List (CacheKey × Expr)
  | .sub key α _ _ _ _ _ _ args _ _ ovArgs, acc =>
    let acc := if acc.any (·.1 == key) then acc else acc ++ [(key, α)]
    keysOfList ovArgs (keysOfList args acc)
  | _, acc => acc

def keysOfList : List Node → List (CacheKey × Expr) → List (CacheKey × Expr)
  | [], acc => acc
  | n :: ns, acc => keysOfList ns (keysOf n acc)

end

/-- The slot list type `σ`. -/
def cacheTypes (slots : List (CacheKey × Expr)) : MetaM Expr :=
  mkListLit (mkSort Level.one) (slots.map (·.2))

/-- `Slot σ α` for the `i`-th slot. -/
def slotExpr : List Expr → Nat → MetaM Expr
  | [], _ => throwError "no such cache slot"
  | α :: rest, 0 => do mkAppOptM ``Slot.here #[some α, some (← mkListLit (mkSort Level.one) rest)]
  | β :: rest, i + 1 => do
    let inner ← slotExpr rest i
    let α := (← inferType inner).appArg!
    mkAppOptM ``Slot.there #[some α, some β, some (← mkListLit (mkSort Level.one) rest), some inner]

/-! ## Generating the solve -/

/-- `key : CacheKey`. -/
def keyExpr (k : CacheKey) : Expr :=
  mkApp3 (Lean.mkConst ``CacheKey.mk) (toExpr k.call) (strList k.scopes) (toExpr k.scope)

/-- `Option (String × SecurityScheme)`. -/
def schemeExpr : Option Expr → MetaM Expr
  | some e => mkAppM ``Option.some #[e]
  | none => do
    mkAppOptM ``Option.none #[some (← mkAppM ``Prod #[Lean.mkConst ``String, Lean.mkConst ``SecurityScheme])]

/-- The parameter product of a dependant's own parameters, in FastAPI's
order (path, query, header, cookie, body), with its type. -/
def paramsOf (ps : List (Source × Expr × Expr)) : MetaM (Expr × Expr) := do
  let sorted := ps.mergeSort (fun a b => a.1.rank ≤ b.1.rank)
  let mut e := Lean.mkConst ``LeanFastapi.Params.nil
  let mut β := Lean.mkConst ``Unit
  for (_, base, p) in sorted.reverse do
    e ← mkAppOptM ``LeanFastapi.Params.cons #[some base, some β, none, none, none, some p, some e]
    β ← mkAppM ``Prod #[base, β]
  return (e, β)

/-- **A dependant's solve** from its sub-dependencies' solves (`subs`,
with their value types, in order): those, then its own parameters, the
request and its scopes, as one `Dep σ β`; and, for a value `v : β`, the
argument values in declaration order. -/
def assembleArgs (σ : Expr) (args : List Node) (subs : List (Expr × Expr)) :
    MetaM (Expr × Expr × (Expr → MetaM (List Expr))) := do
  let ps := args.filterMap fun | .param s b p => some (s, b, p) | _ => none
  let scopes := (args.findSome? fun | .scopes s => some s | _ => none).getD []
  let mut comps : List (Expr × Expr) := subs
  let (psE, psTy) ← paramsOf ps
  comps := comps ++ [(← mkAppOptM ``Dep.params #[some σ, some psTy, some psE], psTy)]
  comps := comps ++ [(← mkAppOptM ``Dep.request #[some σ], Lean.mkConst ``LeanStarlette.Request)]
  comps := comps ++ [(← mkAppOptM ``Dep.scopes #[some σ, some (strList scopes)], Lean.mkConst ``SecurityScopes)]
  let mut dep ← mkAppOptM ``Dep.pure #[some σ, some (Lean.mkConst ``Unit), some (Lean.mkConst ``Unit.unit)]
  let mut β := Lean.mkConst ``Unit
  for (c, t) in comps.reverse do
    dep ← mkAppM ``Dep.both #[c, dep]
    β ← mkAppM ``Prod #[t, β]
  let nsubs := subs.length
  let sortedPs := ps.mergeSort (fun a b => a.1.rank ≤ b.1.rank)
  let project (v : Expr) : MetaM (List Expr) := do
    let mut out : List Expr := []
    let mut si := 0
    for n in args do
      match n with
      | .sub .. => out := out ++ [← projAt v si]; si := si + 1
      | .param _ _ p =>
        let k := (sortedPs.findIdx? (fun q => q.2.2 == p)).getD 0
        out := out ++ [← projAt (← projAt v nsubs) k]
      | .request => out := out ++ [← projAt v (nsubs + 1)]
      | .scopes _ => out := out ++ [← projAt v (nsubs + 2)]
    return out
  return (dep, β, project)

/-- A callable on its solved arguments, as an `Invoke` (its exit, for a
`yield` dependency, on the stack of `scope`), with the arguments' solve. -/
def invokeOf (σ α fn : Expr) (kind : Kind) (scope : String) (args : List Node) (subs : List (Expr × Expr)) :
    MetaM (Expr × Expr × Expr) := do
  let (argDep, β, project) ← assembleArgs σ args subs
  let lam ← withLocalDeclD `v β fun v => do
    let body := mkAppN fn (← project v).toArray
    let body ← match kind with
      | .pure => mkAppM ``handlerPure #[body]
      | _ => pure body
    mkLambdaFVars #[v] body
  let invoke ← match kind with
    | .yield =>
      let sc := if scope == "function" then Lean.mkConst ``DepScope.function else Lean.mkConst ``DepScope.request
      mkAppOptM ``Dep.Invoke.yield #[some β, some α, some sc, some lam]
    | _ => mkAppOptM ``Dep.Invoke.plain #[some β, some α, some lam]
  return (invoke, argDep, β)

mutual

/-- **A sub-dependency's solve**: `Dep.call` on its arguments' solve, with
the override's callable and arguments when one is in force. Structural on
the tree. -/
def genSub (σ : Expr) (slots : List (CacheKey × Expr)) : Node → MetaM Expr
  | .sub key α fn kind useCache scope own scheme args ovFn ovKind ovArgs => do
    let (invoke, argDep, β) ← invokeOf σ α fn kind scope args (← genSubs σ slots args)
    let ovSubs ← genSubs σ slots ovArgs
    let some idx := slots.findIdx? (·.1 == key) | throwError "no cache slot for {key.call}"
    let slot ← slotExpr (slots.map (·.2)) idx
    let ovTy ← mkAppM ``Dep.Override #[σ, α]
    let ov ← match ovFn with
      | none => mkAppOptM ``Option.none #[some ovTy]
      | some ofn => do
        let (oinv, oarg, oβ) ← invokeOf σ α ofn ovKind scope ovArgs ovSubs
        mkAppOptM ``Option.some #[some ovTy,
          ← mkAppOptM ``Dep.Override.mk #[some σ, some α, some oβ, some oinv, some oarg]]
    mkAppOptM ``Dep.call #[some σ, some α, some β, some (keyExpr key), some slot, some (toExpr useCache),
      some (strList own), some (← schemeExpr scheme), some invoke, some argDep, some ov]
  | _ => throwError "not a dependency"

/-- The solves of the sub-dependencies among `args`, in order, with their
value types. -/
def genSubs (σ : Expr) (slots : List (CacheKey × Expr)) : List Node → MetaM (List (Expr × Expr))
  | [] => pure []
  | n :: ns => do
    let rest ← genSubs σ slots ns
    match n with
    | .sub .. =>
      let d ← genSub σ slots n
      pure ((d, (← inferType d).appArg!) :: rest)
    | _ => pure rest

end

/-- **A dependant's solve**: its sub-dependencies, then its own parameters,
the request and its scopes (`assembleArgs`). -/
def genArgs (σ : Expr) (slots : List (CacheKey × Expr)) (args : List Node) :
    MetaM (Expr × Expr × (Expr → MetaM (List Expr))) := do
  assembleArgs σ args (← genSubs σ slots args)

/-! ## `Depends` and `Security` as terms -/

/-- **A dependency as a value** (`Dependency α`): the callable and the
mark, kept for `declared_routes`, and its cache key. -/
def dependencyValue (m : Mark) : MetaM Expr := do
  let node ← subOf maxDepth [] [] [] m
  let .sub key α .. := node | throwError "not a dependency"
  mkAppM ``Dependency.declared #[m.dependency, α, toExpr m.useCache, toExpr m.scope, strList m.own, keyExpr key]

/-- Read a `Dependency.declared` term (possibly erased) back as a mark and
its key. -/
def markOfDependency? (e : Expr) : MetaM (Option (Mark × Expr)) := do
  let e ← instantiateMVars e
  let e := if e.isAppOfArity ``Dependency.erase 2 then e.appArg! else e
  let e ← whnfCore e
  if e.isAppOfArity ``Dependency.declared 7 then
    let a := e.getAppArgs
    let useCache ← match (← whnfD a[3]!).constName? with
      | some ``Bool.false => pure false
      | _ => pure true
    let scope ← match ← whnfD a[4]! with
      | .lit (.strVal s) => pure s
      | _ => pure ""
    let own ← strsOf a[5]!
    return some ({ dependency := a[1]!, useCache, scope, own }, a[6]!)
  return none
where
  strsOf (e : Expr) : MetaM (List String) := do
    let some xs := listLit? e | throwError "scopes must be a list literal, not `{e}`"
    xs.mapM fun x => do
      match ← whnfD x with
      | .lit (.strVal s) => pure s
      | _ => throwError "a scope must be a string literal, not `{x}`"
  listLit? (e : Expr) : Option (List Expr) :=
    go 10000 e
  go : Nat → Expr → Option (List Expr)
    | 0, _ => none
    | n + 1, e =>
      if e.isAppOfArity ``List.nil 1 then some []
      else if e.isAppOfArity ``List.cons 3 then (go n e.appArg!).map (e.appFn!.appArg! :: ·)
      else none

/-- Elaborate `Depends ...` or `Security ...`: the type `DependsT x α ...`
in a type position, the `Dependency` elsewhere. -/
def elabMark (stx : Syntax) (expected? : Option Expr) : TermElabM Expr := do
  if let some t := expected? then
    if (← instantiateMVars t).isMVar then tryPostpone
  let m ← markOfSyntax stx
  let typeMode ← match expected? with
    | some t => do pure (← whnfR (← instantiateMVars t)).isSort
    | none => pure false
  if typeMode then
    let α ← valueType m.dependency
    if stx.getKind == ``securityStx then
      mkAppM ``SecurityT #[m.dependency, α, strList m.own, toExpr m.useCache]
    else mkAppM ``DependsT #[m.dependency, α, toExpr m.useCache, toExpr m.scope]
  else
    let d ← dependencyValue m
    -- an entry of `FastAPI(dependencies=[...])`: its value type forgotten
    match expected? with
    | some t =>
      if (← whnfR (← instantiateMVars t)).isConstOf ``AnyDependency then mkAppM ``Dependency.erase #[d]
      else pure d
    | none => pure d

@[term_elab dependsStx] def elabDepends : TermElab := elabMark

@[term_elab securityStx] def elabSecurity : TermElab := elabMark

end Macro

end LeanFastapi
