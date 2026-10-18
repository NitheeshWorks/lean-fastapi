import LeanFastapi.DataTypes.Dependencies
import LeanFastapi.RepoImpl.Exceptions

/-!
# RepoImpl: solving dependencies

`fastapi.dependencies.utils.solve_dependencies`, as a small set of
combinators over one solving monad.

* A **dependency** `Dep σ α` computes an `α` from a request, or records
  validation errors. It is built (by the path operation macro) from the
  dependant's parts: its parameters (`Dep.params`), the request
  (`Dep.request`), its `SecurityScopes` (`Dep.scopes`), its sub-dependencies
  (`Dep.call`, `Dep.yield_`), put side by side with `Dep.both`.
* `Dep.both a b` solves `a`, then `b`, **even when `a` failed**: FastAPI
  solves every sub-dependency and every parameter and reports all errors
  together, sub-dependencies first in declaration order, then the
  dependant's own parameters (path, query, header, cookie, body).
* `Dep.call key slot f arg` solves the arguments, then (when they had no
  errors) takes the value cached under `key` for this request, or calls `f`
  and caches the result. The cache is typed: the macro gives every distinct
  `CacheKey` of a route a slot `Slot σ α` in a heterogeneous list `Cache σ`,
  so a cached value comes back at its own type.
* A **`yield` dependency** returns its value with an `Exit`: the code after
  `yield`, which receives the exception in flight (or none) and either
  re-raises, raises another, or returns, which suppresses it. Exits go on
  the function or request **exit stack** (`DepScope`), and stacks unwind in
  reverse order (`closeExits`).
* `dependency_overrides`: `Dep.call` takes the override in force for the
  dependency, if any (an `Override σ α`: another callable of the same value
  type with its own arguments). The override's arguments are solved and the
  override is called; the dependency's cache key, cache use and scope stay
  the original's, as in `solve_dependencies`, and OpenAPI still describes
  the original. Which override applies is settled when the application's
  routes are compiled (`declared_routes`), so it is typed: an override of
  another value type does not compile.

Errors and exit stacks live in `Shared`; the cache in `SolveState`. A
dependency raising an exception (an `HTTPException`) stops the solve, and
the exits already entered still run with that exception.
-/

namespace LeanFastapi

open LeanJson (Json)
open LeanPydantic (FromJson ToJson)
open LeanStarlette (Request Response Exception AppM)

/-- The monad of path operation and dependency functions. -/
abbrev Handler (α : Type) : Type := AppM α

/-! ## The typed cache -/

/-- A position in a list of types holding an `α`: `here` is the head,
`there` one further. -/
inductive Slot : List Type → Type → Type 1 where
  | here {α : Type} {σ : List Type} : Slot (α :: σ) α
  | there {α β : Type} {σ : List Type} : Slot σ α → Slot (β :: σ) α

/-- One optional value per slot type. A function into `Type` (not an
inductive family over `List Type`, which would live in `Type 1`), so a cache
can be the state of an `IO` computation. -/
def Cache : List Type → Type
  | [] => Unit
  | α :: σ => Option α × Cache σ

namespace Cache

/-- The empty cache. -/
def empty : (σ : List Type) → Cache σ
  | [] => ()
  | _ :: σ => (none, empty σ)

/-- The value in a slot. -/
def get : {σ : List Type} → {α : Type} → Cache σ → Slot σ α → Option α
  | _ :: _, _, c, .here => c.1
  | _ :: _, _, c, .there s => get c.2 s

/-- The cache with a value in a slot. -/
def set : {σ : List Type} → {α : Type} → Cache σ → Slot σ α → α → Cache σ
  | _ :: _, _, c, .here, v => (some v, c.2)
  | _ :: _, _, c, .there s, v => (c.1, set c.2 s v)

/-- The cache with a value in a slot, unless one is there already
(`if key not in dependency_cache: dependency_cache[key] = solved`). -/
def fill {σ : List Type} {α : Type} (c : Cache σ) (s : Slot σ α) (v : α) : Cache σ :=
  match c.get s with
  | some _ => c
  | none => c.set s v

end Cache

/-! ## Exits and `yield` dependencies -/

/-- The code after a `yield`: it receives the exception raised meanwhile, if
any. Raising (the same exception or another) propagates; returning normally
suppresses it. -/
abbrev Exit := Option Exception → Handler Unit

/-- What a `yield` dependency gives: its value and its exit. -/
abbrev Yielded (α : Type) : Type := α × Exit

/-- `Yield α`: a `yield` dependency of value `α`, setup code in `Handler`
ending in `yieldWith value exit`. -/
macro "Yield " α:term:max : term => `(Handler (Yielded $α))

/-- `yield value`, with what runs after it (`exit` gets the exception in
flight, or `none`). -/
def yieldWith {α : Type} (value : α) (exit : Exit := fun _ => pure ()) : Yield α :=
  pure (value, exit)

/-- `try: yield value finally: cleanup`: the cleanup runs, then the
exception in flight (if any) propagates. -/
def yieldFinally {α : Type} (value : α) (cleanup : Handler Unit) : Yield α :=
  yieldWith value fun e => do
    cleanup
    match e with
    | some e => throw e
    | none => pure ()

/-- Unwind an exit stack, most recent first, threading the exception: each
exit receives the current one; one that returns normally clears it, one that
raises replaces it (`AsyncExitStack.__aexit__`). Generic in the monad and in
how an exit is run, so its order can be observed (`Proofs/Dependencies`). -/
def closeWith {m : Type → Type} [Monad m] {ε : Type} (run : ε → Option Exception → m (Except Exception Unit)) :
    List ε → Option Exception → m (Option Exception)
  | [], e => pure e
  | x :: xs, e => do
    match ← run x e with
    | .ok () => closeWith run xs none
    | .error e' => closeWith run xs (some e')

/-- Run an exit with the exception in flight. -/
def runExit (x : Exit) (e : Option Exception) : IO (Except Exception Unit) := (x e).run

/-- A runner that records the order exits run in, each answering as `r`
says: what the ordering theorems observe `closeWith` and `finishWith` with. -/
def tracedRun {ε : Type} (r : ε → Option Exception → Except Exception Unit) (x : ε) (e : Option Exception) :
    StateM (List ε) (Except Exception Unit) := do
  modify (· ++ [x])
  pure (r x e)

/-- Unwind a stack of exits. -/
def closeExits : List Exit → Option Exception → IO (Option Exception) := closeWith runExit

/-! ## The solving monad -/

/-- What a solve accumulates whatever its slots: the validation errors in
order, and the two exit stacks (most recent first). -/
structure Shared where
  errors : List RequestError := []
  function : List Exit := []
  request : List Exit := []

/-- An exit entered: on top of the stack of its scope. -/
def Shared.push (sh : Shared) (scope : DepScope) (x : Exit) : Shared :=
  match scope with
  | .function => { sh with function := x :: sh.function }
  | .request => { sh with request := x :: sh.request }

/-- The request and its parsed inputs. -/
structure Env where
  request : Request
  inputs : Inputs

/-- What a route's solve reads: the request and its inputs. -/
structure Ctx where
  env : Env

/-- A solve's state: what is shared, and the typed cache. -/
structure SolveState (σ : List Type) where
  shared : Shared
  cache : Cache σ

/-- The solving monad. Exceptions sit inside the state, so the exit stacks
entered before an exception are still there to unwind. -/
abbrev SolveM (σ : List Type) := ReaderT Ctx (ExceptT Exception (StateT (SolveState σ) IO))

namespace SolveM

variable {σ : List Type}

/-- Run a solve from a state. -/
def runAt {α : Type} (x : SolveM σ α) (c : Ctx) (s : SolveState σ) : IO (Except Exception α × SolveState σ) :=
  ((x c).run).run s

/-- Run a `Handler` computation. -/
def lift {α : Type} (m : Handler α) : SolveM σ α := fun _ => ExceptT.mk (liftM (m.run))

/-- Record validation errors. -/
def report (es : List RequestError) : SolveM σ Unit :=
  modify fun s => { s with shared := { s.shared with errors := s.shared.errors ++ es } }

/-- Push an exit on the stack of its scope. -/
def pushExit (scope : DepScope) (x : Exit) : SolveM σ Unit :=
  modify fun s => { s with shared := s.shared.push scope x }

end SolveM

/-! ## Dependencies -/

/-- A dependency of value `α` in a route whose cache has slots `σ`: its tree
as OpenAPI sees it, and its solve, which gives the value or `none` after
recording errors. -/
structure Dep (σ : List Type) (α : Type) where
  info : List DepInfo
  run : SolveM σ (Option α)

namespace Dep

variable {σ : List Type} {α β : Type}

/-- Solve it from a state. -/
abbrev runAt (d : Dep σ α) (c : Ctx) (s : SolveState σ) : IO (Except Exception (Option α) × SolveState σ) :=
  d.run.runAt c s

/-- A constant. -/
def pure (a : α) : Dep σ α := ⟨[], Pure.pure (some a)⟩

/-- The dependant's own parameters: all validated, every error recorded. -/
def params (ps : Params α) : Dep σ α where
  info := ps.infos.map DepInfo.param
  run := do
    match ps.extract (← read).env.inputs with
    | .ok v => Pure.pure (some v)
    | .error es => do SolveM.report es; Pure.pure none

/-- The request itself (a `Request` argument). -/
def request : Dep σ Request := ⟨[], do Pure.pure (some (← read).env.request)⟩

/-- The `SecurityScopes` argument: the scopes required on the way here. -/
def scopes (s : List String) : Dep σ SecurityScopes := ⟨[], Pure.pure (some { scopes := s })⟩

/-- Two parts of a dependant, solved in order, the second even when the
first failed. -/
def both (a : Dep σ α) (b : Dep σ β) : Dep σ (α × β) where
  info := a.info ++ b.info
  run := do
    let x ← a.run
    let y ← b.run
    Pure.pure (do Pure.pure (← x, ← y))

/-- How a sub-dependency is invoked: a plain function, or a `yield`
dependency whose exit goes on the stack of its scope. -/
inductive Invoke (β α : Type) where
  | plain (f : β → Handler α)
  | yield (scope : DepScope) (f : β → Yield α)

/-- Call it on its arguments, pushing a `yield` dependency's exit. -/
def Invoke.call {σ : List Type} {β α : Type} : Invoke β α → β → SolveM σ α
  | .plain f, b => SolveM.lift (f b)
  | .yield scope f, b => do
    let (a, x) ← SolveM.lift (f b)
    SolveM.pushExit scope x
    Pure.pure a

/-- The value for `key`: cached (when `useCache`) or computed, then cached
unless something is there already. -/
def cached (slot : Slot σ α) (useCache : Bool) (compute : SolveM σ α) : SolveM σ (Option α) := do
  let st ← get
  match (if useCache then st.cache.get slot else none) with
  | some v => Pure.pure (some v)
  | none => do
    let v ← compute
    modify fun s => { s with cache := s.cache.fill slot v }
    Pure.pure (some v)

/-- An override in force for a dependency of value `α`: another callable,
with its own arguments (`dependency_overrides[original] = override`). -/
structure Override (σ : List Type) (α : Type) where
  {β : Type}
  invoke : Invoke β α
  arg : Dep σ β

/-- Solve the arguments, then (when they had no errors) take the cached
value or call. -/
def Override.solve (o : Override σ α) (slot : Slot σ α) (useCache : Bool) : SolveM σ (Option α) := do
  match ← o.arg.run with
  | none => Pure.pure none
  | some b => cached slot useCache (o.invoke.call b)

/-- The callable and arguments a sub-dependency solves: the override's when
there is one, else its own. -/
def Override.pick (ov : Option (Override σ α)) (f : Invoke β α) (arg : Dep σ β) : Override σ α :=
  ov.getD ⟨f, arg⟩

/-- **A sub-dependency** (`Depends(f)`), with the override in force for it
(`ov`): the arguments of the override (or, without one, its own `arg`) are
solved, then (when they had no errors) the value cached under `key` is
reused (when `useCache`) or the override (or `f`) is called and its value
cached. The cache key, cache use and exit scope are the original
dependency's, and so is what OpenAPI sees (`info`). -/
def call (key : CacheKey) (slot : Slot σ α) (useCache : Bool) (ownScopes : List String)
    (scheme : Option (String × SecurityScheme)) (f : Invoke β α) (arg : Dep σ β)
    (ov : Option (Override σ α) := none) : Dep σ α where
  info := [.sub key ownScopes scheme arg.info]
  run := (Override.pick ov f arg).solve slot useCache

end Dep

/-! ## Dependencies as values -/

/-- `Depends(f)` as a value (in `FastAPI(dependencies=[...])` or
`app.dependency_overrides[f] = g`): a dependency of value `α`. The callable
itself is read when the application's routes are compiled; at run time the
value is its cache key. -/
structure Dependency (α : Type) where
  key : CacheKey
  deriving Inhabited

/-- `Depends(f)` with its value type forgotten: an entry of
`FastAPI(dependencies=[...])`. -/
structure AnyDependency where
  key : CacheKey
  deriving Inhabited

/-- Forget the value type. -/
def Dependency.erase {α : Type} (d : Dependency α) : AnyDependency := ⟨d.key⟩

instance {α : Type} : CoeOut (Dependency α) AnyDependency := ⟨Dependency.erase⟩

/-- What `Depends dependency (use_cache := ...) (scope := ...)` and
`Security dependency [scopes]` elaborate to as values: the callable and the
mark's arguments, kept in the term so that `declared_routes` can read them. -/
def Dependency.declared.{u} {δ : Sort u} (_dependency : δ) (α : Type) (_use_cache : Bool) (_scope : String)
    (_scopes : List String) (key : CacheKey) : Dependency α := ⟨key⟩

/-! ## Running a path operation inside its exit stacks -/

/-- `FastAPIError("Response not awaited...")`: an exit suppressed the
exception of a failed request, so there is no response. -/
def responseNotAwaited : Exception :=
  .custom "FastAPIError" ("Response not awaited. There's a high chance that the application code is raising " ++
    "an exception and a dependency with yield has a block with a bare except, or a block with except " ++
    "Exception, and is not raising the exception again.") .null

/-- The `UnboundLocalError` of reading the response a suppressed exception
never produced. -/
def responseUnbound : Exception :=
  .custom "UnboundLocalError" "cannot access local variable 'response' where it is not associated with a value" .null

/-- **The two exit stacks** (`request_response` in `fastapi/routing.py`):
the path operation's outcome unwinds the function-scoped exits; a response
then goes out and the request-scoped exits run after it (their exceptions
come too late to change it, and go to `late`, as the server logs them); an
exception unwinds the request-scoped exits too, and one they all suppress
leaves no response (both are 500s). -/
def finishWith {m : Type → Type} [Monad m] {ε : Type} (run : ε → Option Exception → m (Except Exception Unit))
    (outcome : Except Exception Response) (function request : List ε)
    (late : Exception → m Unit := fun _ => pure ()) : m (Except Exception Response) := do
  let e ← closeWith run function (match outcome with | .ok _ => none | .error e => some e)
  match outcome, e with
  | .ok r, none => do
    match ← closeWith run request none with
    | some e' => late e'
    | none => pure ()
    pure (.ok r)
  | _, some e => do
    match ← closeWith run request (some e) with
    | some e' => pure (.error e')
    | none => pure (.error responseNotAwaited)
  | .error _, none => do
    -- the function-scoped exits suppressed it: Python then reads the
    -- unbound `response`, and that error unwinds the request exits
    match ← closeWith run request (some responseUnbound) with
    | some e' => pure (.error e')
    | none => pure (.error responseNotAwaited)

/-- How the server reports an exception raised after the response was sent
(uvicorn logs it with `Exception in ASGI application` on standard error). -/
def logLate (e : Exception) : IO Unit :=
  IO.eprintln s!"Exception in ASGI application\n{e}"

/-- `finishWith` on a request's exit stacks; a request-scoped exit's
exception after the response is written to standard error. -/
def finish (outcome : Except Exception Response) (sh : Shared) : AppM Response :=
  ExceptT.mk (finishWith runExit outcome sh.function sh.request logLate)

end LeanFastapi
