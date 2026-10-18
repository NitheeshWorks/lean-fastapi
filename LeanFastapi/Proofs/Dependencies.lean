import LeanFastapi.RepoImpl.Endpoint

/-!
# Proofs: solving dependencies

* `solve_order`: a dependant's parts are solved in order, each from the
  state the previous one left, so errors accumulate in declaration order,
  and a later part is solved even after an earlier one failed;
  `params_errors`: a dependant's parameters record exactly their
  extraction's errors;
* `cache_same_key`: a dependency whose key is cached is not called again;
  `cached_stores`: a computed value is cached under its key;
* `override_replaces`: with an override in force, the dependant gets the
  override's value (on the override's arguments), cached under the
  dependency's key;
* `cleanup_reverse`: exits run in the reverse of the order they were
  entered;
* `function_scope_not_outlive`: every function-scoped exit runs before any
  request-scoped one, and each runs once, whatever the outcome;
* `security_scopes_accumulate`: a scheme's requirement carries the scopes of
  the way to it, then its own, each once.

The solving monad sits on `IO`; its laws (`instLawfulMonadIO`) and the
run lemmas of `SolveM` below are all these proofs need.
-/

namespace LeanFastapi

open LeanStarlette (Exception Response)

/-- `IO`'s monad laws (its `bind` threads the world state and stops at an
error), so the laws of the transformers above it apply. -/
instance instLawfulMonadIO : LawfulMonad IO := LawfulMonad.mk'
  (id_map := fun x => by
    funext s
    show EST.bind x _ s = x s
    unfold EST.bind
    cases x s <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x f g => by
    funext s
    show EST.bind (EST.bind x f) g s = EST.bind x (fun a => EST.bind (f a) g) s
    unfold EST.bind
    cases x s <;> rfl)

variable {σ : List Type} {α β : Type}

/-! ## Running a solve -/

namespace SolveM

theorem runAt_bind (x : SolveM σ α) (f : α → SolveM σ β) (c : Ctx) (s : SolveState σ) :
    (x >>= f).runAt c s = x.runAt c s >>= fun p => match p with
      | (.ok a, s') => (f a).runAt c s'
      | (.error e, s') => pure (.error e, s') := by
  unfold SolveM.runAt
  simp only [bind, StateT.bind, ExceptT.bind, ReaderT.bind, ExceptT.mk, ExceptT.run, StateT.run, ExceptT.bindCont]
  congr 1
  funext p
  obtain ⟨r, s'⟩ := p
  cases r <;> rfl

theorem runAt_pure (a : α) (c : Ctx) (s : SolveState σ) : (pure a : SolveM σ α).runAt c s = pure (.ok a, s) := rfl

theorem runAt_get (c : Ctx) (s : SolveState σ) : (get : SolveM σ (SolveState σ)).runAt c s = pure (.ok s, s) := rfl

theorem runAt_read (c : Ctx) (s : SolveState σ) : (read : SolveM σ Ctx).runAt c s = pure (.ok c, s) := rfl

theorem runAt_modify (f : SolveState σ → SolveState σ) (c : Ctx) (s : SolveState σ) :
    (modify f : SolveM σ Unit).runAt c s = pure (.ok (), f s) := rfl

end SolveM

/-! ## Order -/

/-- **Parts are solved in order, each from the state the previous left**:
`b` runs from `a`'s final state (so its errors come after `a`'s) even when
`a` failed to validate (`x = none`). -/
theorem solve_order (a : Dep σ α) (b : Dep σ β) (c : Ctx) (s s₁ s₂ : SolveState σ) (x : Option α)
    (y : Option β) (ha : a.runAt c s = pure (.ok x, s₁)) (hb : b.runAt c s₁ = pure (.ok y, s₂)) :
    (Dep.both a b).runAt c s = pure (.ok (do Pure.pure (← x, ← y)), s₂) := by
  simp only [Dep.runAt, Dep.both, SolveM.runAt_bind] at ha hb ⊢
  rw [ha, pure_bind]
  simp only
  rw [hb, pure_bind]
  rfl

/-- **A dependant's parameters record exactly their extraction's errors**,
after those already recorded. -/
theorem params_errors (ps : Params α) (c : Ctx) (s : SolveState σ) (es : List RequestError)
    (h : ps.extract c.env.inputs = .error es) :
    (Dep.params ps).runAt c s =
      pure (.ok none, { s with shared := { s.shared with errors := s.shared.errors ++ es } }) := by
  simp only [Dep.runAt, Dep.params, SolveM.runAt_bind, SolveM.runAt_read, pure_bind, h, SolveM.report,
    SolveM.runAt_modify]
  rfl

/-! ## The cache -/

theorem Cache.get_set_same {σ : List Type} {α : Type} (c : Cache σ) (s : Slot σ α) (v : α) :
    (c.set s v).get s = some v := by
  induction s with
  | here => rfl
  | there s ih => simp only [Cache.set, Cache.get]; exact ih _ _

/-- **A cached key is not called again**: with a value under its slot, a
dependency (with `use_cache`) gives it and leaves the state as it was. -/
theorem cache_same_key (slot : Slot σ α) (compute : SolveM σ α) (c : Ctx) (s : SolveState σ) (v : α)
    (h : s.cache.get slot = some v) :
    (Dep.cached slot true compute).runAt c s = pure (.ok (some v), s) := by
  simp only [Dep.cached, SolveM.runAt_bind, SolveM.runAt_get, pure_bind, ite_true, h]
  rfl

/-- **A computed value is cached under its key** when the slot was empty, so
the next use of the key gets it (`cache_same_key`). -/
theorem cached_stores (slot : Slot σ α) (useCache : Bool) (compute : SolveM σ α) (c : Ctx)
    (s s₁ : SolveState σ) (v : α) (hs : s.cache.get slot = none) (hc : compute.runAt c s = pure (.ok v, s₁))
    (h₁ : s₁.cache.get slot = none) :
    (Dep.cached slot useCache compute).runAt c s = pure (.ok (some v), { s₁ with cache := s₁.cache.set slot v }) := by
  have hn : (if useCache = true then s.cache.get slot else none) = none := by cases useCache <;> simp [hs]
  simp only [Dep.cached, SolveM.runAt_bind, SolveM.runAt_get, pure_bind, hn]
  rw [hc, pure_bind]
  simp only [SolveM.runAt_modify, pure_bind, SolveM.runAt_pure, Cache.fill, h₁]

/-! ## Overrides -/

/-- With an override in force, a dependency is solved exactly as the
override on its own arguments would be, under the dependency's own key, cache
use and scope. -/
theorem call_override {β' : Type} (key : CacheKey) (slot : Slot σ α) (useCache : Bool) (own : List String)
    (scheme : Option (String × SecurityScheme)) (f : Dep.Invoke β α) (arg : Dep σ β)
    (g : Dep.Invoke β' α) (arg' : Dep σ β') :
    (Dep.call key slot useCache own scheme f arg (some ⟨g, arg'⟩)).run =
      (Dep.call key slot useCache own scheme g arg').run := rfl

/-- **An override replaces the dependency, and the dependant gets the
override's value**: when the override's arguments solve to `b` and the
override, called on `b`, returns `v` (from an empty slot), the dependency's
value is `v`, cached under the dependency's key. The dependency's own
function and arguments play no part. -/
theorem override_replaces {β' : Type} (key : CacheKey) (slot : Slot σ α) (useCache : Bool) (own : List String)
    (scheme : Option (String × SecurityScheme)) (f : Dep.Invoke β α) (arg : Dep σ β)
    (g : Dep.Invoke β' α) (arg' : Dep σ β') (c : Ctx) (s s₁ s₂ : SolveState σ) (b : β') (v : α)
    (ha : arg'.runAt c s = pure (.ok (some b), s₁)) (hs : s₁.cache.get slot = none)
    (hg : (g.call b).runAt c s₁ = pure (.ok v, s₂)) (h₂ : s₂.cache.get slot = none) :
    (Dep.call key slot useCache own scheme f arg (some ⟨g, arg'⟩)).runAt c s =
      pure (.ok (some v), { s₂ with cache := s₂.cache.set slot v }) := by
  simp only [Dep.runAt, Dep.call, Dep.Override.pick, Option.getD, Dep.Override.solve, SolveM.runAt_bind] at ha ⊢
  rw [ha, pure_bind]
  exact cached_stores slot useCache (g.call b) c s₁ s₂ v hs hg h₂

/-! ## Exit stacks -/

/-- What unwinding gives, when exit `x` answers `r x e`. -/
def closeResult {ε : Type} (r : ε → Option Exception → Except Exception Unit) : List ε → Option Exception →
    Option Exception
  | [], e => e
  | x :: xs, e =>
    match r x e with
    | .ok () => closeResult r xs none
    | .error e' => closeResult r xs (some e')

/-- Unwinding a stack runs its exits in stack order, each once. -/
theorem closeWith_run {ε : Type} (r : ε → Option Exception → Except Exception Unit) (xs : List ε)
    (e : Option Exception) (t : List ε) :
    (closeWith (tracedRun r) xs e).run t = ((closeResult r xs e, t ++ xs) : Option Exception × List ε) := by
  induction xs generalizing e t with
  | nil => simp [closeWith, closeResult]; rfl
  | cons x xs ih =>
    simp only [closeWith, closeResult, tracedRun, StateT.run_bind, StateT.run_modify, StateT.run_pure]
    show (match r x e with
      | .ok () => closeWith (tracedRun r) xs none
      | .error e' => closeWith (tracedRun r) xs (some e')).run (t ++ [x]) = _
    split <;> simp [ih]

/-- Entering exits pushes them: the stack is the entered ones, most recent
first, on top of the older ones. -/
theorem push_request (sh : Shared) (xs : List Exit) :
    (xs.foldl (fun sh x => sh.push .request x) sh).request = xs.reverse ++ sh.request := by
  induction xs generalizing sh with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl]; rw [ih]; simp [Shared.push]

/-- **Exits run in the reverse of the order they were entered**, then the
older ones. -/
theorem cleanup_reverse (r : Exit → Option Exception → Except Exception Unit) (sh : Shared) (xs : List Exit)
    (e : Option Exception) :
    ((closeWith (tracedRun r) (xs.foldl (fun sh x => sh.push .request x) sh).request e).run []).2 =
      xs.reverse ++ sh.request := by
  rw [closeWith_run, push_request, List.nil_append]

/-- **Function-scoped exits do not outlive the function**: whatever the
outcome and whatever each exit does, every function-scoped exit runs (in
stack order) before any request-scoped one, and each runs once. -/
theorem function_scope_not_outlive {ε : Type} (r : ε → Option Exception → Except Exception Unit)
    (outcome : Except Exception Response) (function request : List ε) :
    ((finishWith (tracedRun r) outcome function request).run []).2 = function ++ request := by
  unfold finishWith
  rw [StateT.run_bind, closeWith_run]
  have idBind : ∀ {α β : Type} (x : Id α) (f : α → Id β), x >>= f = f x := fun _ _ => rfl
  rcases outcome with ex | resp <;> cases closeResult r function _ <;>
    simp only [idBind, List.nil_append, StateT.run_bind, closeWith_run] <;>
    first
    | rfl
    | (cases closeResult r request _ <;> rfl)

/-! ## Scopes -/

/-- `mergeScopes a b`: the scopes of `a`, then those of `b` not yet there. -/
theorem mergeScopes_mem (a b : List String) (s : String) : s ∈ mergeScopes a b ↔ s ∈ a ∨ s ∈ b := by
  induction b generalizing a with
  | nil => simp [mergeScopes]
  | cons x xs ih =>
    simp only [mergeScopes, List.foldl] at ih ⊢
    rw [ih]
    have step : s ∈ (if a.contains x = true then a else a ++ [x]) ↔ s ∈ a ∨ s = x := by
      split
      · rename_i hx
        have : x ∈ a := by simpa using hx
        constructor
        · exact Or.inl
        · rintro (h | rfl) <;> assumption
      · simp
    rw [step]
    simp only [List.mem_cons, or_assoc]

mutual

theorem FlatDeps.node_prefix (scopes : List String) (d : DepInfo) (w : FlatDeps) :
    w.security <+: (FlatDeps.node scopes d w).security := by
  match d with
  | .param _ => exact List.prefix_refl _
  | .sub key own scheme args =>
    unfold FlatDeps.node
    split
    · exact List.prefix_refl _
    · dsimp only
      apply List.IsPrefix.trans _ (FlatDeps.list_prefix _ args _)
      exact List.prefix_append _ _

theorem FlatDeps.list_prefix (scopes : List String) (ds : List DepInfo) (w : FlatDeps) :
    w.security <+: (FlatDeps.list scopes ds w).security := by
  match ds with
  | [] => exact List.prefix_refl _
  | d :: ds =>
    unfold FlatDeps.list
    exact (FlatDeps.node_prefix scopes d w).trans (FlatDeps.list_prefix scopes ds _)

end

/-- **Scopes accumulate along the way to a scheme**: its requirement is the
scopes of the way to it, then its own, each once (`mergeScopes_mem`). -/
theorem security_scopes_accumulate (scopes own : List String) (key : CacheKey) (n : String) (m : SecurityScheme)
    (args : List DepInfo) (w : FlatDeps) (h : key ∉ w.visited) :
    (n, m, mergeScopes scopes own) ∈ (FlatDeps.node scopes (.sub key own (some (n, m)) args) w).security := by
  unfold FlatDeps.node
  cases hc : w.visited.contains key
  · simp only [Bool.false_eq_true, ite_false]
    exact (FlatDeps.list_prefix _ args _).subset (by simp)
  · exact absurd (by simpa using hc) h

end LeanFastapi
