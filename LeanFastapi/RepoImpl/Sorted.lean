/-!
# RepoImpl: association lists sorted by key

`components.schemas` is sorted by name (`{k: definitions[k] for k in
sorted(definitions)}`), and a name given twice keeps its last definition
(`definitions.update`). `insertSorted` is that `update` on a strictly sorted
list, and `ofListSorted` folds it over a list. The invariant they keep,
`(l.map Prod.fst).Pairwise (· < ·)`, is what `Components.sorted` stores, so
the lemmas that preserve it live here, next to the definitions.
-/

namespace LeanFastapi

namespace Sorted

variable {β : Type}

/-- Insert `(k, v)` into a list sorted by key, replacing the entry for `k`. -/
def insertSorted (kv : String × β) : List (String × β) → List (String × β)
  | [] => [kv]
  | x :: xs =>
    if kv.1 < x.1 then kv :: x :: xs
    else if kv.1 = x.1 then kv :: xs
    else x :: insertSorted kv xs

/-- Insert every entry, in order: later entries replace earlier ones. -/
def ofListSorted (l : List (String × β)) : List (String × β) :=
  l.foldl (fun acc kv => insertSorted kv acc) []

theorem mem_keys_insertSorted (kv : String × β) (l : List (String × β)) (k : String) :
    k ∈ (insertSorted kv l).map Prod.fst ↔ k = kv.1 ∨ k ∈ l.map Prod.fst := by
  induction l with
  | nil => simp [insertSorted]
  | cons x xs ih =>
    unfold insertSorted
    split
    · simp
    · split
      · rename_i h; simp [h]
      · simp only [List.map_cons, List.mem_cons, ih]
        constructor
        · rintro (h | h | h) <;> simp [h]
        · rintro (h | h | h) <;> simp [h]

theorem insertSorted_sorted (kv : String × β) (l : List (String × β))
    (h : (l.map Prod.fst).Pairwise (· < ·)) : ((insertSorted kv l).map Prod.fst).Pairwise (· < ·) := by
  induction l with
  | nil => simp [insertSorted]
  | cons x xs ih =>
    simp only [List.map_cons, List.pairwise_cons] at h
    unfold insertSorted
    split
    · rename_i hlt
      simp only [List.map_cons, List.pairwise_cons, List.mem_cons]
      refine ⟨?_, h.1, h.2⟩
      rintro b (rfl | hb)
      · exact hlt
      · exact String.lt_trans hlt (h.1 b hb)
    · split
      · rename_i _ heq
        simp only [List.map_cons, List.pairwise_cons]
        exact ⟨fun b hb => heq ▸ h.1 b hb, h.2⟩
      · rename_i hlt hne
        simp only [List.map_cons, List.pairwise_cons]
        refine ⟨?_, ih h.2⟩
        intro b hb
        rcases (mem_keys_insertSorted kv xs b).1 hb with rfl | hb
        · rcases Std.lt_trichotomy x.1 kv.1 with h' | h' | h'
          · exact h'
          · exact absurd h'.symm hne
          · exact absurd h' hlt
        · exact h.1 b hb

theorem ofListSorted_sorted (l : List (String × β)) :
    ((ofListSorted l).map Prod.fst).Pairwise (· < ·) := by
  unfold ofListSorted
  suffices ∀ acc : List (String × β), (acc.map Prod.fst).Pairwise (· < ·) →
      ((l.foldl (fun acc kv => insertSorted kv acc) acc).map Prod.fst).Pairwise (· < ·) from
    this [] (by simp)
  induction l with
  | nil => intro acc h; exact h
  | cons kv l ih => intro acc h; exact ih _ (insertSorted_sorted kv acc h)

theorem mem_insertSorted (kv : String × β) (l : List (String × β)) (y : String × β) :
    y ∈ insertSorted kv l → y = kv ∨ y ∈ l := by
  induction l with
  | nil => simp [insertSorted]
  | cons x xs ih =>
    unfold insertSorted
    split
    · simp only [List.mem_cons]; rintro (h | h | h) <;> simp [h]
    · split
      · simp only [List.mem_cons]; rintro (h | h) <;> simp [h]
      · simp only [List.mem_cons]
        rintro (h | h)
        · exact .inr (.inl h)
        · rcases ih h with h | h
          · exact .inl h
          · exact .inr (.inr h)

/-- Every entry of `ofListSorted l` is an entry of `l`. -/
theorem mem_ofListSorted (l : List (String × β)) (y : String × β) :
    y ∈ ofListSorted l → y ∈ l := by
  unfold ofListSorted
  suffices ∀ acc : List (String × β), y ∈ l.foldl (fun acc kv => insertSorted kv acc) acc → y ∈ acc ∨ y ∈ l from
    fun h => (this [] h).elim (by simp) id
  induction l with
  | nil => intro acc h; exact .inl h
  | cons kv l ih =>
    intro acc h
    rcases ih _ h with h | h
    · rcases mem_insertSorted kv acc y h with h | h
      · exact .inr (h ▸ List.mem_cons_self)
      · exact .inl h
    · exact .inr (List.mem_cons_of_mem _ h)

/-- The keys of `ofListSorted l` are the keys of `l`. -/
theorem mem_keys_ofListSorted (l : List (String × β)) (k : String) :
    k ∈ (ofListSorted l).map Prod.fst ↔ k ∈ l.map Prod.fst := by
  unfold ofListSorted
  suffices ∀ acc : List (String × β),
      k ∈ (l.foldl (fun acc kv => insertSorted kv acc) acc).map Prod.fst ↔
        k ∈ acc.map Prod.fst ∨ k ∈ l.map Prod.fst from by simpa using this []
  induction l with
  | nil => intro acc; simp
  | cons kv l ih =>
    intro acc
    rw [List.foldl_cons, ih, mem_keys_insertSorted]
    simp only [List.map_cons, List.mem_cons]
    constructor
    · rintro ((h | h) | h) <;> simp [h]
    · rintro (h | h | h) <;> simp [h]

end Sorted

end LeanFastapi
