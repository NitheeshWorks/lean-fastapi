import LeanFastapi.RepoImpl.OpenApi

/-!
# Proofs: references in schemas resolve to the schema's models

The general fact behind `openapi_refs_resolve`: turning a pydantic schema
into a document schema (`OSchema.ofSchema`) only refers to models that
`OSchema.models` collects from it (`refs_ofSchema`), and the collected models
only refer to each other (`models_closed`). Both are proved once, by
structural induction over pydantic's `Schema`, for every schema.
-/

namespace LeanFastapi

open LeanPydantic (Schema)

namespace OSchema

/-- The names of a list of components. -/
abbrev names (l : List (String × OSchema)) : List String := l.map Prod.fst

mutual
/-- **A document schema refers only to models of its pydantic schema.** -/
theorem refs_ofSchema : ∀ (s : Schema), ∀ n ∈ (ofSchema s).refs, n ∈ names (models s)
  | .any, n, h => by simp [ofSchema, refs] at h
  | .null, n, h => by simp [ofSchema, refs] at h
  | .boolean, n, h => by simp [ofSchema, refs] at h
  | .integer _, n, h => by simp [ofSchema, refs] at h
  | .number _, n, h => by simp [ofSchema, refs] at h
  | .string _, n, h => by simp [ofSchema, refs] at h
  | .literal _, n, h => by simp [ofSchema, refs] at h
  | .array i _, n, h => by
    simp only [ofSchema, refs, models] at h ⊢
    exact refs_ofSchema i n h
  | .tuple ps, n, h => by
    simp only [ofSchema, refs, models] at h ⊢
    exact refsList_ofSchemas ps n h
  | .dict v, n, h => by
    simp only [ofSchema, refs, models] at h ⊢
    exact refs_ofSchema v n h
  | .anyOf alts, n, h => by
    simp only [ofSchema, refs, models] at h ⊢
    exact refsList_ofSchemas alts n h
  | .object t _ _, n, h => by
    simp only [ofSchema, refs, List.mem_singleton] at h
    subst h; simp [models]
  | .ref t _, n, h => by
    simp only [ofSchema, refs, List.mem_singleton] at h
    subst h; simp [models]
  | .annotated s _ _, n, h => by
    simp only [ofSchema, refs, models] at h ⊢
    exact refs_ofSchema s n h

theorem refsList_ofSchemas : ∀ (ss : List Schema), ∀ n ∈ refsList (ofSchemas ss), n ∈ names (modelsList ss)
  | [], n, h => by simp [ofSchemas, refsList] at h
  | s :: ss, n, h => by
    simp only [ofSchemas, refsList, modelsList, List.mem_append, names, List.map_append] at h ⊢
    rcases h with h | h
    · exact .inl (refs_ofSchema s n h)
    · exact .inr (refsList_ofSchemas ss n h)

theorem refsProps_ofProps : ∀ (ps : List (String × Schema)), ∀ n ∈ refsProps (ofProps ps), n ∈ names (modelsProps ps)
  | [], n, h => by simp [ofProps, refsProps] at h
  | (_, s) :: ps, n, h => by
    simp only [ofProps, refsProps, modelsProps, List.mem_append, names, List.map_append] at h ⊢
    rcases h with h | h
    · exact .inl (refs_ofSchema s n h)
    · exact .inr (refsProps_ofProps ps n h)
end

/-- A named schema's component refers only to the schema's models. -/
theorem refs_body (t : Schema) : ∀ n ∈ (body t).refs, n ∈ names (models t) := by
  cases t with
  | object t props req =>
    intro n hn
    simp only [body, refs] at hn
    simp only [models, names, List.map_cons, List.mem_cons]
    exact .inr (refsProps_ofProps props n hn)
  | _ => exact refs_ofSchema _

mutual
/-- **The models of a schema refer only to each other.** -/
theorem models_closed : ∀ (s : Schema), ∀ c ∈ models s, ∀ n ∈ c.2.refs, n ∈ names (models s)
  | .any, c, hc, _, _ => by simp [models] at hc
  | .null, c, hc, _, _ => by simp [models] at hc
  | .boolean, c, hc, _, _ => by simp [models] at hc
  | .integer _, c, hc, _, _ => by simp [models] at hc
  | .number _, c, hc, _, _ => by simp [models] at hc
  | .string _, c, hc, _, _ => by simp [models] at hc
  | .literal _, c, hc, _, _ => by simp [models] at hc
  | .array i _, c, hc, n, hn => by
    simp only [models] at hc ⊢
    exact models_closed i c hc n hn
  | .tuple ps, c, hc, n, hn => by
    simp only [models] at hc ⊢
    exact modelsList_closed ps c hc n hn
  | .dict v, c, hc, n, hn => by
    simp only [models] at hc ⊢
    exact models_closed v c hc n hn
  | .ref t s, c, hc, n, hn => by
    simp only [models, List.mem_cons] at hc
    simp only [models, names, List.map_cons, List.mem_cons]
    rcases hc with rfl | hc
    · exact .inr (refs_body s n hn)
    · exact .inr (models_closed s c hc n hn)
  | .anyOf alts, c, hc, n, hn => by
    simp only [models] at hc ⊢
    exact modelsList_closed alts c hc n hn
  | .object t props req, c, hc, n, hn => by
    simp only [models, List.mem_cons] at hc
    simp only [models, names, List.map_cons, List.mem_cons]
    rcases hc with rfl | hc
    · simp only [refs] at hn
      exact .inr (refsProps_ofProps props n hn)
    · exact .inr (modelsProps_closed props c hc n hn)
  | .annotated s _ _, c, hc, n, hn => by
    simp only [models] at hc ⊢
    exact models_closed s c hc n hn

theorem modelsList_closed : ∀ (ss : List Schema), ∀ c ∈ modelsList ss, ∀ n ∈ c.2.refs, n ∈ names (modelsList ss)
  | [], c, hc, _, _ => by simp [modelsList] at hc
  | s :: ss, c, hc, n, hn => by
    simp only [modelsList, List.mem_append, names, List.map_append] at hc ⊢
    rcases hc with hc | hc
    · exact .inl (models_closed s c hc n hn)
    · exact .inr (modelsList_closed ss c hc n hn)

theorem modelsProps_closed : ∀ (ps : List (String × Schema)), ∀ c ∈ modelsProps ps, ∀ n ∈ c.2.refs,
    n ∈ names (modelsProps ps)
  | [], c, hc, _, _ => by simp [modelsProps] at hc
  | (_, s) :: ps, c, hc, n, hn => by
    simp only [modelsProps, List.mem_append, names, List.map_append] at hc ⊢
    rcases hc with hc | hc
    · exact .inl (models_closed s c hc n hn)
    · exact .inr (modelsProps_closed ps c hc n hn)
end

/-- A field's schema refers to what its pydantic schema's conversion does. -/
theorem refs_fieldSchema (s : Schema) (a : Annotations) (t : String) :
    (fieldSchema s a t).refs = (ofSchema s).refs := by
  unfold fieldSchema
  split
  · rename_i n h; rw [h]; split <;> simp [refs]
  · simp [refs]

end OSchema

end LeanFastapi
