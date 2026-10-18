import LeanFastapi.Proofs.Schema

/-!
# Proofs: the OpenAPI document of every application

Facts about `getOpenapi info routes` for every list of routes, so for every
application (`FastAPI.openapiSchema`):

* `openapi_all_routes`: its operations are exactly the `(path, method)`
  pairs of the routes in the schema;
* `openapi_refs_resolve`: every `$ref` names a component;
* `openapi_components_sorted`: components are sorted by name, strictly;
* `operationId_unique`: when the routes' operation ids are distinct, so are
  the document's;
* `openapi_operation_of_route`: every operation is some route's
  `APIRoute.operation` for one of its methods, so the per-route facts
  `openapi_422_iff` and `openapi_params_match` hold of every operation.

The building blocks are two general lemmas about upserting into an
association list (`foldl upsertOp`, `dedupParams`): keys are kept, each key
occurs once, and every entry comes from the input.
-/

namespace LeanFastapi

open LeanPydantic (Schema)

/-! ## Upserting operations -/

/-- The `(path, method)` key of an operation entry. -/
abbrev opKey (e : String × String × Operation) : String × String := (e.1, e.2.1)

theorem upsert_cond (x e : String × String × Operation) :
    (x.1 == e.1 && x.2.1 == e.2.1) = decide (opKey x = opKey e) := by
  by_cases h1 : x.1 = e.1 <;> by_cases h2 : x.2.1 = e.2.1 <;> simp [opKey, h1, h2]

theorem keys_upsertOp (acc : List (String × String × Operation)) (e : String × String × Operation) :
    (upsertOp acc e).map opKey =
      if opKey e ∈ acc.map opKey then acc.map opKey else acc.map opKey ++ [opKey e] := by
  unfold upsertOp
  simp only [upsert_cond]
  by_cases h : opKey e ∈ acc.map opKey
  · have ha : acc.any (fun x => decide (opKey x = opKey e)) = true := by
      obtain ⟨x, hx, hk⟩ := List.mem_map.1 h
      exact List.any_eq_true.2 ⟨x, hx, by simp [hk]⟩
    rw [if_pos ha, if_pos h, List.map_map]
    congr 1; funext x
    simp only [Function.comp]
    split
    · rename_i hk; exact (of_decide_eq_true hk).symm
    · rfl
  · have ha : ¬ acc.any (fun x => decide (opKey x = opKey e)) = true := by
      intro ha
      obtain ⟨x, hx, hk⟩ := List.any_eq_true.1 ha
      exact h (List.mem_map.2 ⟨x, hx, of_decide_eq_true hk⟩)
    rw [if_neg ha, if_neg h]; simp

theorem mem_upsertOp (acc : List (String × String × Operation)) (e y : String × String × Operation) :
    y ∈ upsertOp acc e → y = e ∨ y ∈ acc := by
  unfold upsertOp
  split
  · intro hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    split
    · exact .inl rfl
    · exact .inr hx
  · intro hy
    rcases List.mem_append.1 hy with hy | hy
    · exact .inr hy
    · exact .inl (List.mem_singleton.1 hy)

theorem mem_keys_foldl_upsert (l acc : List (String × String × Operation)) (k : String × String) :
    k ∈ (l.foldl upsertOp acc).map opKey ↔ k ∈ acc.map opKey ∨ k ∈ l.map opKey := by
  induction l generalizing acc with
  | nil => simp
  | cons e l ih =>
    rw [List.foldl_cons, ih, keys_upsertOp]
    split
    · rename_i h
      simp only [List.map_cons, List.mem_cons]
      constructor
      · rintro (h' | h') <;> simp [h']
      · rintro (h' | rfl | h')
        · exact .inl h'
        · exact .inl h
        · exact .inr h'
    · simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, or_assoc]

theorem nodup_keys_foldl_upsert (l acc : List (String × String × Operation)) (h : (acc.map opKey).Nodup) :
    ((l.foldl upsertOp acc).map opKey).Nodup := by
  induction l generalizing acc with
  | nil => exact h
  | cons e l ih =>
    rw [List.foldl_cons]
    apply ih
    rw [keys_upsertOp]
    split
    · exact h
    · rename_i hn
      rw [List.nodup_append]
      refine ⟨h, by simp, ?_⟩
      intro a ha b hb hab
      rw [List.mem_singleton.1 hb] at hab
      exact hn (hab ▸ ha)

theorem mem_foldl_upsert (l acc : List (String × String × Operation)) (y : String × String × Operation) :
    y ∈ l.foldl upsertOp acc → y ∈ acc ∨ y ∈ l := by
  induction l generalizing acc with
  | nil => exact .inl
  | cons e l ih =>
    intro h
    rcases ih _ h with h | h
    · rcases mem_upsertOp acc e y h with rfl | h
      · exact .inr List.mem_cons_self
      · exact .inl h
    · exact .inr (List.mem_cons_of_mem _ h)

/-! ## Nodup through an injective map -/

theorem eq_of_nodup_map {α β : Type} (f : α → β) :
    ∀ (l : List α), (l.map f).Nodup → ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y
  | [], _, x, hx, _, _, _ => absurd hx (by simp)
  | a :: t, h, x, hx, y, hy, hxy => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    rcases List.mem_cons.1 hx with hx' | hx2 <;> rcases List.mem_cons.1 hy with hy' | hy2
    · rw [hx', hy']
    · subst hx'; exact absurd hxy.symm (h.1 y hy2)
    · subst hy'; exact absurd hxy (h.1 x hx2)
    · exact eq_of_nodup_map f t (by simpa using h.2) x hx2 y hy2 hxy

theorem nodup_map_of_sub {α β κ : Type} (f : α → β) (key : α → κ) (L : List α) (hL : (L.map f).Nodup) :
    ∀ (R : List α), (∀ x ∈ R, x ∈ L) → (R.map key).Nodup → (R.map f).Nodup
  | [], _, _ => by simp
  | a :: t, hsub, hk => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hk ⊢
    refine ⟨fun b hb hfb => ?_, nodup_map_of_sub f key L hL t (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) hk.2⟩
    have := eq_of_nodup_map f L hL b (hsub b (List.mem_cons_of_mem _ hb)) a (hsub a List.mem_cons_self) hfb
    exact hk.1 b hb (by rw [this])

/-! ## The document's operations -/

theorem keys_getOpenapi (info : Info) (routes : List APIRoute) :
    (getOpenapi info routes).keys = (openapiPaths routes).map opKey := rfl

/-- **Every operation of the document is a route's operation** for one of
its methods, under the route's path format. -/
theorem openapi_operation_of_route (info : Info) (routes : List APIRoute) (e : String × String × Operation)
    (h : e ∈ (getOpenapi info routes).paths) :
    ∃ r ∈ routes, r.include_in_schema = true ∧ ∃ m ∈ r.methods,
      e = (pathFormat r.path, m.toLower, r.operation m) := by
  rcases mem_foldl_upsert _ [] e h with h | h
  · simp at h
  · obtain ⟨r, hr, he⟩ := List.mem_flatMap.1 h
    unfold APIRoute.operations at he
    split at he
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 he
      exact ⟨r, hr, ‹_›, m, hm, rfl⟩
    · simp at he

/-- **All routes, and nothing else**: the document has an operation at
`(path, method)` exactly when some route in the schema has that path format
and method. -/
theorem openapi_all_routes (info : Info) (routes : List APIRoute) (p m : String) :
    (p, m) ∈ (getOpenapi info routes).keys ↔
      ∃ r ∈ routes, r.include_in_schema = true ∧ pathFormat r.path = p ∧ m ∈ r.methods.map String.toLower := by
  rw [keys_getOpenapi, openapiPaths, mem_keys_foldl_upsert]
  simp only [List.map_nil, List.not_mem_nil, false_or, List.mem_map, List.mem_flatMap]
  constructor
  · rintro ⟨e, ⟨r, hr, he⟩, hk⟩
    unfold APIRoute.operations at he
    split at he
    · obtain ⟨m', hm', rfl⟩ := List.mem_map.1 he
      simp only [opKey, Prod.mk.injEq] at hk
      exact ⟨r, hr, ‹_›, hk.1, m', hm', hk.2⟩
    · simp at he
  · rintro ⟨r, hr, hi, hp, m', hm', rfl⟩
    refine ⟨(pathFormat r.path, m'.toLower, r.operation m'), ⟨r, hr, ?_⟩, by simp [opKey, hp]⟩
    simp only [APIRoute.operations, hi, if_true, List.mem_map]
    exact ⟨m', hm', rfl⟩

/-- Each `(path, method)` occurs once in the document. -/
theorem openapi_keys_nodup (info : Info) (routes : List APIRoute) : (getOpenapi info routes).keys.Nodup := by
  rw [keys_getOpenapi, openapiPaths]
  exact nodup_keys_foldl_upsert _ [] (by simp)

/-- **Operation ids are unique** when the routes' are: the document keeps
one operation per `(path, method)`, each a route's. -/
theorem operationId_unique (info : Info) (routes : List APIRoute)
    (h : ((routes.flatMap APIRoute.operations).map (·.2.2.operationId)).Nodup) :
    (getOpenapi info routes).operationIds.Nodup := by
  unfold OpenAPI.operationIds
  refine nodup_map_of_sub _ opKey _ h _ (fun x hx => ?_) (openapi_keys_nodup info routes)
  rcases mem_foldl_upsert _ [] x hx with hx | hx
  · simp at hx
  · exact hx

/-- **Components are sorted** by name, with no name twice. -/
theorem openapi_components_sorted (info : Info) (routes : List APIRoute) :
    (getOpenapi info routes).componentNames.Pairwise (· < ·) :=
  (getOpenapi info routes).components.sorted

/-! ## One route's operation -/

theorem mem_dedupParams_keys (ps : List Parameter) (k : Source × String) :
    k ∈ (dedupParams ps).map Parameter.key ↔ k ∈ ps.map Parameter.key := by
  unfold dedupParams
  suffices ∀ acc : List Parameter, k ∈ (ps.foldl (fun acc p =>
      if acc.any (fun q => q.key == p.key) then
        acc.map fun q => if q.key == p.key && (p.required || !q.required) then p else q
      else acc ++ [p]) acc).map Parameter.key ↔ k ∈ acc.map Parameter.key ∨ k ∈ ps.map Parameter.key by
    simpa using this []
  induction ps with
  | nil => intro acc; simp
  | cons p ps ih =>
    intro acc
    rw [List.foldl_cons, ih]
    split
    · rename_i ha
      obtain ⟨q, hq, hk⟩ := List.any_eq_true.1 ha
      have hkeys : (acc.map fun q => if q.key == p.key && (p.required || !q.required) then p else q).map
          Parameter.key = acc.map Parameter.key := by
        rw [List.map_map]; congr 1; funext x
        simp only [Function.comp]
        split
        · rename_i h; simp only [Bool.and_eq_true, beq_iff_eq] at h; exact h.1.symm
        · rfl
      rw [hkeys]
      simp only [List.map_cons, List.mem_cons]
      have hpk : p.key ∈ acc.map Parameter.key := List.mem_map.2 ⟨q, hq, beq_iff_eq.1 hk⟩
      constructor
      · rintro (h | h) <;> simp [h]
      · rintro (h | rfl | h)
        · exact .inl h
        · exact .inl hpk
        · exact .inr h
    · simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, or_assoc]

theorem mem_dedupParams (ps : List Parameter) (p : Parameter) : p ∈ dedupParams ps → p ∈ ps := by
  unfold dedupParams
  suffices ∀ acc : List Parameter, p ∈ ps.foldl (fun acc p =>
      if acc.any (fun q => q.key == p.key) then
        acc.map fun q => if q.key == p.key && (p.required || !q.required) then p else q
      else acc ++ [p]) acc → p ∈ acc ∨ p ∈ ps from fun h => (this [] h).elim (by simp) id
  induction ps with
  | nil => intro acc h; exact .inl h
  | cons x ps ih =>
    intro acc h
    rcases ih _ h with h | h
    · dsimp only at h
      split at h
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h
        split
        · exact .inr List.mem_cons_self
        · exact .inl hy
      · rcases List.mem_append.1 h with h | h
        · exact .inl h
        · exact .inr (List.mem_singleton.1 h ▸ List.mem_cons_self)
    · exact .inr (List.mem_cons_of_mem _ h)

/-- **The `422` response**: an operation documents `422` exactly when its
route validates input (has a parameter or a body) or its own status code is
`422`. -/
theorem openapi_422_iff (r : APIRoute) (m : String) :
    "422" ∈ (r.operation m).responses.map Prod.fst ↔ r.params ≠ [] ∨ r.statusKey = "422" := by
  simp only [APIRoute.operation, APIRoute.validates]
  by_cases hs : r.statusKey = "422" <;> by_cases hp : r.params = [] <;> simp [hs, hp, List.isEmpty_iff]
  all_goals exact fun h => hs h.symm

/-- **Parameters match**: an operation documents the parameter `(in, name)`
exactly when its route declares a non-body parameter with that source and
wire name that is in the schema. -/
theorem openapi_params_match (r : APIRoute) (m : String) (i : Source) (n : String) :
    (i, n) ∈ (r.operation m).parameters.map Parameter.key ↔
      ∃ p ∈ r.params, p.source ≠ .body ∧ p.include_in_schema = true ∧ p.source = i ∧ p.alias = n := by
  rw [show (r.operation m).parameters = r.parameters from rfl, APIRoute.parameters, mem_dedupParams_keys]
  simp only [List.map_map, List.mem_map, List.mem_filter, Function.comp, ParamInfo.toParameter, Parameter.key,
    Prod.mk.injEq]
  constructor
  · rintro ⟨p, ⟨hp, hf⟩, h1, h2⟩
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hf
    exact ⟨p, hp, hf.1, hf.2, h1, h2⟩
  · rintro ⟨p, hp, hb, hi, h1, h2⟩
    exact ⟨p, ⟨hp, by simp [hb, hi]⟩, h1, h2⟩

/-! ## References resolve -/

/-- The definitions every included route contributes. -/
theorem models_mem_definitions (routes : List APIRoute) (r : APIRoute) (hr : r ∈ routes)
    (hi : r.include_in_schema = true) (s : Schema) (hs : s ∈ r.schemas) (c : String × OSchema)
    (hc : c ∈ OSchema.models s) : c ∈ openapiDefinitions routes := by
  unfold openapiDefinitions
  exact List.mem_append_left _ (List.mem_flatMap.2 ⟨r, List.mem_filter.2 ⟨hr, hi⟩,
    List.mem_flatMap.2 ⟨s, hs, hc⟩⟩)

theorem validation_mem_definitions (routes : List APIRoute) (r : APIRoute) (hr : r ∈ routes)
    (hi : r.include_in_schema = true) (hv : r.validates = true) (c : String × OSchema)
    (hc : c ∈ validationDefinitions) : c ∈ openapiDefinitions routes := by
  unfold openapiDefinitions
  have : (routes.filter (·.include_in_schema)).any APIRoute.validates = true :=
    List.any_eq_true.2 ⟨r, List.mem_filter.2 ⟨hr, hi⟩, hv⟩
  simp only [this, if_true]
  exact List.mem_append_right _ hc

/-- A schema of an included route refers only to definitions. -/
theorem refs_route_schema (routes : List APIRoute) (r : APIRoute) (hr : r ∈ routes)
    (hi : r.include_in_schema = true) (s : Schema) (hs : s ∈ r.schemas) :
    ∀ n ∈ (OSchema.ofSchema s).refs, n ∈ OSchema.names (openapiDefinitions routes) := by
  intro n hn
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 (OSchema.refs_ofSchema s n hn)
  exact List.mem_map.2 ⟨c, models_mem_definitions routes r hr hi s hs c hc, rfl⟩

theorem refs_mainContent (r : APIRoute) (m : String) (c : MediaContent)
    (h : (if isBodyAllowedForStatusCode (r.status_code.getD 200) = true then
      some ({ schema := r.responseSchema m } : MediaContent) else none) = some c) :
    ∀ n ∈ c.schema.refs, ∃ s ∈ r.response_model.toList, n ∈ (OSchema.ofSchema s).refs := by
  intro n hn
  split at h
  · cases h
    unfold APIRoute.responseSchema at hn
    split at hn
    · rename_i s hs
      rw [OSchema.refs_fieldSchema] at hn
      exact ⟨s, by simp [hs], hn⟩
    · simp [OSchema.refs] at hn
  · cases h

theorem requestBody_mem (r : APIRoute) (m : String) (b : RequestBody) (h : r.requestBody m = some b) :
    ∃ bi ∈ r.params, ∃ a t, b.content.schema = fieldSchema bi.schema a t := by
  unfold APIRoute.requestBody at h
  split at h
  · split at h
    · rename_i bi _ hbs
      cases h
      exact ⟨bi, (List.mem_filter.1 (hbs ▸ List.mem_cons_self)).1, _, _, rfl⟩
    · cases h
  · cases h

/-- An included route's operation refers only to definitions. -/
theorem refs_operation (routes : List APIRoute) (r : APIRoute) (hr : r ∈ routes)
    (hi : r.include_in_schema = true) (m : String) :
    ∀ n ∈ (r.operation m).refs, n ∈ OSchema.names (openapiDefinitions routes) := by
  intro n hn
  simp only [Operation.refs, APIRoute.operation, List.mem_append, List.mem_flatMap] at hn
  rcases hn with (⟨p, hp, hn⟩ | hn) | ⟨⟨k, resp⟩, hk, hn⟩
  · -- a parameter
    have hp := mem_dedupParams _ p hp
    obtain ⟨pi, hpi, rfl⟩ := List.mem_map.1 hp
    simp only [ParamInfo.toParameter, OSchema.refs_fieldSchema] at hn
    exact refs_route_schema routes r hr hi pi.schema
      (List.mem_append_left _ (List.mem_map.2 ⟨pi, (List.mem_filter.1 hpi).1, rfl⟩)) n hn
  · -- the request body
    revert hn
    cases hb : r.requestBody m with
    | none => simp
    | some b =>
      intro hn
      obtain ⟨bi, hbi, a, t, hs⟩ := requestBody_mem r m b hb
      simp only [hs, OSchema.refs_fieldSchema] at hn
      exact refs_route_schema routes r hr hi bi.schema
        (List.mem_append_left _ (List.mem_map.2 ⟨bi, hbi, rfl⟩)) n hn
  · -- a response
    rcases hk with hk | hk
    · simp only [List.mem_singleton, Prod.mk.injEq] at hk
      obtain ⟨_, rfl⟩ := hk
      revert hn
      split
      · rename_i c hc
        intro hn
        dsimp only at hc
        obtain ⟨s, hs, hn⟩ := refs_mainContent r m c hc n hn
        exact refs_route_schema routes r hr hi s (List.mem_append_right _ hs) n hn
      · simp
    · split at hk
      · rename_i hv
        simp only [List.mem_singleton, Prod.mk.injEq] at hk
        obtain ⟨_, rfl⟩ := hk
        simp only [validationErrorResponseSpec, OSchema.refs, List.mem_singleton] at hn
        subst hn
        exact List.mem_map.2 ⟨("HTTPValidationError", httpValidationErrorSchema),
          validation_mem_definitions routes r hr hi hv _ (by simp [validationDefinitions]), rfl⟩
      · simp at hk

/-- A definition refers only to definitions. -/
theorem refs_definition (routes : List APIRoute) (c : String × OSchema) (hc : c ∈ openapiDefinitions routes) :
    ∀ n ∈ c.2.refs, n ∈ OSchema.names (openapiDefinitions routes) := by
  intro n hn
  unfold openapiDefinitions at hc ⊢
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨r, hr, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨s, hs, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 (OSchema.models_closed s c hc n hn)
    exact List.mem_map.2 ⟨d, List.mem_append_left _ (List.mem_flatMap.2 ⟨r, hr, List.mem_flatMap.2 ⟨s, hs, hd⟩⟩), rfl⟩
  · split at hc
    · rename_i hv
      simp only [validationDefinitions, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · simp [validationErrorSchema, OSchema.refs, OSchema.refsProps, OSchema.refsList] at hn
      · simp only [httpValidationErrorSchema, OSchema.refs, OSchema.refsProps, List.mem_append, List.mem_singleton,
          List.not_mem_nil, or_false] at hn
        subst hn
        simp only [hv, if_true]
        exact List.mem_map.2 ⟨("ValidationError", validationErrorSchema), List.mem_append_right _ (by simp [validationDefinitions]), rfl⟩
    · simp at hc

/-- **References resolve**: every `$ref` in the document, in an operation or
in a component, names one of its components. -/
theorem openapi_refs_resolve (info : Info) (routes : List APIRoute) :
    ∀ n ∈ (getOpenapi info routes).refs, n ∈ (getOpenapi info routes).componentNames := by
  intro n hn
  have hnames : ∀ k, k ∈ (getOpenapi info routes).componentNames ↔ k ∈ OSchema.names (openapiDefinitions routes) :=
    fun k => Sorted.mem_keys_ofListSorted _ k
  rw [hnames]
  simp only [OpenAPI.refs, List.mem_append, List.mem_flatMap] at hn
  rcases hn with ⟨e, he, hn⟩ | ⟨c, hc, hn⟩
  · obtain ⟨r, hr, hi, m, _, rfl⟩ := openapi_operation_of_route info routes e he
    exact refs_operation routes r hr hi m n hn
  · exact refs_definition routes c (Sorted.mem_ofListSorted _ c hc) n hn

end LeanFastapi
