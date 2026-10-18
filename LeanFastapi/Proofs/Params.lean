import LeanFastapi.RepoImpl.Infer

/-!
# Proofs: parameters, extraction, the 422 response and response models

* `params_to_args_loc`: every error extraction reports is located under one
  of the declared parameters (`[source, alias]`, or `["body"]`);
* `extract_sound` and `extract_cons_ok_iff`: extraction succeeds exactly
  when every parameter's raw value validates (or is absent and has a
  default), and gives those values;
* `extract_422`: when extraction fails, the operation, under FastAPI's
  exception handlers, answers `422 {"detail": errors}` with exactly those
  errors;
* `serialize_response_conforms`: what a response model sends conforms to its
  JSON Schema, and `serialize_response_dump`: a value of the model is sent as
  its own dump;
* `infer_param`, `header_alias_hyphen`: FastAPI's classification rule and
  header naming, as equations;
* `embed_rule`, `form_field_loc`, `form_missing`: when body parameters are
  embedded, and where a form field's errors are located.
-/

namespace LeanFastapi

open LeanJson (Json)
open LeanPydantic (FromJson ToJson JsonSchema LawfulJson Conforms)

/-! ## Locations -/

/-- **Every error is located under a declared parameter.** -/
theorem params_to_args_loc {β : Type} (ps : Params β) (inp : Inputs) (es : List RequestError)
    (h : ps.extract inp = .error es) : ∀ e ∈ es, ∃ i ∈ ps.infos, i.loc <+: e.loc :=
  ps.extract_loc inp es h

/-! ## What extraction returns -/

theorem atPath_ok_iff {ι α : Type} (v : Keel.Validator RequestError ι α) (x : ι) (a : α) :
    ∀ (p : Keel.Loc), (v.atPath p) x = .ok a ↔ v x = .ok a
  | [] => Iff.rfl
  | k :: p => by rw [Keel.Validator.atPath_cons, Keel.Validator.at_ok_iff, atPath_ok_iff v x a p]

/-- **A parameter's value is its raw value, validated, or its default.** -/
theorem extract_sound {α : Type} [ParamValue α] (p : Param α) (inp : Inputs) (a : α) :
    p.validator inp = .ok a ↔
      match p.raw inp with
      | none => p.default = some a
      | some v => ParamValue.read v = .ok a := by
  unfold Param.validator
  rw [atPath_ok_iff]
  unfold Param.read
  cases hr : p.raw inp with
  | none => cases p.default <;> simp
  | some v => simp

/-- **A product of parameters succeeds exactly when each does.** -/
theorem extract_cons_ok_iff {α β : Type} [ParamValue α] [ToJson α] [JsonSchema α] (p : Param α) (rest : Params β)
    (inp : Inputs) (a : α) (b : β) :
    (Params.cons p rest).extract inp = .ok (a, b) ↔ p.validator inp = .ok a ∧ rest.extract inp = .ok b :=
  Keel.Validator.both_ok_iff _ _ _ _ _

/-! ## The 422 response -/

/-- After a solve that recorded errors, the operation is not called:
`RequestValidationError` with every error is raised. -/
theorem respond_errors {σ : List Type} {β γ : Type} [IntoResult γ] (e : Endpoint σ β γ) (v? : Option β) (c : Ctx)
    (st : SolveState σ) (hne : st.shared.errors ≠ []) :
    (((e.respond v?).run c).run).run st = pure (.error (RequestValidationError st.shared.errors), st) := by
  obtain ⟨⟨errs, f, r⟩, cache⟩ := st
  simp only at hne
  cases errs with
  | nil => exact absurd rfl hne
  | cons x xs => cases v? <;> rfl

/-- **Validation errors are raised inside the exit stacks**: when the solve
records errors, the operation's outcome is `RequestValidationError` with all
of them, unwound through the exits the solve entered. -/
theorem endpoint_app_errors {σ : List Type} {β γ : Type} [IntoResult γ] (e : Endpoint σ β γ)
    (req : LeanStarlette.Request) (b : BodyInput) (v? : Option β) (st : SolveState σ)
    (hb : e.body req = .ok b) (hs : e.solveIO req b = pure (.ok v?, st)) (hne : st.shared.errors ≠ []) :
    e.app req = finish (.error (RequestValidationError st.shared.errors)) st.shared := by
  have h1 : e.app req = ExceptT.mk ((((e.respond v?).run (Endpoint.ctx req b)).run).run st >>=
      fun x => (finish x.1 x.2.shared).run) := by
    unfold Endpoint.app
    rw [hb]
    simp only [hs]
    rfl
  rw [h1, respond_errors e v? _ st hne]
  rfl

/-- **Invalid input is a 422 with exactly the solve's errors**: under
FastAPI's exception handlers, an operation whose parameters (its own and its
dependencies') fail to validate answers `422 {"detail": [...]}` listing
every error, when no `yield` dependency was entered. -/
theorem extract_422 {σ : List Type} {β γ : Type} [IntoResult γ] (e : Endpoint σ β γ)
    (req : LeanStarlette.Request) (b : BodyInput) (v? : Option β) (st : SolveState σ) (es : List RequestError)
    (hb : e.body req = .ok b) (hs : e.solveIO req b = pure (.ok v?, st)) (hst : st.shared = { errors := es })
    (hne : es ≠ []) :
    LeanStarlette.exceptionMiddleware defaultExceptionHandlers e.app req =
      pure (validationErrorResponse (errorsJson es)) := by
  have h := endpoint_app_errors e req b v? st hb hs (by rw [hst]; exact hne)
  rw [hst] at h
  simp only [LeanStarlette.exceptionMiddleware, h]
  rfl

/-! ## Response models -/

/-- **What a response model sends conforms to its schema.** -/
theorem serialize_response_conforms (β : Type) [FromJson β] [ToJson β] [JsonSchema β] [LawfulJson β]
    (j out : Json) (h : (ResponseModel.of β).serialize j = .ok out) :
    Conforms (JsonSchema.schema β) out := by
  simp only [ResponseModel.of] at h
  split at h
  · rename_i b _
    cases h
    exact LawfulJson.schema_sound { strict := true } _ b rfl (LawfulJson.fromJson_toJson _ b)
  · cases h

/-- **A value of the response model is sent as its dump** (re-validating it
changes nothing). -/
theorem serialize_response_dump (β : Type) [FromJson β] [ToJson β] [JsonSchema β] [LawfulJson β] (b : β) :
    (ResponseModel.of β).serialize (LeanPydantic.toJson LeanPydantic.DumpOpts.roundTrip b) =
      .ok (LeanPydantic.toJson LeanPydantic.DumpOpts.roundTrip b) := by
  simp only [ResponseModel.of, responseDumpOpts]
  rw [show ({ by_alias := true } : LeanPydantic.DumpOpts) = LeanPydantic.DumpOpts.roundTrip from rfl, LawfulJson.fromJson_toJson]

/-! ## Classification and naming -/

/-- **FastAPI's inference rule**: an argument without an explicit wrapper is
a path parameter when its name is in the path template, else the body when
its type is a model, else a query parameter. -/
theorem infer_param (name : String) (inPath isModel : Bool) :
    inferParam { name, inPath, isModel } =
      .param (if inPath then .path else if isModel then .body else .query) := by
  cases inPath <;> simp [inferParam]

/-- An explicit wrapper decides the source, outside the path template. -/
theorem infer_param_explicit (s : ParamShape) (w : Wrapper) (hw : w ≠ .none) (hr : s.isRequest = false)
    (hp : s.inPath = false) (hs : s.wrapper = w) : inferParam s = .param w.source := by
  unfold inferParam
  cases w <;> simp_all

/-- **A header parameter's name is its argument name with `_` as `-`**
(unless it has an alias or `convert_underscores=False`). -/
theorem header_alias_hyphen (name : String) :
    headerParamAlias name none true = String.ofList (name.toList.map fun c => if c = '_' then '-' else c) := rfl

/-! ## Forms and the embed rule -/

/-- A list headed by `a` has more than one distinct element exactly when
something in its tail differs from `a`. -/
theorem eraseDups_cons_length_gt_one {β : Type} [BEq β] [LawfulBEq β] (a : β) (l : List β) :
    (a :: l).eraseDups.length > 1 ↔ ∃ b ∈ l, b ≠ a := by
  rw [List.eraseDups_cons]
  simp only [List.length_cons, gt_iff_lt, Nat.lt_add_left_iff_pos]
  constructor
  · intro h
    cases hf : l.filter (fun b => !b == a) with
    | nil => rw [hf] at h; simp [List.eraseDups] at h
    | cons b bs =>
      have hb : b ∈ l.filter (fun b => !b == a) := by rw [hf]; exact List.mem_cons_self
      rw [List.mem_filter] at hb
      exact ⟨b, hb.1, by simpa using hb.2⟩
  · rintro ⟨b, hb, hne⟩
    cases hf : l.filter (fun b => !b == a) with
    | nil =>
      have : b ∈ l.filter (fun b => !b == a) := List.mem_filter.2 ⟨hb, by simpa using hne⟩
      rw [hf] at this; cases this
    | cons c cs => rw [List.eraseDups_cons]; simp

/-- **The embed rule** (`_should_embed_body_fields`): the body parameters are
read from members of the body exactly when there is another body parameter
name, the first is `embed=True`, or the first is a form field whose type is
not a model. -/
theorem embed_rule (f : BodyField) (fs : List BodyField) :
    shouldEmbedBodyFields (f :: fs) = true ↔
      (∃ g ∈ fs, g.name ≠ f.name) ∨ f.embed = true ∨ (f.isForm = true ∧ f.isModel = false) := by
  simp only [shouldEmbedBodyFields, List.map_cons, Bool.or_eq_true, decide_eq_true_eq,
    eraseDups_cons_length_gt_one, List.mem_map, Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · rintro ((⟨n, ⟨g, hg, rfl⟩, hn⟩ | h) | h)
    · exact .inl ⟨g, hg, hn⟩
    · exact .inr (.inl h)
    · exact .inr (.inr h)
  · rintro (⟨g, hg, hn⟩ | h | h)
    · exact .inl (.inl ⟨g.name, ⟨g, hg, rfl⟩, hn⟩)
    · exact .inl (.inr h)
    · exact .inr h

/-- **A form field's errors are under `["body", alias]`.** -/
theorem form_field_loc {α : Type} [ParamValue α] (p : Param α) (inp : Inputs) (es : List RequestError)
    (hs : p.source = .body) (he : p.embed = true) (h : p.validator inp = .error es) :
    ∀ e ∈ es, [.key "body", .key p.alias] <+: e.loc := by
  have hl : p.loc = [.key "body", .key p.alias] := by
    simp [Param.loc, Param.isWholeBody, hs, he, Source.value]
  rw [← hl]; exact p.validator_loc inp es h

/-- **A form field absent from the form is one `missing` error at
`["body", alias]`** (when it has no default). -/
theorem form_missing {α : Type} [ParamValue α] (p : Param α) (inp : Inputs) (fs : List (String × FormInput))
    (hs : p.source = .body) (he : p.embed = true) (hb : inp.body = .form fs)
    (hr : Inputs.formRaw fs p.alias p.isSeq = none) (hd : p.default = none) :
    p.validator inp = .error [{ RequestError.missing with loc := [.key "body", .key p.alias] }] := by
  have hraw : p.raw inp = none := by
    simp [Param.raw, Param.isWholeBody, hs, he, hb, hr]
  simp [Param.validator, Param.loc, Param.isWholeBody, hs, he, Source.value, Keel.Validator.at,
    Param.read, hraw, hd, Except.mapError, Keel.Located.within, RequestError.missing]

end LeanFastapi
