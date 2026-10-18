import LeanFastapi.RepoImpl.Security

/-!
# Proofs: security schemes

* `bearer_parse`: `Authorization: <scheme> <param>` reads back as that scheme
  and the stripped parameter;
* `b64decode_encode`, `basic_base64_roundtrip`: base64 decoding inverts
  encoding, so `HTTPBasic` reads back the credentials a client encodes;
* `apikey_sources`: an API key is read exactly where a parameter of the same
  location would be.
-/

namespace LeanFastapi

open LeanStarlette (Request)

/-! ## Splitting at a separator -/

theorem takeWhile_ne_sep {c : Char} {l : List Char} (r : List Char) (h : c ∉ l) :
    (l ++ c :: r).takeWhile (· ≠ c) = l := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx : x ≠ c := fun e => h (e ▸ List.mem_cons_self ..)
    rw [List.cons_append, List.takeWhile_cons_of_pos (by simpa using hx),
      ih (fun m => h (List.mem_cons_of_mem _ m))]

theorem dropWhile_ne_sep {c : Char} {l : List Char} (r : List Char) (h : c ∉ l) :
    (l ++ c :: r).dropWhile (· ≠ c) = c :: r := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx : x ≠ c := fun e => h (e ▸ List.mem_cons_self ..)
    rw [List.cons_append, List.dropWhile_cons_of_pos (by simpa using hx),
      ih (fun m => h (List.mem_cons_of_mem _ m))]

/-- **`get_authorization_scheme_param`** reads `"<scheme> <param>"` as the
scheme and the stripped parameter, for a scheme without spaces. -/
theorem bearer_parse (scheme param : String) (h : ' ' ∉ scheme.toList) :
    authorizationSchemeParam (some (scheme ++ " " ++ param)) = (scheme, pyStrip param) := by
  have hl : (scheme ++ " " ++ param).toList = scheme.toList ++ ' ' :: param.toList := by simp
  have hne : (scheme ++ " " ++ param).isEmpty = false := by
    rw [Bool.eq_false_iff]; intro he
    have := congrArg String.toList (String.isEmpty_iff.mp he); rw [hl] at this; simp at this
  simp only [authorizationSchemeParam, hne, hl, takeWhile_ne_sep _ h, dropWhile_ne_sep _ h]
  simp

/-! ## Base64 -/

theorem b64Char_table : ∀ i : Fin 64,
    b64Value (b64Char i.val) = some i.val ∧ b64Char i.val ≠ '=' ∧ (b64Char i.val).toNat < 128 := by
  decide

theorem b64Char_mod (n : Nat) : b64Char n = b64Char (n % 64) := by
  simp [b64Char]

theorem b64Value_b64Char (n : Nat) : b64Value (b64Char n) = some (n % 64) := by
  rw [b64Char_mod]; exact (b64Char_table ⟨n % 64, Nat.mod_lt _ (by decide)⟩).1

theorem b64Char_ne_pad (n : Nat) : b64Char n ≠ '=' := by
  rw [b64Char_mod]; exact (b64Char_table ⟨n % 64, Nat.mod_lt _ (by decide)⟩).2.1

theorem b64Char_ascii (n : Nat) : (b64Char n).toNat < 128 := by
  rw [b64Char_mod]; exact (b64Char_table ⟨n % 64, Nat.mod_lt _ (by decide)⟩).2.2


/-- Decoding the encoding of whole and final groups, from the start of a
group. -/
theorem run_b64encode (bs : List Nat) (hb : ∀ b ∈ bs, b < 256) (st : B64State) (hq : st.quad = 0) :
    (st.run (b64encode bs)).quad = 0 ∧ (st.run (b64encode bs)).out = bs.reverse ++ st.out := by
  induction bs using b64encode.induct generalizing st with
  | case1 a b c rest ih =>
    have ha := hb a (by simp); have hb' := hb b (by simp); have hc := hb c (by simp)
    simp [b64encode, B64State.run, B64State.step, b64Char_ne_pad, b64Value_b64Char, hq]
    have h := fun st' => ih (fun x hx => hb x (by simp [hx])) st'
    refine ⟨(h _ (by rfl)).1, (h _ (by rfl)).2.trans ?_⟩
    simp only [List.append_cancel_left_eq, List.cons.injEq]
    refine ⟨?_, ?_, ?_, trivial⟩ <;> omega
  | case2 a b =>
    have ha := hb a (by simp); have hb' := hb b (by simp)
    simp [b64encode, B64State.run, B64State.step, b64Char_ne_pad, b64Value_b64Char, hq]
    constructor <;> omega
  | case3 a =>
    have ha := hb a (by simp)
    simp [b64encode, B64State.run, B64State.step, b64Char_ne_pad, b64Value_b64Char, hq]
    omega
  | case4 => exact ⟨hq, by simp [b64encode, B64State.run]⟩

theorem b64encode_ascii (bs : List Nat) : ∀ c ∈ b64encode bs, c.toNat < 128 := by
  induction bs using b64encode.induct with
  | case1 a b c rest ih => intro x hx; simp [b64encode] at hx; rcases hx with h | h | h | h | h <;> (try subst h) <;> first | exact b64Char_ascii _ | exact ih _ h
  | case2 a b => intro x hx; simp [b64encode] at hx; rcases hx with h | h | h | h <;> subst h <;> first | exact b64Char_ascii _ | decide
  | case3 a => intro x hx; simp [b64encode] at hx; rcases hx with h | h | h <;> subst h <;> first | exact b64Char_ascii _ | decide
  | case4 => simp [b64encode]

/-- **Base64 decoding inverts encoding** (`b64decode(b64encode(b)) == b`). -/
theorem b64decode_encode (bs : List Nat) (hb : ∀ b ∈ bs, b < 256) :
    b64decode (b64encode bs) = some bs := by
  have hasc : (b64encode bs).any (fun c => c.toNat ≥ 128) = false := by
    simp only [List.any_eq_false]; intro c hc; have := b64encode_ascii bs c hc; simp; omega
  obtain ⟨h1, h2⟩ := run_b64encode bs hb {} rfl
  simp [b64decode, hasc, h1, h2]

/-! ## HTTP Basic -/

/-- **`HTTPBasic` reads back the credentials a client encodes**, for ASCII
credentials whose username has no `:` (HTTP Basic cannot carry one). -/
theorem basic_base64_roundtrip (username password : String)
    (hu : ∀ c ∈ username.toList, c.toNat < 128) (hp : ∀ c ∈ password.toList, c.toNat < 128)
    (hc : ':' ∉ username.toList) :
    basicCredentials (basicToken username password) = some { username, password } := by
  have hl : (username ++ ":" ++ password).toList = username.toList ++ ':' :: password.toList := by simp
  have hall : ∀ c ∈ (username ++ ":" ++ password).toList, c.toNat < 128 := by
    rw [hl]; intro c hc'; simp at hc'
    rcases hc' with h | h | h
    · exact hu c h
    · subst h; decide
    · exact hp c h
  have hdec := b64decode_encode ((username ++ ":" ++ password).toList.map Char.toNat)
    (by intro b hb; obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hb; have := hall c hc'; omega)
  have hasc : ((username ++ ":" ++ password).toList.map Char.toNat).any (· ≥ 128) = false := by
    simp only [List.any_eq_false]; intro b hb; obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hb
    have := hall c hc'; simp; omega
  have hround : ((username ++ ":" ++ password).toList.map Char.toNat).map Char.ofNat =
      (username ++ ":" ++ password).toList := by
    rw [List.map_map]
    conv => rhs; rw [← List.map_id (username ++ ":" ++ password).toList]
    apply List.map_congr_left; intro c _; simp [Char.ofNat_toNat]
  unfold basicCredentials basicToken
  rw [String.toList_ofList, hdec]
  simp only [Option.bind_eq_bind, Option.bind_some, hasc, Bool.false_eq_true, ite_false]
  rw [hround, hl, takeWhile_ne_sep _ hc, dropWhile_ne_sep _ hc]
  simp

/-! ## API keys -/

/-- **An API key is read where a parameter of its location is**: the query
string, a header, or a cookie, exactly as `Query`, `Header` and `Cookie`
read them. -/
theorem apikey_sources (location : APIKeyIn) (name : String) (req : Request) (body : BodyInput) :
    (apiKeyValue location name req).map .str = (Inputs.ofRequest req body).lookup location.source name := by
  cases location <;> rfl

end LeanFastapi
