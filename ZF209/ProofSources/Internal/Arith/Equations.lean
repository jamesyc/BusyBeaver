module
public import Internal.Arith.Translate
@[expose] public section
/-! # Code equations for the arithmetic translation

Consecutive-variable vectors, well-formedness of graphs and translations, and the
facts that the translation commutes with negation and with the shift of free
variables. -/
namespace ZF209.Internal.Arith
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Consecutive variables -/

lemma idv_spec : ∀ n : V, IsSemitermVec ℒₛₑₜ n n (idv n) ∧ ∀ i < n, (idv n).[i] = ^#i := by
  intro n
  induction n using ISigma1.pi1_succ_induction
  · definability
  · simp
  · rename_i n ih
    refine ⟨by simpa using ih.1.qVec, ?_⟩
    intro i hi
    rcases zero_or_succ i with rfl | ⟨i, rfl⟩
    · simp [qVec]
    · have hi' : i < n := by simpa using hi
      simp [qVec, ih.1.lh, nth_termBShiftVec ih.1.isUTerm hi', ih.2 i hi']

lemma idv_semitermVec (n : V) : IsSemitermVec ℒₛₑₜ n n (idv n) := (idv_spec n).1
@[simp] lemma nth_idv {n i : V} (hi : i < n) : (idv n).[i] = ^#i := (idv_spec n).2 i hi
@[simp] lemma len_idv (n : V) : len (idv n) = n := (idv_semitermVec n).lh

lemma bv2_semitermVec (n : V) : IsSemitermVec ℒₛₑₜ n (n + 2) (bv2 n) := by
  have := (idv_semitermVec n).termBShiftVec.termBShiftVec
  simpa [bv2, add_assoc, one_add_one_eq_two] using this

lemma bv3_semitermVec (n : V) : IsSemitermVec ℒₛₑₜ n (n + 3) (bv3 n) := by
  have := (bv2_semitermVec n).termBShiftVec
  simpa [bv3, add_assoc, show (2 : V) + 1 = 3 by norm_num] using this

@[simp] lemma nth_bv2 {n i : V} (hi : i < n) : (bv2 n).[i] = ^#(i + 2) := by
  have h := idv_semitermVec n
  simp [bv2, nth_termBShiftVec h.termBShiftVec.isUTerm hi, nth_termBShiftVec h.isUTerm hi,
    nth_idv hi, add_assoc, one_add_one_eq_two]

@[simp] lemma nth_bv3 {n i : V} (hi : i < n) : (bv3 n).[i] = ^#(i + 3) := by
  have h := bv2_semitermVec n
  simp [bv3, nth_termBShiftVec h.isUTerm hi, nth_bv2 hi, add_assoc,
    show (2 : V) + 1 = 3 by norm_num]

@[simp] lemma len_bv2 (n : V) : len (bv2 n) = n := (bv2_semitermVec n).lh
@[simp] lemma len_bv3 (n : V) : len (bv3 n) = n := (bv3_semitermVec n).lh

/-! ## Templates -/

lemma semiformula_mono {n m p : V} (h : IsSemiformula ℒₛₑₜ n p) (hnm : n ≤ m) :
    IsSemiformula ℒₛₑₜ m p := ⟨h.isUFormula, le_trans h.bv_le hnm⟩

lemma tq_semiformula {k : ℕ} (φ : Semisentence ℒₛₑₜ k) : IsSemiformula ℒₛₑₜ (k : V) (tq φ : V) := by
  rw [tq_eq]; simp

@[simp] lemma shift_tq {k : ℕ} (φ : Semisentence ℒₛₑₜ k) : shift ℒₛₑₜ (tq φ : V) = (tq φ : V) := by
  rw [tq_eq, Sentence.quote_def, ← Semiformula.quote_shift]
  congr 1
  unfold Rewriting.emb Rewriting.shift
  rw [← TransitiveRewriting.comp_app]; congr 2
  ext x <;> simp

lemma lor_func_cases {k f : V} (h : (ℒₒᵣ).IsFunc k f) :
    (k = 0 ∧ f = zeroIndex) ∨ (k = 0 ∧ f = oneIndex) ∨ (k = 2 ∧ f = addIndex) ∨
      (k = 2 ∧ f = mulIndex) := by
  have e₀ : (⌜(Language.Zero.zero : (ℒₒᵣ).Func 0)⌝ : V) = zeroIndex := rfl
  have e₁ : (⌜(Language.One.one : (ℒₒᵣ).Func 0)⌝ : V) = oneIndex := rfl
  have e₂ : (⌜(Language.Add.add : (ℒₒᵣ).Func 2)⌝ : V) = addIndex := rfl
  have e₃ : (⌜(Language.Mul.mul : (ℒₒᵣ).Func 2)⌝ : V) = mulIndex := rfl
  simpa [isFunc_iff_LOR, e₀, e₁, e₂, e₃] using h

lemma vec2_eq' {v : V} (h : len v = 2) : v.[0] ∷ v.[1] ∷ 0 = v := by
  apply nth_ext' 2 (by simp [one_add_one_eq_two]) h
  intro i hi
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · simp
  · rcases zero_or_succ i with rfl | ⟨i, rfl⟩
    · simp
    · exfalso; have : i + 1 + 1 < 2 := hi; simp [← one_add_one_eq_two] at this

/-! ## Graph equations -/

section
variable (ι : Interp)

lemma G_func2 {ε n s t : V} (g : V) (hg : (ℒₒᵣ).IsFunc 2 g) (hs : IsUTerm ℒₒᵣ s)
    (ht : IsUTerm ℒₒᵣ t) :
    G ι ε n (^func 2 g (s ∷ t ∷ (0 : V))) =
      funcG ι ε n 2 g (G ι ε n s ∷ G ι ε n t ∷ (0 : V)) := by
  have hv : IsUTermVec ℒₒᵣ 2 (s ∷ t ∷ (0 : V)) := by simp [hs, ht]
  rw [G, (Graph.construction ι).result_func' hg hv]
  have h2 : (2 : V) = 1 + 1 := one_add_one_eq_two.symm
  have hv1 : IsUTermVec ℒₒᵣ 1 (t ∷ (0 : V)) := by
    simpa using (show IsUTermVec ℒₒᵣ (0 + 1) (t ∷ (0 : V)) from
      (show IsUTermVec ℒₒᵣ 0 (0 : V) by simp).adjoin ht)
  have e : (Graph.construction ι).resultVec ℒₒᵣ ![n, ε] 2 (s ∷ t ∷ (0 : V)) =
      G ι ε n s ∷ G ι ε n t ∷ (0 : V) := by
    rw [h2, (Graph.construction ι).resultVec_cons ℒₒᵣ _ (by simpa using hv1) hs]
    have e1 := (Graph.construction ι).resultVec_cons ℒₒᵣ ![n, ε]
      (show IsUTermVec ℒₒᵣ 0 (0 : V) by simp) ht
    simp only [zero_add] at e1
    rw [e1]; simp [G]
  rw [e]; rfl

lemma G_add {ε n s t : V} (hs : IsUTerm ℒₒᵣ s) (ht : IsUTerm ℒₒᵣ t) :
    G ι ε n (s ^+ t) = binG (tq ι.add) ε n (G ι ε n s) (G ι ε n t) := by
  unfold qqAdd
  rw [G_func2 ι _ (by simp) hs ht]
  simp [funcG]

lemma G_mul {ε n s t : V} (hs : IsUTerm ℒₒᵣ s) (ht : IsUTerm ℒₒᵣ t) :
    G ι ε n (s ^* t) = binG (tq ι.mul) ε n (G ι ε n s) (G ι ε n t) := by
  unfold qqMul
  rw [G_func2 ι _ (by simp) hs ht]
  simp [funcG, addIndex_ne_mulIndex.symm]

lemma G_zero (ε n : V) : G ι ε n (𝟎 : V) = un (tq ι.zero) (bs ε) ^#0 := by
  rw [qqZero_eq_qqFunc, G, (Graph.construction ι).result_func' (by simp) (by simp)]
  show funcG ι ε n 0 _ _ = _
  simp [funcG]

lemma G_one (ε n : V) : G ι ε n (𝟏 : V) = un (tq ι.one) (bs ε) ^#0 := by
  rw [qqOne_eq_qqFunc, G, (Graph.construction ι).result_func' (by simp) (by simp)]
  show funcG ι ε n 0 _ _ = _
  simp [funcG, zeroIndex_ne_oneIndex.symm]

/-- Every ℒₒᵣ term is a variable, a constant, a sum or a product. -/
lemma lor_term_cases {n t : V} (ht : IsSemiterm ℒₒᵣ n t) :
    (∃ z < n, t = ^#z) ∨ (∃ x, t = ^&x) ∨ t = 𝟎 ∨ t = 𝟏 ∨
      (∃ a b, IsSemiterm ℒₒᵣ n a ∧ IsSemiterm ℒₒᵣ n b ∧ t = a ^+ b) ∨
      (∃ a b, IsSemiterm ℒₒᵣ n a ∧ IsSemiterm ℒₒᵣ n b ∧ t = a ^* b) := by
  rcases IsSemiterm.case_iff.mp ht with h | h | ⟨k, f, v, hf, hv, rfl⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rcases lor_func_cases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · right; right; left; rw [qqZero_eq_qqFunc]; simp [show v = 0 by simpa using hv]
    · right; right; right; left; rw [qqOne_eq_qqFunc]; simp [show v = 0 by simpa using hv]
    · right; right; right; right; left
      refine ⟨v.[0], v.[1], hv.nth (by simp), hv.nth (by simp), ?_⟩
      unfold qqAdd; rw [vec2_eq' hv.lh]
    · right; right; right; right; right
      refine ⟨v.[0], v.[1], hv.nth (by simp), hv.nth (by simp), ?_⟩
      unfold qqMul; rw [vec2_eq' hv.lh]

end

lemma zero_lt_three' : (0 : V) < 3 := by
  rw [show (3 : V) = 0 + 1 + 1 + 1 by norm_num]; simp
lemma one_lt_three' : (1 : V) < 3 := by
  rw [show (3 : V) = 1 + 1 + 1 by norm_num]; simp
lemma two_lt_three' : (2 : V) < 3 := by
  rw [show (3 : V) = 2 + 1 by norm_num]; exact lt_add_one 2
lemma zero_lt_two' : (0 : V) < 2 := by simp

lemma lt_add_three {n a : V} (ha : a < 3) : a < n + 1 + 1 + 1 :=
  lt_of_lt_of_le ha (by
    rw [show n + 1 + 1 + 1 = n + 3 by rw [add_assoc, add_assoc]; norm_num]
    exact le_add_of_nonneg_left (by simp))

lemma lt_add_two {n a : V} (ha : a < 2) : a < n + 1 + 1 :=
  lt_of_lt_of_le ha (by
    rw [show n + 1 + 1 = n + 2 by rw [add_assoc, one_add_one_eq_two]]
    exact le_add_of_nonneg_left (by simp))

end ZF209.Internal.Arith
