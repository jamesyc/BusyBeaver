module
public import Internal.Arith.WellFormed
@[expose] public section
/-! # The arithmetic translation commutes with negation and shift -/
namespace ZF207.Internal.Arith
open I0451.Logic (set_isRel set_no_func set_term_cases)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (ι : Interp)

/-! ## Negation -/

theorem J_neg : ∀ n p : V, IsSemiformula ℒₒᵣ n p → ∀ ε, IsSemiterm ℒₛₑₜ n ε →
    J ι ε n (neg ℒₒᵣ p) = neg ℒₛₑₜ (J ι ε n p) := by
  intro n p hp
  revert n p
  apply IsSemiformula.induction1 𝚷 (P := fun n p => ∀ ε, IsSemiterm ℒₛₑₜ n ε →
    J ι ε n (neg ℒₒᵣ p) = neg ℒₛₑₜ (J ι ε n p))
  · definability
  · intro n k r v hr hv ε he
    simp [hr, hv.isUTerm]
  · intro n k r v hr hv ε he
    have := rel_two_lor hr; subst this
    have ha := (atomJ_semiformula ι (R := r) he (hv.nth zero_lt_two') (hv.nth one_lt_two)).isUFormula
    simp [hr, hv.isUTerm, ha]
  · intro n ε _; simp
  · intro n ε _; simp
  · intro n p q hp hq ihp ihq ε he
    simp [hp.isUFormula, hq.isUFormula, hp.isUFormula.neg, hq.isUFormula.neg, ihp ε he, ihq ε he,
      (J_semiformula ι n p hp ε he).isUFormula, (J_semiformula ι n q hq ε he).isUFormula]
  · intro n p q hp hq ihp ihq ε he
    simp [hp.isUFormula, hq.isUFormula, hp.isUFormula.neg, hq.isUFormula.neg, ihp ε he, ihq ε he,
      (J_semiformula ι n p hp ε he).isUFormula, (J_semiformula ι n q hq ε he).isUFormula]
  · intro n p hp ih ε he
    have hd := (un_semiformula (V := V) ι.dom (bs_semiterm he) (a := ^#0) (by simp)).isUFormula
    simp [hp.isUFormula, hp.isUFormula.neg, ih _ (bs_semiterm he), hd,
      (J_semiformula ι _ p hp _ (bs_semiterm he)).isUFormula]
  · intro n p hp ih ε he
    have hd := (un_semiformula (V := V) ι.dom (bs_semiterm he) (a := ^#0) (by simp)).isUFormula
    simp [hp.isUFormula, hp.isUFormula.neg, ih _ (bs_semiterm he), hd,
      (J_semiformula ι _ p hp _ (bs_semiterm he)).isUFormula]

/-! ## Shift -/

lemma termShiftVec_of_bvars {k w : V} (hw : IsUTermVec ℒₛₑₜ k w)
    (h : ∀ i < k, ∃ z, w.[i] = ^#z) : termShiftVec ℒₛₑₜ k w = w := by
  apply nth_ext' k (by simp [hw]) hw.lh.symm
  intro i hi
  obtain ⟨z, hz⟩ := h i hi
  rw [nth_termShiftVec hw hi, hz]; simp

lemma bvars_cons {k z w : V} (h : ∀ i < k, ∃ z, w.[i] = ^#z) :
    ∀ i < k + 1, ∃ z', (^#z ∷ w).[i] = ^#z' := by
  intro i hi
  rcases zero_or_succ i with rfl | ⟨i, rfl⟩
  · exact ⟨z, by simp⟩
  · simpa using h i (by simpa using hi)

lemma bv3_bvars (n : V) : ∀ i < n, ∃ z, (bv3 n).[i] = ^#z := fun _ hi => ⟨_, nth_bv3 hi⟩
lemma bv2_bvars (n : V) : ∀ i < n, ∃ z, (bv2 n).[i] = ^#z := fun _ hi => ⟨_, nth_bv2 hi⟩

lemma shift_subst_bvars {k m w p : V} (hp : IsSemiformula ℒₛₑₜ k p) (hw : IsSemitermVec ℒₛₑₜ k m w)
    (h : ∀ i < k, ∃ z, w.[i] = ^#z) :
    shift ℒₛₑₜ (subst ℒₛₑₜ w p) = subst ℒₛₑₜ w (shift ℒₛₑₜ p) := by
  rw [shift_substs hp hw, termShiftVec_of_bvars hw.isUTerm h]

lemma termShiftVec_cons_bvars {k t w : V} (ht : IsUTerm ℒₛₑₜ t) (hw : IsUTermVec ℒₛₑₜ k w)
    (h : ∀ i < k, ∃ z, w.[i] = ^#z) :
    termShiftVec ℒₛₑₜ (k + 1) (t ∷ w) = termShift ℒₛₑₜ t ∷ w := by
  rw [termShiftVec_cons ht hw, termShiftVec_of_bvars hw h]

lemma shift_bs {n ε : V} (he : IsSemiterm ℒₛₑₜ n ε) :
    termShift ℒₛₑₜ (bs ε) = bs (termShift ℒₛₑₜ ε) := (termBShift_termShift he).symm

lemma bs_shift_semiterm {n ε : V} (he : IsSemiterm ℒₛₑₜ n ε) :
    IsSemiterm ℒₛₑₜ n (termShift ℒₛₑₜ ε) := he.termShift

lemma shift_binG (φ : Semisentence ℒₛₑₜ 4) {ε n a b : V} (he : IsSemiterm ℒₛₑₜ n ε)
    (ha : IsSemiformula ℒₛₑₜ (n + 1) a) (hb : IsSemiformula ℒₛₑₜ (n + 1) b) :
    shift ℒₛₑₜ (binG (tq φ) ε n a b) =
      binG (tq φ) (termShift ℒₛₑₜ ε) n (shift ℒₛₑₜ a) (shift ℒₛₑₜ b) := by
  have h4 : IsSemiformula ℒₛₑₜ 4 (tq φ : V) := by simpa using tq_semiformula (V := V) φ
  have hv := bv3_semitermVec n
  have e : n + 1 + 1 + 1 = n + 3 := by rw [add_assoc, add_assoc]; norm_num
  have l : IsSemitermVec ℒₛₑₜ (n + 1) (n + 1 + 1 + 1) (^#1 ∷ bv3 n) :=
    vec_bvar_cons (lt_add_three one_lt_three') (by rw [e]; exact hv)
  have r : IsSemitermVec ℒₛₑₜ (n + 1) (n + 1 + 1 + 1) (^#0 ∷ bv3 n) :=
    vec_bvar_cons (lt_add_three zero_lt_three') (by rw [e]; exact hv)
  have he3 := bs_semiterm (bs_semiterm (bs_semiterm he))
  have o₃ : IsSemitermVec ℒₛₑₜ 3 (n + 1 + 1 + 1) (^#1 ∷ ^#0 ∷ ^#2 ∷ (0 : V)) := by
    rw [show (3 : V) = 0 + 1 + 1 + 1 by norm_num]
    exact vec_bvar_cons (lt_add_three one_lt_three') (vec_bvar_cons (lt_add_three zero_lt_three')
      (vec_bvar_cons (lt_add_three two_lt_three') (by simp)))
  have o : IsSemitermVec ℒₛₑₜ 4 (n + 1 + 1 + 1) (bs (bs (bs ε)) ∷ ^#1 ∷ ^#0 ∷ ^#2 ∷ (0 : V)) := by
    rw [show (4 : V) = 3 + 1 by norm_num]
    exact IsSemitermVec.cons_iff.mpr ⟨he3, o₃⟩
  have bl := bvars_cons (z := 1) (bv3_bvars n)
  have br := bvars_cons (z := 0) (bv3_bvars n)
  have bo : ∀ i < 3, ∃ z, (^#1 ∷ ^#0 ∷ ^#2 ∷ (0 : V)).[i] = ^#z := by
    rw [show (3 : V) = 0 + 1 + 1 + 1 by norm_num]
    exact bvars_cons (bvars_cons (bvars_cons (fun i hi => by simp at hi)))
  have hsa := (ha.subst l).isUFormula
  have hsb := (hb.subst r).isUFormula
  have hso := (h4.subst o).isUFormula
  simp only [binG]
  rw [shift_exs (by simp [hsa, hsb, hso]), shift_exs (by simp [hsa, hsb, hso]),
    shift_and (by simp [hsa, hsb]) hso, shift_and hsa hsb, shift_subst_bvars ha l bl,
    shift_subst_bvars hb r br, shift_substs h4 o, shift_tq,
    show (4 : V) = 3 + 1 by norm_num, termShiftVec_cons_bvars he3.isUTerm o₃.isUTerm bo,
    shift_bs (bs_semiterm (bs_semiterm he)), shift_bs (bs_semiterm he), shift_bs he]

lemma shift_eqAt {m ε a b : V} (he : IsSemiterm ℒₛₑₜ m ε) (ha : IsSemiterm ℒₛₑₜ m a)
    (hb : IsSemiterm ℒₛₑₜ m b) :
    shift ℒₛₑₜ (eqAt ι ε a b) =
      eqAt ι (termShift ℒₛₑₜ ε) (termShift ℒₛₑₜ a) (termShift ℒₛₑₜ b) := by
  have h3 : IsSemiformula ℒₛₑₜ 3 (tq ι.eq : V) := by simpa using tq_semiformula (V := V) ι.eq
  have hw : IsSemitermVec ℒₛₑₜ 3 m (ε ∷ a ∷ b ∷ (0 : V)) := by
    rw [show (3 : V) = 0 + 1 + 1 + 1 by norm_num]; simp [he, ha, hb]
  have hw2 : IsUTermVec ℒₛₑₜ 2 (a ∷ b ∷ (0 : V)) := by simp [ha.isUTerm, hb.isUTerm]
  unfold eqAt
  rw [shift_substs h3 hw, shift_tq, show (3 : V) = 2 + 1 by norm_num,
    termShiftVec_cons he.isUTerm hw2, termShiftVec_cons₂ ha.isUTerm hb.isUTerm]

lemma shift_un (φ : Semisentence ℒₛₑₜ 2) {m ε a : V} (he : IsSemiterm ℒₛₑₜ m ε)
    (ha : IsSemiterm ℒₛₑₜ m a) :
    shift ℒₛₑₜ (un (tq φ) ε a) = un (tq φ) (termShift ℒₛₑₜ ε) (termShift ℒₛₑₜ a) := by
  have h2 : IsSemiformula ℒₛₑₜ 2 (tq φ : V) := by simpa using tq_semiformula (V := V) φ
  have hw : IsSemitermVec ℒₛₑₜ 2 m (ε ∷ a ∷ (0 : V)) := by
    rw [show (2 : V) = 0 + 1 + 1 by simp [one_add_one_eq_two]]; simp [he, ha]
  unfold un
  rw [shift_substs h2 hw, shift_tq, termShiftVec_cons₂ he.isUTerm ha.isUTerm]

lemma termShift_add {a b : V} (ha : IsUTerm ℒₒᵣ a) (hb : IsUTerm ℒₒᵣ b) :
    termShift ℒₒᵣ (a ^+ b) = termShift ℒₒᵣ a ^+ termShift ℒₒᵣ b := by
  unfold qqAdd
  rw [termShift_func (by simp) (by simp [ha, hb]), termShiftVec_cons₂ ha hb]

lemma termShift_mul {a b : V} (ha : IsUTerm ℒₒᵣ a) (hb : IsUTerm ℒₒᵣ b) :
    termShift ℒₒᵣ (a ^* b) = termShift ℒₒᵣ a ^* termShift ℒₒᵣ b := by
  unfold qqMul
  rw [termShift_func (by simp) (by simp [ha, hb]), termShiftVec_cons₂ ha hb]

lemma termShift_zero : termShift ℒₒᵣ (𝟎 : V) = 𝟎 := by
  rw [qqZero_eq_qqFunc, termShift_func (by simp) (by simp)]; simp

lemma termShift_one : termShift ℒₒᵣ (𝟏 : V) = 𝟏 := by
  rw [qqOne_eq_qqFunc, termShift_func (by simp) (by simp)]; simp

lemma shift_G {ε n : V} (he : IsSemiterm ℒₛₑₜ n ε) : ∀ t, IsSemiterm ℒₒᵣ n t →
    shift ℒₛₑₜ (G ι ε n t) = G ι (termShift ℒₛₑₜ ε) n (termShift ℒₒᵣ t) := by
  refine IsSemiterm.induction 𝚷
    (P := fun t => shift ℒₛₑₜ (G ι ε n t) = G ι (termShift ℒₛₑₜ ε) n (termShift ℒₒᵣ t)) ?_ ?_ ?_ ?_
  · definability
  · intro z hz
    simp [shift_eqAt ι (m := n + 1) (a := ^#0) (b := ^#(z + 1)) (bs_semiterm he) (by simp)
      (by simp [hz]), shift_bs he]
  · intro x
    simp [shift_eqAt ι (m := n + 1) (a := ^#0) (b := ^&x) (bs_semiterm he) (by simp) (by simp),
      shift_bs he]
  · intro k f v hf hv ih
    rcases lor_func_cases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have : v = 0 := by simpa using hv
      subst this
      rw [show (^func (0 : V) (zeroIndex : V) 0 : V) = 𝟎 by rw [qqZero_eq_qqFunc], G_zero,
        termShift_zero, G_zero, shift_un ι.zero (bs_semiterm he) (show IsSemiterm ℒₛₑₜ (n + 1) ^#0
          by simp), shift_bs he]
      simp
    · have : v = 0 := by simpa using hv
      subst this
      rw [show (^func (0 : V) (oneIndex : V) 0 : V) = 𝟏 by rw [qqOne_eq_qqFunc], G_one,
        termShift_one, G_one, shift_un ι.one (bs_semiterm he) (show IsSemiterm ℒₛₑₜ (n + 1) ^#0
          by simp), shift_bs he]
      simp
    · have h0 := hv.nth zero_lt_two'
      have h1 := hv.nth one_lt_two
      rw [← vec2_eq' hv.lh, show (^func (2 : V) (addIndex : V) (v.[0] ∷ v.[1] ∷ 0) : V) =
        v.[0] ^+ v.[1] by rfl, G_add ι h0.isUTerm h1.isUTerm, termShift_add h0.isUTerm h1.isUTerm,
        G_add ι h0.isUTerm.termShift h1.isUTerm.termShift,
        shift_binG ι.add he (G_semiformula ι he _ h0) (G_semiformula ι he _ h1),
        ih 0 zero_lt_two', ih 1 one_lt_two]
    · have h0 := hv.nth zero_lt_two'
      have h1 := hv.nth one_lt_two
      rw [← vec2_eq' hv.lh, show (^func (2 : V) (mulIndex : V) (v.[0] ∷ v.[1] ∷ 0) : V) =
        v.[0] ^* v.[1] by rfl, G_mul ι h0.isUTerm h1.isUTerm, termShift_mul h0.isUTerm h1.isUTerm,
        G_mul ι h0.isUTerm.termShift h1.isUTerm.termShift,
        shift_binG ι.mul he (G_semiformula ι he _ h0) (G_semiformula ι he _ h1),
        ih 0 zero_lt_two', ih 1 one_lt_two]

lemma shift_relT (R : V) : shift ℒₛₑₜ (relT ι R) = relT ι R := by
  unfold relT; split <;> simp

lemma shift_atomJ {ε n R t₀ t₁ : V} (he : IsSemiterm ℒₛₑₜ n ε) (h₀ : IsSemiterm ℒₒᵣ n t₀)
    (h₁ : IsSemiterm ℒₒᵣ n t₁) :
    shift ℒₛₑₜ (atomJ ι ε n R t₀ t₁) =
      atomJ ι (termShift ℒₛₑₜ ε) n R (termShift ℒₒᵣ t₀) (termShift ℒₒᵣ t₁) := by
  have hv := bv2_semitermVec n
  have e : n + 1 + 1 = n + 2 := by rw [add_assoc, one_add_one_eq_two]
  have l : IsSemitermVec ℒₛₑₜ (n + 1) (n + 1 + 1) (^#1 ∷ bv2 n) :=
    vec_bvar_cons (lt_add_two one_lt_two) (by rw [e]; exact hv)
  have r : IsSemitermVec ℒₛₑₜ (n + 1) (n + 1 + 1) (^#0 ∷ bv2 n) :=
    vec_bvar_cons (lt_add_two zero_lt_two') (by rw [e]; exact hv)
  have he2 := bs_semiterm (bs_semiterm he)
  have o₂ : IsSemitermVec ℒₛₑₜ 2 (n + 1 + 1) (^#1 ∷ ^#0 ∷ (0 : V)) := by
    rw [show (2 : V) = 0 + 1 + 1 by simp [one_add_one_eq_two]]
    exact vec_bvar_cons (lt_add_two one_lt_two) (vec_bvar_cons (lt_add_two zero_lt_two') (by simp))
  have o : IsSemitermVec ℒₛₑₜ 3 (n + 1 + 1) (bs (bs ε) ∷ ^#1 ∷ ^#0 ∷ (0 : V)) := by
    rw [show (3 : V) = 2 + 1 by norm_num]
    exact IsSemitermVec.cons_iff.mpr ⟨he2, o₂⟩
  have bl := bvars_cons (z := 1) (bv2_bvars n)
  have br := bvars_cons (z := 0) (bv2_bvars n)
  have bo : ∀ i < 2, ∃ z, (^#1 ∷ ^#0 ∷ (0 : V)).[i] = ^#z := by
    rw [show (2 : V) = 0 + 1 + 1 by simp [one_add_one_eq_two]]
    exact bvars_cons (bvars_cons (fun i hi => by simp at hi))
  have hR : IsSemiformula ℒₛₑₜ 3 (relT ι R) := relT_semiformula ι R le_rfl
  have g₀ := G_semiformula ι he t₀ h₀
  have g₁ := G_semiformula ι he t₁ h₁
  have hsa := (g₀.subst l).isUFormula
  have hsb := (g₁.subst r).isUFormula
  have hso := (hR.subst o).isUFormula
  simp only [atomJ]
  rw [shift_exs (by simp [hsa, hsb, hso]), shift_exs (by simp [hsa, hsb, hso]),
    shift_and (by simp [hsa, hsb]) hso, shift_and hsa hsb, shift_subst_bvars g₀ l bl,
    shift_subst_bvars g₁ r br, shift_substs hR o, shift_relT,
    show (3 : V) = 2 + 1 by norm_num, termShiftVec_cons_bvars he2.isUTerm o₂.isUTerm bo,
    shift_bs (bs_semiterm he), shift_bs he, shift_G ι he t₀ h₀, shift_G ι he t₁ h₁]

theorem J_shift : ∀ n p : V, IsSemiformula ℒₒᵣ n p → ∀ ε, IsSemiterm ℒₛₑₜ n ε →
    J ι (termShift ℒₛₑₜ ε) n (shift ℒₒᵣ p) = shift ℒₛₑₜ (J ι ε n p) := by
  intro n p hp
  revert n p
  apply IsSemiformula.induction1 𝚷 (P := fun n p => ∀ ε, IsSemiterm ℒₛₑₜ n ε →
    J ι (termShift ℒₛₑₜ ε) n (shift ℒₒᵣ p) = shift ℒₛₑₜ (J ι ε n p))
  · definability
  · intro n k r v hr hv ε he
    have := rel_two_lor hr; subst this
    have h0 := hv.nth zero_lt_two'
    have h1 := hv.nth one_lt_two
    rw [shift_rel hr hv.isUTerm, J_rel hr hv.isUTerm.termShiftVec, J_rel hr hv.isUTerm,
      shift_atomJ ι he h0 h1, nth_termShiftVec hv.isUTerm zero_lt_two',
      nth_termShiftVec hv.isUTerm one_lt_two]
  · intro n k r v hr hv ε he
    have := rel_two_lor hr; subst this
    have h0 := hv.nth zero_lt_two'
    have h1 := hv.nth one_lt_two
    rw [shift_nrel hr hv.isUTerm, J_nrel hr hv.isUTerm.termShiftVec, J_nrel hr hv.isUTerm,
      shift_neg (atomJ_semiformula ι he h0 h1), shift_atomJ ι he h0 h1,
      nth_termShiftVec hv.isUTerm zero_lt_two', nth_termShiftVec hv.isUTerm one_lt_two]
  · intro n ε _; simp
  · intro n ε _; simp
  · intro n p q hp hq ihp ihq ε he
    rw [shift_and hp.isUFormula hq.isUFormula, J_and hp.isUFormula.shift hq.isUFormula.shift,
      J_and hp.isUFormula hq.isUFormula, ihp ε he, ihq ε he,
      shift_and (J_semiformula ι n p hp ε he).isUFormula (J_semiformula ι n q hq ε he).isUFormula]
  · intro n p q hp hq ihp ihq ε he
    rw [shift_or hp.isUFormula hq.isUFormula, J_or hp.isUFormula.shift hq.isUFormula.shift,
      J_or hp.isUFormula hq.isUFormula, ihp ε he, ihq ε he,
      shift_or (J_semiformula ι n p hp ε he).isUFormula (J_semiformula ι n q hq ε he).isUFormula]
  · intro n p hp ih ε he
    have hd := un_semiformula (V := V) ι.dom (bs_semiterm he) (a := ^#0) (by simp)
    have hj := J_semiformula ι _ p hp _ (bs_semiterm he)
    rw [shift_all hp.isUFormula, J_all hp.isUFormula.shift, J_all hp.isUFormula, ← shift_bs he,
      ih _ (bs_semiterm he), shift_all (by simp [hd.isUFormula, hj.isUFormula]),
      shift_or (by simp [hd.isUFormula]) hj.isUFormula, shift_neg hd,
      shift_un ι.dom (bs_semiterm he) (show IsSemiterm ℒₛₑₜ (n + 1) ^#0 by simp)]
    simp
  · intro n p hp ih ε he
    have hd := un_semiformula (V := V) ι.dom (bs_semiterm he) (a := ^#0) (by simp)
    have hj := J_semiformula ι _ p hp _ (bs_semiterm he)
    rw [shift_exs hp.isUFormula, J_exs hp.isUFormula.shift, J_exs hp.isUFormula, ← shift_bs he,
      ih _ (bs_semiterm he), shift_exs (by simp [hd.isUFormula, hj.isUFormula]),
      shift_and hd.isUFormula hj.isUFormula,
      shift_un ι.dom (bs_semiterm he) (show IsSemiterm ℒₛₑₜ (n + 1) ^#0 by simp)]
    simp

end ZF207.Internal.Arith
