module
public import Internal.Arith.Equations
@[expose] public section
/-! # Well-formedness, negation and shift for the arithmetic translation -/
namespace ZF207.Internal.Arith
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (ι : Interp)

lemma tq_semiformula' {k : ℕ} (φ : Semisentence ℒₛₑₜ k) {m : V} (h : (k : V) ≤ m) :
    IsSemiformula ℒₛₑₜ m (tq φ : V) := semiformula_mono (tq_semiformula φ) h

lemma eqAt_semiformula {m ε a b : V} (he : IsSemiterm ℒₛₑₜ m ε) (ha : IsSemiterm ℒₛₑₜ m a)
    (hb : IsSemiterm ℒₛₑₜ m b) : IsSemiformula ℒₛₑₜ m (eqAt ι ε a b) := by
  have h3 : IsSemiformula ℒₛₑₜ 3 (tq ι.eq : V) := by simpa using tq_semiformula (V := V) ι.eq
  exact h3.subst (m := m) (by
    rw [show (3 : V) = 0 + 1 + 1 + 1 by norm_num]
    simp [he, ha, hb])

lemma un_semiformula (φ : Semisentence ℒₛₑₜ 2) {m ε a : V} (he : IsSemiterm ℒₛₑₜ m ε)
    (ha : IsSemiterm ℒₛₑₜ m a) : IsSemiformula ℒₛₑₜ m (un (tq φ) ε a) := by
  have h2 : IsSemiformula ℒₛₑₜ 2 (tq φ : V) := by simpa using tq_semiformula (V := V) φ
  exact h2.subst (m := m) (by
    rw [show (2 : V) = 0 + 1 + 1 by simp [one_add_one_eq_two]]
    simp [he, ha])

lemma bs_semiterm {n ε : V} (he : IsSemiterm ℒₛₑₜ n ε) : IsSemiterm ℒₛₑₜ (n + 1) (bs ε) :=
  he.termBShift

lemma vec_bvar_cons {n m a w : V} (ha : a < m) (hw : IsSemitermVec ℒₛₑₜ n m w) :
    IsSemitermVec ℒₛₑₜ (n + 1) m (^#a ∷ w) := IsSemitermVec.cons_iff.mpr ⟨by simp [ha], hw⟩

lemma binG_semiformula (φ : Semisentence ℒₛₑₜ 4) {ε n a b : V} (he : IsSemiterm ℒₛₑₜ n ε)
    (ha : IsSemiformula ℒₛₑₜ (n + 1) a) (hb : IsSemiformula ℒₛₑₜ (n + 1) b) :
    IsSemiformula ℒₛₑₜ (n + 1) (binG (tq φ) ε n a b) := by
  have h4 : IsSemiformula ℒₛₑₜ 4 (tq φ : V) := by simpa using tq_semiformula (V := V) φ
  have hv := bv3_semitermVec n
  have e : n + 1 + 1 + 1 = n + 3 := by rw [add_assoc, add_assoc]; norm_num
  have l : IsSemitermVec ℒₛₑₜ (n + 1) (n + 1 + 1 + 1) (^#1 ∷ bv3 n) :=
    vec_bvar_cons (lt_add_three one_lt_three') (by rw [e]; exact hv)
  have r : IsSemitermVec ℒₛₑₜ (n + 1) (n + 1 + 1 + 1) (^#0 ∷ bv3 n) :=
    vec_bvar_cons (lt_add_three zero_lt_three') (by rw [e]; exact hv)
  have o : IsSemitermVec ℒₛₑₜ 4 (n + 1 + 1 + 1) (bs (bs (bs ε)) ∷ ^#1 ∷ ^#0 ∷ ^#2 ∷ (0 : V)) := by
    rw [show (4 : V) = 0 + 1 + 1 + 1 + 1 by norm_num]
    exact IsSemitermVec.cons_iff.mpr ⟨bs_semiterm (bs_semiterm (bs_semiterm he)),
      vec_bvar_cons (lt_add_three one_lt_three') (vec_bvar_cons (lt_add_three zero_lt_three')
      (vec_bvar_cons (lt_add_three two_lt_three') (by simp)))⟩
  simp only [binG, IsSemiformula.exs, IsSemiformula.and]
  exact ⟨⟨ha.subst l, hb.subst r⟩, h4.subst o⟩

lemma G_semiformula {ε n : V} (he : IsSemiterm ℒₛₑₜ n ε) :
    ∀ t, IsSemiterm ℒₒᵣ n t → IsSemiformula ℒₛₑₜ (n + 1) (G ι ε n t) := by
  refine IsSemiterm.induction 𝚷 (P := fun t => IsSemiformula ℒₛₑₜ (n + 1) (G ι ε n t)) ?_ ?_ ?_ ?_
  · definability
  · intro z hz
    simp only [G_bvar]
    exact eqAt_semiformula ι (bs_semiterm he) (by simp) (by simp [hz])
  · intro x
    simp only [G_fvar]
    exact eqAt_semiformula ι (bs_semiterm he) (by simp) (by simp)
  · intro k f v hf hv ih
    rcases lor_func_cases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have : v = 0 := by simpa using hv
      subst this
      rw [show (^func (0 : V) (zeroIndex : V) 0 : V) = 𝟎 by rw [qqZero_eq_qqFunc], G_zero]
      exact un_semiformula ι.zero (bs_semiterm he) (by simp)
    · have : v = 0 := by simpa using hv
      subst this
      rw [show (^func (0 : V) (oneIndex : V) 0 : V) = 𝟏 by rw [qqOne_eq_qqFunc], G_one]
      exact un_semiformula ι.one (bs_semiterm he) (by simp)
    · rw [← vec2_eq' hv.lh, show (^func (2 : V) (addIndex : V) (v.[0] ∷ v.[1] ∷ 0) : V) =
        v.[0] ^+ v.[1] by rfl, G_add ι (hv.nth (by simp)).isUTerm (hv.nth (by simp)).isUTerm]
      exact binG_semiformula ι.add he (ih 0 (by simp)) (ih 1 (by simp))
    · rw [← vec2_eq' hv.lh, show (^func (2 : V) (mulIndex : V) (v.[0] ∷ v.[1] ∷ 0) : V) =
        v.[0] ^* v.[1] by rfl, G_mul ι (hv.nth (by simp)).isUTerm (hv.nth (by simp)).isUTerm]
      exact binG_semiformula ι.mul he (ih 0 (by simp)) (ih 1 (by simp))

lemma relT_semiformula (R : V) {m : V} (hm : 3 ≤ m) : IsSemiformula ℒₛₑₜ m (relT ι R) := by
  unfold relT; split
  · exact tq_semiformula' ι.eq (by simpa using hm)
  · exact tq_semiformula' ι.lt (by simpa using hm)

lemma atomJ_semiformula {ε n R t₀ t₁ : V} (he : IsSemiterm ℒₛₑₜ n ε)
    (h₀ : IsSemiterm ℒₒᵣ n t₀) (h₁ : IsSemiterm ℒₒᵣ n t₁) :
    IsSemiformula ℒₛₑₜ n (atomJ ι ε n R t₀ t₁) := by
  have hv := bv2_semitermVec n
  have e : n + 1 + 1 = n + 2 := by rw [add_assoc, one_add_one_eq_two]
  have l : IsSemitermVec ℒₛₑₜ (n + 1) (n + 1 + 1) (^#1 ∷ bv2 n) :=
    vec_bvar_cons (lt_add_two one_lt_two) (by rw [e]; exact hv)
  have r : IsSemitermVec ℒₛₑₜ (n + 1) (n + 1 + 1) (^#0 ∷ bv2 n) :=
    vec_bvar_cons (lt_add_two zero_lt_two') (by rw [e]; exact hv)
  have o : IsSemitermVec ℒₛₑₜ 3 (n + 1 + 1) (bs (bs ε) ∷ ^#1 ∷ ^#0 ∷ (0 : V)) := by
    rw [show (3 : V) = 0 + 1 + 1 + 1 by norm_num]
    exact IsSemitermVec.cons_iff.mpr ⟨bs_semiterm (bs_semiterm he),
      vec_bvar_cons (lt_add_two one_lt_two) (vec_bvar_cons (lt_add_two zero_lt_two') (by simp))⟩
  have hR : IsSemiformula ℒₛₑₜ 3 (relT ι R) := relT_semiformula ι R le_rfl
  simp only [atomJ, IsSemiformula.exs, IsSemiformula.and]
  exact ⟨⟨(G_semiformula ι he t₀ h₀).subst l, (G_semiformula ι he t₁ h₁).subst r⟩, hR.subst o⟩

lemma rel_two_lor {k R : V} (h : (ℒₒᵣ).IsRel k R) : k = 2 := by
  have := isRel_iff_LOR.mp h
  rcases this with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl

theorem J_semiformula : ∀ n p : V, IsSemiformula ℒₒᵣ n p →
    ∀ ε, IsSemiterm ℒₛₑₜ n ε → IsSemiformula ℒₛₑₜ n (J ι ε n p) := by
  intro n p hp
  revert n p
  apply IsSemiformula.induction1 𝚷
    (P := fun n p => ∀ ε, IsSemiterm ℒₛₑₜ n ε → IsSemiformula ℒₛₑₜ n (J ι ε n p))
  · definability
  · intro n k r v hr hv ε he
    have := rel_two_lor hr; subst this
    simp only [J_rel hr hv.isUTerm]
    exact atomJ_semiformula ι he (hv.nth (by simp)) (hv.nth (by simp))
  · intro n k r v hr hv ε he
    have := rel_two_lor hr; subst this
    simp only [J_nrel hr hv.isUTerm, IsSemiformula.neg_iff]
    exact atomJ_semiformula ι he (hv.nth (by simp)) (hv.nth (by simp))
  · intro n ε _; simp
  · intro n ε _; simp
  · intro n p q hp hq ihp ihq ε he
    simp [J_and hp.isUFormula hq.isUFormula, ihp ε he, ihq ε he]
  · intro n p q hp hq ihp ihq ε he
    simp [J_or hp.isUFormula hq.isUFormula, ihp ε he, ihq ε he]
  · intro n p hp ih ε he
    simp only [J_all hp.isUFormula, IsSemiformula.all, IsSemiformula.or, IsSemiformula.neg_iff]
    exact ⟨un_semiformula ι.dom (bs_semiterm he) (by simp), ih _ (bs_semiterm he)⟩
  · intro n p hp ih ε he
    simp only [J_exs hp.isUFormula, IsSemiformula.exs, IsSemiformula.and]
    exact ⟨un_semiformula ι.dom (bs_semiterm he) (by simp), ih _ (bs_semiterm he)⟩

end ZF207.Internal.Arith
