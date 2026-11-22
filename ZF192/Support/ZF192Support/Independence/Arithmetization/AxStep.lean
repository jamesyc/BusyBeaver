module
public import ZF192Support.Independence.Arithmetization.Closing
@[expose] public section
/-! # Translated axioms from marker-closed axioms

The axiom of `U` for an axiom `σ` of `T` is `∀e (Mark e → Ĵσ)`, where `Ĵσ = J ι (#0) 1 σ`
translates `σ` with the marker as a bound variable. Instantiating `e` by a free-variable
marker `ε` gives `¬Mark ε ∨ J ι ε 0 σ` (`J_subst` on the marker slot). With Craig padding
`σ ⋏ ⊤ⁿ` the padding translates to `⊤ⁿ`, which is derivable. -/
namespace ZF192Support.Internal.Arith
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (ι : Interp)

/-- The marker-closed translation of a sentence. -/
noncomputable def jhat (σ : V) : V := J ι (^#0) 1 σ

/-- The axiom of `U` for `σ`: `∀e (Mark e → Ĵσ)`. -/
noncomputable def kax (σ : V) : V := ^∀ imp ℒₛₑₜ (markAt ι (^#0)) (jhat ι σ)

lemma subst_closed_lor {p m u : V} (hp : IsFormula ℒₒᵣ p) (hu : IsSemitermVec ℒₒᵣ 1 m u) :
    subst ℒₒᵣ u p = p := by
  have e0 : subst ℒₒᵣ 0 p = p := subst_eq_self hp (by simp) (by simp)
  calc subst ℒₒᵣ u p = subst ℒₒᵣ u (subst ℒₒᵣ 0 p) := by rw [e0]
    _ = subst ℒₒᵣ (termSubstVec ℒₒᵣ 0 u 0) p := substs_substs hp hu (by simp)
    _ = p := by simp [e0]

lemma vec_closed {ε : V} (he : IsSemiterm ℒₛₑₜ 0 ε) : IsSemitermVec ℒₛₑₜ 1 0 (ε ∷ (0 : V)) := by
  rw [show (1 : V) = 0 + 1 by simp]; simp [he]

lemma vec_closed_lor {ε : V} (he : IsSemiterm ℒₛₑₜ 0 ε) : IsSemitermVec ℒₒᵣ 1 0 (ε ∷ (0 : V)) := by
  rcases set_term_cases.mp he with ⟨z, hz, _⟩ | ⟨x, rfl⟩
  · simp at hz
  · rw [show (1 : V) = 0 + 1 by simp]; simp

lemma varVec_closed {ε : V} (he : IsSemiterm ℒₛₑₜ 0 ε) : VarVec 1 (ε ∷ (0 : V)) :=
  varVec_of_set (vec_closed he)

lemma jhat_subst {σ ε : V} (hσ : IsFormula ℒₒᵣ σ) (he : IsSemiterm ℒₛₑₜ 0 ε) :
    subst ℒₛₑₜ (ε ∷ (0 : V)) (jhat ι σ) = J ι ε 0 σ := by
  have hσ1 : IsSemiformula ℒₒᵣ 1 σ := ⟨hσ.isUFormula, le_trans hσ.bv_le (by simp)⟩
  have h := J_subst ι 1 σ hσ1 (^#0) (by simp) 0 (ε ∷ 0) (vec_closed_lor he) (varVec_closed he)
  rw [subst_closed_lor hσ (vec_closed_lor he)] at h
  simpa [jhat] using h.symm

lemma markAt_subst {ε : V} (he : IsSemiterm ℒₛₑₜ 0 ε) :
    subst ℒₛₑₜ (ε ∷ (0 : V)) (markAt ι (^#0)) = markAt ι ε := by
  have h1 : IsSemiformula ℒₛₑₜ 1 (tq ι.mark : V) := by simpa using tq_semiformula (V := V) ι.mark
  have hw₁ : IsSemitermVec ℒₛₑₜ 1 1 (^#0 ∷ (0 : V)) := by
    rw [show (1 : V) = 0 + 1 by simp]; simp
  unfold markAt
  rw [substs_substs h1 (vec_closed he) hw₁, show (1 : V) = 0 + 1 by simp,
    termSubstVec_cons (by simp) (by simp)]
  simp

lemma jhat_semiformula {σ : V} (hσ : IsFormula ℒₒᵣ σ) : IsSemiformula ℒₛₑₜ 1 (jhat ι σ) :=
  J_semiformula ι 1 σ ⟨hσ.isUFormula, le_trans hσ.bv_le (by simp)⟩ _ (by simp)

/-- `⊤ⁿ` translates to itself. -/
lemma J_verums (ε n : V) : ∀ k : V, J ι ε n (qqVerums k) = qqVerums k := by
  intro k
  induction k using ISigma1.sigma1_succ_induction
  · definability
  · simp
  · rename_i k ih
    have hv : IsUFormula ℒₒᵣ (qqVerums k) := (IsSemiformula.qqVerums (n := 0) k).isUFormula
    rw [qqVerums_succ, J_and (IsUFormula.verum (L := ℒₒᵣ)) hv, J_verum, ih]

end

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (ι : Interp)
variable {U : Theory ℒₛₑₜ} [U.Δ₁]

lemma pair_formulaSet {a b : V} (ha : IsFormula ℒₛₑₜ a) (hb : IsFormula ℒₛₑₜ b) :
    IsFormulaSet ℒₛₑₜ (insert a (insert b (0 : V))) := by
  intro y hy
  rcases mem_bitInsert_iff.mp hy with rfl | hy
  · exact ha
  · exact singleton_formulaSet hb y hy

/-- From a derivation of `∀e (Mark e → Ĵσ)` in context, `U` derives `¬Mark ε ∨ J ε σ`. -/
theorem derivable_of_kax' {σ ε : V} (hσ : IsFormula ℒₒᵣ σ) (he : IsSemiterm ℒₛₑₜ 0 ε)
    (d₁ : Derivable U (insert (kax ι σ) (insert (neg ℒₛₑₜ (markAt ι ε))
      (insert (J ι ε 0 σ) (0 : V))))) :
    Derivable U (insert (neg ℒₛₑₜ (markAt ι ε)) (insert (J ι ε 0 σ) (0 : V))) := by
  have hm1 : IsSemiformula ℒₛₑₜ 1 (markAt ι (^#0 : V)) := markAt_semiformula ι (by simp)
  have hj1 := jhat_semiformula ι hσ
  have hφ : IsSemiformula ℒₛₑₜ 1 (imp ℒₛₑₜ (markAt ι (^#0)) (jhat ι σ)) := by simp [hm1, hj1]
  have hM : IsFormula ℒₛₑₜ (markAt ι ε) := markAt_semiformula ι he
  have hJ : IsFormula ℒₛₑₜ (J ι ε 0 σ) := J_semiformula ι 0 σ hσ ε he
  have hS : IsFormulaSet ℒₛₑₜ (insert (neg ℒₛₑₜ (markAt ι ε)) (insert (J ι ε 0 σ) (0 : V))) :=
    pair_formulaSet (IsSemiformula.neg_iff.mpr hM) hJ
  have hsub : substs1 ℒₛₑₜ ε (neg ℒₛₑₜ (imp ℒₛₑₜ (markAt ι (^#0)) (jhat ι σ))) =
      markAt ι ε ^⋏ neg ℒₛₑₜ (J ι ε 0 σ) := by
    rw [substs1, substs_neg hφ (vec_closed he), imp, substs_or (by simp [hm1.isUFormula])
      hj1.isUFormula, substs_neg hm1 (vec_closed he), markAt_subst ι he, jhat_subst ι hσ he]
    simp [hM.isUFormula, hJ.isUFormula, hM.isUFormula.neg_neg]
  -- its negation is refuted by instantiating at `ε`
  have d₂ : Derivable U (insert (neg ℒₛₑₜ (kax ι σ)) (insert (neg ℒₛₑₜ (markAt ι ε))
      (insert (J ι ε 0 σ) (0 : V)))) := by
    have hnk : neg ℒₛₑₜ (kax ι σ) = ^∃ neg ℒₛₑₜ (imp ℒₛₑₜ (markAt ι (^#0)) (jhat ι σ)) := by
      simp [kax, hφ.isUFormula]
    rw [hnk]
    refine Derivable.exs (t := ε) (IsSemiformula.neg_iff.mpr hφ) (by simpa using he) ?_
    rw [hsub]
    have hS₂ : IsFormulaSet ℒₛₑₜ (insert (markAt ι ε ^⋏ neg ℒₛₑₜ (J ι ε 0 σ))
        (insert (neg ℒₛₑₜ (markAt ι ε)) (insert (J ι ε 0 σ) (0 : V)))) := by
      intro y hy
      rcases mem_bitInsert_iff.mp hy with rfl | hy
      · simp [hM, hJ]
      · exact hS y hy
    refine Derivable.and_m (p := markAt ι ε) (q := neg ℒₛₑₜ (J ι ε 0 σ)) (by simp) ?_ ?_
    · refine Derivable.em ?_ (markAt ι ε) (by simp) (by simp)
      intro y hy
      rcases mem_bitInsert_iff.mp hy with rfl | hy
      · exact hM
      · exact hS₂ y hy
    · refine Derivable.em ?_ (J ι ε 0 σ) (by simp) (by simp [hJ.isUFormula.neg_neg])
      intro y hy
      rcases mem_bitInsert_iff.mp hy with rfl | hy
      · exact IsSemiformula.neg_iff.mpr hJ
      · exact hS₂ y hy
  exact Derivable.cut (kax ι σ) d₁ d₂

lemma kax_formula {σ : V} (hσ : IsFormula ℒₒᵣ σ) : IsFormula ℒₛₑₜ (kax ι σ) := by
  have hm1 : IsSemiformula ℒₛₑₜ 1 (markAt ι (^#0 : V)) := markAt_semiformula ι (by simp)
  have hj1 := jhat_semiformula ι hσ
  have hφ : IsSemiformula ℒₛₑₜ 1 (imp ℒₛₑₜ (markAt ι (^#0)) (jhat ι σ)) := by simp [hm1, hj1]
  simpa [kax] using hφ

/-- From the axiom `∀e (Mark e → Ĵσ)`, `U` derives `¬Mark ε ∨ J ε σ`. -/
theorem derivable_of_kax {σ ε : V} (hσ : IsFormula ℒₒᵣ σ) (he : IsSemiterm ℒₛₑₜ 0 ε)
    (hK : kax ι σ ∈ U.Δ₁Class) :
    Derivable U (insert (neg ℒₛₑₜ (markAt ι ε)) (insert (J ι ε 0 σ) (0 : V))) := by
  have hM : IsFormula ℒₛₑₜ (markAt ι ε) := markAt_semiformula ι he
  have hJ : IsFormula ℒₛₑₜ (J ι ε 0 σ) := J_semiformula ι 0 σ hσ ε he
  have hS : IsFormulaSet ℒₛₑₜ (insert (neg ℒₛₑₜ (markAt ι ε)) (insert (J ι ε 0 σ) (0 : V))) :=
    pair_formulaSet (IsSemiformula.neg_iff.mpr hM) hJ
  refine derivable_of_kax' ι hσ he (Derivable.by_axm ?_ _ (by simp) hK)
  intro y hy
  rcases mem_bitInsert_iff.mp hy with rfl | hy
  · exact kax_formula ι hσ
  · exact hS y hy

end

end ZF192Support.Internal.Arith
