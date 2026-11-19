module
public import Internal.Arith.ExStep
@[expose] public section
/-! # Closing off the marker

`stage_one` leaves a `U`-derivation of `¬Mark &x`. A one-formula sequent `{shift θ}` gives
`{θ}` (quantify the unused variable vacuously, then instantiate), so `¬Mark &x` descends to
`¬Mark &0`; then `∀e ¬Mark e` and the axiom `∃e Mark e` refute `U`. -/
namespace ZF207.Internal.Arith
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma subst_closed_fml {p m u : V} (hp : IsFormula ℒₛₑₜ p) (hu : IsSemitermVec ℒₛₑₜ 1 m u) :
    subst ℒₛₑₜ u p = p := by
  have e0 : subst ℒₛₑₜ 0 p = p := subst_eq_self hp (by simp) (by simp)
  calc subst ℒₛₑₜ u p = subst ℒₛₑₜ u (subst ℒₛₑₜ 0 p) := by rw [e0]
    _ = subst ℒₛₑₜ (termSubstVec ℒₛₑₜ 0 u 0) p := substs_substs hp hu (by simp)
    _ = p := by simp [e0]

lemma singleton_formulaSet {p : V} (hp : IsFormula ℒₛₑₜ p) : IsFormulaSet ℒₛₑₜ (insert p (0 : V)) := by
  intro y hy
  rcases mem_bitInsert_iff.mp hy with rfl | hy
  · exact hp
  · simp at hy

lemma setShift_zero : setShift ℒₛₑₜ (0 : V) = 0 :=
  mem_ext fun y => by simp [mem_setShift_iff]

variable {U : Theory ℒₛₑₜ} [U.Δ₁]

/-- `{shift θ}` gives `{θ}`. -/
lemma unshift₁ {θ : V} (hθ : IsFormula ℒₛₑₜ θ) (h : Derivable U (insert (shift ℒₛₑₜ θ) (0 : V))) :
    Derivable U (insert θ (0 : V)) := by
  have h1 : IsSemiformula ℒₛₑₜ 1 θ := semiformula_mono hθ (by simp)
  have hw : IsSemitermVec ℒₛₑₜ 1 0 (^&0 ∷ (0 : V)) := by
    rw [show (1 : V) = 0 + 1 by simp]; simp
  have hfree : free ℒₛₑₜ θ = shift ℒₛₑₜ θ := by
    rw [free, substs1]; exact subst_closed_fml hθ.shift hw
  have hall : Derivable U (insert (^∀ θ) (0 : V)) :=
    Derivable.all h1 (by simpa [hfree, setShift_zero] using h)
  have hn : IsFormula ℒₛₑₜ (neg ℒₛₑₜ θ) := IsSemiformula.neg_iff.mpr hθ
  have hsub : substs1 ℒₛₑₜ (^&0) (neg ℒₛₑₜ θ) = neg ℒₛₑₜ θ := by
    rw [substs1]; exact subst_closed_fml hn hw
  have hS : IsFormulaSet ℒₛₑₜ (insert (neg ℒₛₑₜ θ) (insert θ (0 : V))) := by
    intro y hy
    rcases mem_bitInsert_iff.mp hy with rfl | hy
    · exact hn
    · exact singleton_formulaSet hθ y hy
  have hd : Derivable U (insert (^∃ (neg ℒₛₑₜ θ)) (insert θ (0 : V))) :=
    Derivable.exs (t := ^&0) (IsSemiformula.neg_iff.mpr h1) (by simp) (by
      rw [hsub]; exact Derivable.em hS θ (mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inl rfl))))
        (mem_bitInsert_iff.mpr (Or.inl rfl)))
  have hS₂ : IsFormulaSet ℒₛₑₜ (insert (^∀ θ) (insert θ (0 : V))) := by
    intro y hy
    rcases mem_bitInsert_iff.mp hy with rfl | hy
    · simpa using h1
    · exact singleton_formulaSet hθ y hy
  refine Derivable.cut (^∀ θ) (Derivable.wk hS₂ ?_ hall) (by simpa [h1.isUFormula] using hd)
  intro y hy
  rcases mem_bitInsert_iff.mp hy with rfl | hy
  · simp
  · simp at hy

end

section
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (ι : Interp)
variable {U : Theory ℒₛₑₜ} [U.Δ₁]

lemma markAt_free : free ℒₛₑₜ (neg ℒₛₑₜ (markAt ι (^#0 : V))) = neg ℒₛₑₜ (markAt ι (^&0 : V)) := by
  have hm : IsSemiformula ℒₛₑₜ 1 (markAt ι (^#0 : V)) := markAt_semiformula ι (by simp)
  have h1 : IsSemiformula ℒₛₑₜ 1 (tq ι.mark : V) := by simpa using tq_semiformula (V := V) ι.mark
  have hw : IsSemitermVec ℒₛₑₜ 1 0 (^&0 ∷ (0 : V)) := by
    rw [show (1 : V) = 0 + 1 by simp]; simp
  have hw₁ : IsSemitermVec ℒₛₑₜ 1 1 (^#0 ∷ (0 : V)) := by
    rw [show (1 : V) = 0 + 1 by simp]; simp
  have e1 : shift ℒₛₑₜ (markAt ι (^#0 : V)) = markAt ι (^#0 : V) := by
    rw [shift_markAt ι (show IsSemiterm ℒₛₑₜ 1 (^#0 : V) by simp)]; simp
  have e2 : subst ℒₛₑₜ (^&0 ∷ (0 : V)) (markAt ι (^#0 : V)) = markAt ι (^&0 : V) := by
    unfold markAt
    rw [substs_substs h1 hw hw₁, show (1 : V) = 0 + 1 by simp,
      termSubstVec_cons (by simp) (by simp)]
    simp
  rw [free, substs1, shift_neg hm, e1, substs_neg hm hw, e2]

/-- `¬Mark &x` descends to `¬Mark &0`. -/
lemma mark_descend : ∀ x : V, Derivable U (insert (neg ℒₛₑₜ (markAt ι (^&x))) (0 : V)) →
    Derivable U (insert (neg ℒₛₑₜ (markAt ι (^&0 : V))) (0 : V)) := by
  have hP : 𝚷ᴬ_[1 + 1]-Predicate (fun x : V => Derivable U (insert (neg ℒₛₑₜ (markAt ι (^&x))) (0 : V)) →
      Derivable U (insert (neg ℒₛₑₜ (markAt ι (^&0 : V))) (0 : V))) := by
    have : 𝚺ᴬ_[1 + 1]-Predicate (Derivable (V := V) U) := .of_lt Derivable.definable (by simp)
    have : 𝚷ᴬ_[1 + 1]-Predicate (Derivable (V := V) U) := .of_lt Derivable.definable (by simp)
    definability
  refine InductionOnHierarchy.succ_induction_sigma 𝚷 (1 + 1) hP (fun h => h) ?_
  intro x ih h
  apply ih
  have hm : IsFormula ℒₛₑₜ (neg ℒₛₑₜ (markAt ι (^&x))) :=
    IsSemiformula.neg_iff.mpr (markAt_semiformula ι (by simp))
  refine unshift₁ hm ?_
  rw [shift_neg (markAt_semiformula ι (m := 0) (by simp)), shift_markAt ι (m := 0) (show IsSemiterm ℒₛₑₜ 0 (^&x : V)
    by simp)]
  simpa using h

/-- With the axiom `∃e Mark e`, `¬Mark &x` refutes `U`. -/
theorem refute_of_mark {x : V} (hM : ^∃ (markAt ι (^#0 : V)) ∈ U.Δ₁Class)
    (h : Derivable U (insert (neg ℒₛₑₜ (markAt ι (^&x))) (0 : V))) :
    Bootstrapping.Provable U (^⊥ : V) := by
  have h₀ := mark_descend ι x h
  have hm1 : IsSemiformula ℒₛₑₜ 1 (markAt ι (^#0 : V)) := markAt_semiformula ι (by simp)
  have hall : Derivable U (insert (^∀ (neg ℒₛₑₜ (markAt ι (^#0 : V)))) (0 : V)) :=
    Derivable.all (IsSemiformula.neg_iff.mpr hm1) (by simpa [markAt_free, setShift_zero] using h₀)
  have hex : Derivable U (insert (^∃ (markAt ι (^#0 : V))) (0 : V)) :=
    Derivable.by_axm (singleton_formulaSet (by simpa using hm1)) _ (by simp) hM
  have h₂ : Derivable U (0 : V) :=
    Derivable.cut (^∀ (neg ℒₛₑₜ (markAt ι (^#0 : V)))) (by simpa using hall)
      (by simpa [hm1.isUFormula] using hex)
  refine (internal_provable_iff_internal_derivable).mpr
    (Derivable.wk (singleton_formulaSet (by simp)) (fun y hy => by simp at hy) h₂)

/-- Stage one, closed: an internal refutation of `T` gives an internal refutation of `U`. -/
theorem stage_one_bot {U : Theory ℒₛₑₜ} [U.Δ₁] (T : ArithmeticTheory) [T.Δ₁]
    (hF : InterpFacts ι U) (hT : AxStep ι T U V)
    (hM : ^∃ (markAt ι (^#0 : V)) ∈ U.Δ₁Class) (h : Bootstrapping.Provable T (^⊥ : V)) :
    Bootstrapping.Provable U (^⊥ : V) := by
  obtain ⟨x, hx⟩ := stage_one T hF hT h
  exact refute_of_mark ι hM hx

end

end ZF207.Internal.Arith
