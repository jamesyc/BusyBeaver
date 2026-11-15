module
public import Internal.Tait.Translate
@[expose] public section
/-! # Equations of the translation

The recursion equations of `tr`; the negative component is the translation of
the negation; shifting free variables shifts the free-label offset; substituting
variables for bound variables changes only the bound-label vector. All are code
equalities, proved by internal Π1 induction. -/
namespace ZF209.Internal.Tait
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

instance tr_defined : 𝚺ᴬ₁-Function₂ (tr : V → V → V) via Tr.blueprint.result ℒₛₑₜ :=
  Tr.construction.result_defined (L := ℒₛₑₜ)

instance tr_definable : 𝚺ᴬ₁-Function₂ (tr : V → V → V) := tr_defined.to_definable

instance tr_definable' (Γ m) : Γᴬ_[m + 1]-Function₂ (tr : V → V → V) :=
  tr_definable.of_sigmaOne

instance vlab_definable' (Γ m) : Γᴬ_[m + 1]-Function₃ (vlab : V → V → V → V) :=
  .of_sigmaOne vlab_defined.to_definable

instance step_definable' (Γ m) : Γᴬ_[m + 1]-Function₁ (step : V → V) :=
  .of_sigmaOne step_defined.to_definable

@[simp] lemma step_mk (e d m f : V) : step ⟪e, d, m, f⟫ = ⟪xlab f d ∷ e, d + 1, m, f⟫ := by
  simp [step]

@[simp] lemma tr_rel {param k R v : V} (hR : (ℒₛₑₜ).IsRel k R) (hv : IsUTermVec ℒₛₑₜ k v) :
    tr param (^rel k R v) = posPair (atom (penv param) (poff param) R v.[0] v.[1]) := by
  simp [tr, hR, hv, Tr.construction]

@[simp] lemma tr_nrel {param k R v : V} (hR : (ℒₛₑₜ).IsRel k R) (hv : IsUTermVec ℒₛₑₜ k v) :
    tr param (^nrel k R v) = negPair (atom (penv param) (poff param) R v.[0] v.[1]) := by
  simp [tr, hR, hv, Tr.construction]

@[simp] lemma tr_verum (param : V) : tr param ^⊤ = posPair (cneg (1 : V)) := by
  simp [tr, Tr.construction]

@[simp] lemma tr_falsum (param : V) : tr param ^⊥ = negPair (cneg (1 : V)) := by
  simp [tr, Tr.construction]

@[simp] lemma tr_and {param p q : V} (hp : IsUFormula ℒₛₑₜ p) (hq : IsUFormula ℒₛₑₜ q) :
    tr param (p ^⋏ q) = posPair (cand (π₁ (tr param p)) (π₁ (tr param q))) := by
  simp [tr, hp, hq, Tr.construction]

@[simp] lemma tr_or {param p q : V} (hp : IsUFormula ℒₛₑₜ p) (hq : IsUFormula ℒₛₑₜ q) :
    tr param (p ^⋎ q) = negPair (cand (π₂ (tr param p)) (π₂ (tr param q))) := by
  simp [tr, hp, hq, Tr.construction]

@[simp] lemma tr_all {param p : V} (hp : IsUFormula ℒₛₑₜ p) :
    tr param (^∀ p) =
      posPair (all (xlab (pfam param) (pdep param)) (π₁ (tr (step param) p))) := by
  simp [tr, hp, Tr.construction]

@[simp] lemma tr_exs {param p : V} (hp : IsUFormula ℒₛₑₜ p) :
    tr param (^∃ p) =
      negPair (all (xlab (pfam param) (pdep param)) (π₂ (tr (step param) p))) := by
  simp [tr, hp, Tr.construction]

/-- The negative component is the translation of the negation. -/
theorem tr_neg {p : V} (hp : IsUFormula ℒₛₑₜ p) : ∀ param : V,
    π₂ (tr param p) = π₁ (tr param (neg ℒₛₑₜ p)) ∧
      π₂ (tr param (neg ℒₛₑₜ p)) = π₁ (tr param p) := by
  revert p
  apply IsUFormula.induction1 𝚷 (P := fun p => ∀ param : V,
    π₂ (tr param p) = π₁ (tr param (neg ℒₛₑₜ p)) ∧
      π₂ (tr param (neg ℒₛₑₜ p)) = π₁ (tr param p))
  · definability
  · intro k r v hr hv param; simp [hr, hv, posPair, negPair]
  · intro k r v hr hv param; simp [hr, hv, posPair, negPair]
  · intro param; simp [posPair, negPair]
  · intro param; simp [posPair, negPair]
  · intro p q hp hq ihp ihq param
    simp [hp, hq, hp.neg, hq.neg, posPair, negPair, (ihp param).1, (ihp param).2,
      (ihq param).1, (ihq param).2]
  · intro p q hp hq ihp ihq param
    simp [hp, hq, hp.neg, hq.neg, posPair, negPair, (ihp param).1, (ihp param).2,
      (ihq param).1, (ihq param).2]
  · intro p hp ih param
    simp [hp, hp.neg, posPair, negPair, (ih (step param)).1, (ih (step param)).2]
  · intro p hp ih param
    simp [hp, hp.neg, posPair, negPair, (ih (step param)).1, (ih (step param)).2]

/-! ## Terms -/

lemma set_uterm_cases {t : V} : IsUTerm ℒₛₑₜ t → (∃ i, t = ^#i) ∨ ∃ i, t = ^&i := by
  intro h
  rcases IsUTerm.case h with h | h | ⟨k, f, v, hf, _, _⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd hf (by simp)

lemma vlab_termShift {t : V} (ht : IsUTerm ℒₛₑₜ t) (e m : V) :
    vlab e m (termShift ℒₛₑₜ t) = vlab e (m + 1) t := by
  rcases set_uterm_cases ht with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp
  · simp [ylab, add_assoc, add_comm 1 i]

lemma vlab_termBShift {t : V} (ht : IsUTerm ℒₛₑₜ t) (x e m : V) :
    vlab (x ∷ e) m (termBShift ℒₛₑₜ t) = vlab e m t := by
  rcases set_uterm_cases ht with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> simp

lemma rel_two {k R : V} (hR : (ℒₛₑₜ).IsRel k R) : k = 2 := ((set_isRel k R).mp hR).1

/-! ## Shift -/

/-- Shifting free variables shifts the free-label offset. -/
theorem tr_shift {p : V} (hp : IsUFormula ℒₛₑₜ p) : ∀ e d m f : V,
    tr ⟪e, d, m, f⟫ (shift ℒₛₑₜ p) = tr ⟪e, d, m + 1, f⟫ p := by
  revert p
  apply IsUFormula.induction1 𝚷 (P := fun p => ∀ e d m f : V,
    tr ⟪e, d, m, f⟫ (shift ℒₛₑₜ p) = tr ⟪e, d, m + 1, f⟫ p)
  · definability
  · intro k r v hr hv e d m f
    have hk := rel_two hr; subst hk
    simp [hr, hv, hv.termShiftVec, atom, nth_termShiftVec hv,
      vlab_termShift (hv.nth (i := 0) (by simp)), vlab_termShift (hv.nth (i := 1) (by simp))]
  · intro k r v hr hv e d m f
    have hk := rel_two hr; subst hk
    simp [hr, hv, hv.termShiftVec, atom, nth_termShiftVec hv,
      vlab_termShift (hv.nth (i := 0) (by simp)), vlab_termShift (hv.nth (i := 1) (by simp))]
  · intro e d m f; simp
  · intro e d m f; simp
  · intro p q hp hq ihp ihq e d m f
    simp [hp, hq, hp.shift, hq.shift, ihp e d m f, ihq e d m f]
  · intro p q hp hq ihp ihq e d m f
    simp [hp, hq, hp.shift, hq.shift, ihp e d m f, ihq e d m f]
  · intro p hp ih e d m f
    simp [hp, hp.shift, ih]
  · intro p hp ih e d m f
    simp [hp, hp.shift, ih]

/-! ## Substitution of variables -/

/-- The bound-label vector `e'` holds the labels of the terms `w`. -/
def LabAgree (n e e' m w : V) : Prop := ∀ i < n, e'.[i] = vlab e m w.[i]

instance labAgree_definable : 𝚫ᴬ₁-Relation₅ (LabAgree : V → V → V → V → V → Prop) := by
  unfold LabAgree; definability

instance labAgree_definable' (Γ m) :
    Γᴬ_[m + 1]-Relation₅ (LabAgree : V → V → V → V → V → Prop) :=
  labAgree_definable.of_deltaOne

/-- Substituting variable terms `w` for the bound variables replaces the
bound-label vector by the labels of `w`. -/
theorem tr_subst {n p : V} (hp : IsSemiformula ℒₛₑₜ n p) : ∀ a w e e' d m f : V,
    IsSemitermVec ℒₛₑₜ n a w → LabAgree n e e' m w →
    tr ⟪e, d, m, f⟫ (subst ℒₛₑₜ w p) = tr ⟪e', d, m, f⟫ p := by
  revert n p
  apply IsSemiformula.induction1 𝚷 (P := fun n p => ∀ a w e e' d m f : V,
    IsSemitermVec ℒₛₑₜ n a w → LabAgree n e e' m w →
    tr ⟪e, d, m, f⟫ (subst ℒₛₑₜ w p) = tr ⟪e', d, m, f⟫ p)
  · definability
  · intro n k r v hr hv a w e e' d m f hw he
    have hk := rel_two hr; subst hk
    have key : ∀ i < (2 : V), vlab e m (termSubst ℒₛₑₜ w v.[i]) = vlab e' m v.[i] := by
      intro i hi
      rcases set_term_cases.mp (hv.nth hi) with ⟨j, hj, h⟩ | ⟨j, h⟩
      · rw [h, termSubst_bvar, vlab_bvar, he j hj]
      · rw [h]; simp
    rw [substs_rel hr hv.isUTerm, tr_rel hr (hw.termSubstVec hv).isUTerm, tr_rel hr hv.isUTerm]
    simp only [penv_mk, poff_mk, atom, nth_termSubstVec hv.isUTerm (show (0 : V) < 2 by simp),
      nth_termSubstVec hv.isUTerm (show (1 : V) < 2 by simp), key 0 (by simp), key 1 (by simp)]
  · intro n k r v hr hv a w e e' d m f hw he
    have hk := rel_two hr; subst hk
    have key : ∀ i < (2 : V), vlab e m (termSubst ℒₛₑₜ w v.[i]) = vlab e' m v.[i] := by
      intro i hi
      rcases set_term_cases.mp (hv.nth hi) with ⟨j, hj, h⟩ | ⟨j, h⟩
      · rw [h, termSubst_bvar, vlab_bvar, he j hj]
      · rw [h]; simp
    rw [substs_nrel hr hv.isUTerm, tr_nrel hr (hw.termSubstVec hv).isUTerm, tr_nrel hr hv.isUTerm]
    simp only [penv_mk, poff_mk, atom, nth_termSubstVec hv.isUTerm (show (0 : V) < 2 by simp),
      nth_termSubstVec hv.isUTerm (show (1 : V) < 2 by simp), key 0 (by simp), key 1 (by simp)]
  · intro n a w e e' d m f _ _; simp
  · intro n a w e e' d m f _ _; simp
  · intro n p q hp hq ihp ihq a w e e' d m f hw he
    simp [hp.isUFormula, hq.isUFormula, (hp.subst hw).isUFormula,
      (hq.subst hw).isUFormula, ihp a w e e' d m f hw he, ihq a w e e' d m f hw he]
  · intro n p q hp hq ihp ihq a w e e' d m f hw he
    simp [hp.isUFormula, hq.isUFormula, (hp.subst hw).isUFormula,
      (hq.subst hw).isUFormula, ihp a w e e' d m f hw he, ihq a w e e' d m f hw he]
  · intro n p hp ih a w e e' d m f hw he
    have hq := ih (a + 1) (qVec ℒₛₑₜ w) (xlab f d ∷ e) (xlab f d ∷ e') (d + 1) m f hw.qVec
      (by
        intro i hi
        rcases zero_or_succ i with rfl | ⟨j, rfl⟩
        · simp [qVec]
        · have hj : j < n := by simpa using hi
          simp only [qVec, nth_adjoin_succ, hw.lh]
          rw [nth_termBShiftVec hw.isUTerm hj, vlab_termBShift (hw.isUTerm.nth hj), he j hj])
    simp [hp.isUFormula, (hp.subst hw.qVec).isUFormula, hq]
  · intro n p hp ih a w e e' d m f hw he
    have hq := ih (a + 1) (qVec ℒₛₑₜ w) (xlab f d ∷ e) (xlab f d ∷ e') (d + 1) m f hw.qVec
      (by
        intro i hi
        rcases zero_or_succ i with rfl | ⟨j, rfl⟩
        · simp [qVec]
        · have hj : j < n := by simpa using hi
          simp only [qVec, nth_adjoin_succ, hw.lh]
          rw [nth_termBShiftVec hw.isUTerm hj, vlab_termBShift (hw.isUTerm.nth hj), he j hj])
    simp [hp.isUFormula, (hp.subst hw.qVec).isUFormula, hq]

/-- The eigenvariable instance `free p` of a formula with one bound variable. -/
theorem tr_free {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p) (e d m f : V) :
    tr ⟪e, d, m, f⟫ (free ℒₛₑₜ p) = tr ⟪?[ylab m], d, m + 1, f⟫ p := by
  rw [free, substs1, tr_subst hp.shift 0 ?[^&0] e ?[ylab m] d m f (by simp)
    (by intro i hi; have : i = 0 := by simpa using hi
        subst this; simp)]
  exact tr_shift hp.isUFormula _ _ _ _

/-- An instance at a free variable. -/
theorem tr_substs1 {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p) (j e d m f : V) :
    tr ⟪e, d, m, f⟫ (substs1 ℒₛₑₜ ^&j p) = tr ⟪?[ylab (m + j)], d, m, f⟫ p := by
  rw [substs1, tr_subst hp 0 ?[^&j] e ?[ylab (m + j)] d m f (by simp)
    (by intro i hi; have : i = 0 := by simpa using hi
        subst this; simp)]

end ZF209.Internal.Tait
