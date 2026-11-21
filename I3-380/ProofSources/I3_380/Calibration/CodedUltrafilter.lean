module
public import I3_380.Calibration.FilterHistories
@[expose] public section

namespace PalomarI3380.Calibration.TermWords

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

noncomputable abbrev stagedAlgebra := (quotientAlgebra (M := M)).withStages

def CodeLe (a b : M) : Prop := meetValueDef.val.Evalb ![a,a,b]

theorem codeLe_defined : 𝚺ᴬ₁-Relation (CodeLe (M := M)) := by
  let Meet (out a b : M) := meetValueDef.val.Evalb ![out,a,b]
  have defined : 𝚺ᴬ₁-Relation₃ Meet via meetValueDef := .mk fun v => by
    change meetValueDef.val.Evalb v ↔ meetValueDef.val.Evalb ![v 0,v 1,v 2]
    rw [← Matrix.fun_eq_vec_three v]
  have graph : 𝚺ᴬ₁-Relation₃ Meet := defined.to_definable
  exact graph.comp (.var 0) (.var 0) (.var 1)

theorem codeLe_eval (a b : CanonicalTerm M) :
    CodeLe a.val b.val ↔ stagedAlgebra.le (canonicalClass a) (canonicalClass b) :=
  (meetValue_eval a a b).trans eq_comm

theorem descendName_le (laws : RelationLaws (stagedAlgebra (M := M)))
    (current : CanonicalTerm M) (i : M) :
    stagedAlgebra.le (canonicalClass (descendName current i)) (canonicalClass current) := by
  simp only [descendName]
  split
  · exact laws.bool.le_refl _
  · rw [nameClass_class]
    exact laws.bool.inf_le_left _ _

theorem descendName_nonzero (current : CanonicalTerm M) (i : M)
    (nonzero : current ≠ zeroName) : descendName current i ≠ zeroName := by
  simp only [descendName]
  split
  · exact nonzero
  · rename_i meets
    intro h
    apply meets
    simpa [zeroName] using congrArg canonicalClass h

theorem FilterHistory.name_le (laws : RelationLaws (stagedAlgebra (M := M)))
    {seed : CanonicalTerm M} {n trace : M} (h : FilterHistory seed n trace)
    {i j : M} (ij : i ≤ j) (jn : j ≤ n) : CodeLe trace.[j] trace.[i] := by
  have definable : 𝚺ᴬ₁-Relation (CodeLe (M := M)) := codeLe_defined
  have all (k : M) : i ≤ k → k ≤ n → CodeLe trace.[k] trace.[i] := by
    induction k using ISigma1.sigma1_succ_induction with
    | zero =>
      intro h₀ kn
      have eq : i=0 := nonpos_iff_eq_zero.mp h₀
      subst i
      exact (codeLe_eval ⟨trace.[0],h.canonical _ kn⟩ ⟨trace.[0],h.canonical _ kn⟩).mpr
        (laws.bool.le_refl _)
    | succ k ih =>
      intro before fits
      let a : CanonicalTerm M := ⟨trace.[k+1],h.canonical _ fits⟩
      let b : CanonicalTerm M := ⟨trace.[i],h.canonical _ (before.trans fits)⟩
      apply (codeLe_eval a b).mpr
      rcases lt_or_eq_of_le before with earlier | eq
      · have kn : k < n := lt_of_lt_of_le (lt_add_one _) fits
        let previous : CanonicalTerm M := ⟨trace.[k],h.canonical _ (le_of_lt kn)⟩
        have next : a = descendName previous k :=
          Subtype.ext ((descentStepDef_eval previous k a.val).mp (h.step k kn))
        have past := (codeLe_eval previous b).mp (ih (lt_succ_iff_le.mp earlier) (le_of_lt kn))
        rw [next]
        exact laws.bool.le_trans (descendName_le laws previous k) past
      · have same : a = b := Subtype.ext (congrArg (fun k => trace.[k]) eq.symm)
        rw [same]
        exact laws.bool.le_refl _
    | hP => definability
  exact all j ij jn

theorem FilterHistory.name_nonzero {seed : CanonicalTerm M} {n trace : M}
    (h : FilterHistory seed n trace) (seedNonzero : seed ≠ zeroName) {i : M} (fits : i ≤ n) :
    trace.[i] ≠ (zeroName (M := M)).val := by
  have all (k : M) : k ≤ n → trace.[k] ≠ (zeroName (M := M)).val := by
    induction k using ISigma1.sigma1_succ_induction with
    | zero =>
      intro _ starts
      exact seedNonzero (Subtype.ext (h.initial.symm.trans starts))
    | succ k ih =>
      intro bound empty
      have kn : k < n := lt_of_lt_of_le (lt_add_one _) bound
      let previous : CanonicalTerm M := ⟨trace.[k],h.canonical _ (le_of_lt kn)⟩
      have next := (descentStepDef_eval previous k trace.[k+1]).mp (h.step k kn)
      have nz : previous ≠ zeroName := fun eq => ih (le_of_lt kn) (congrArg Subtype.val eq)
      exact descendName_nonzero previous k nz (Subtype.ext (next.symm.trans empty))
    | hP => definability
  exact all i fits

theorem descentAt_le (laws : RelationLaws (stagedAlgebra (M := M)))
    (seed : CanonicalTerm M) {i j : M} (before : i ≤ j) :
    stagedAlgebra.le (canonicalClass (descentAt seed j)) (canonicalClass (descentAt seed i)) := by
  obtain ⟨tr,h⟩ := filterHistory_exists seed j
  let tr' := Classical.choose (filterHistory_exists seed i)
  have agrees := (Classical.choose_spec (filterHistory_exists seed i)).agree h i le_rfl before
  apply (codeLe_eval (descentAt seed j) (descentAt seed i)).mp
  change CodeLe (descentAt seed j).val tr'.[i]
  rw [h.result,show tr'.[i] = tr.[i] from agrees]
  exact h.name_le laws before le_rfl

theorem descentAt_nonzero (seed : CanonicalTerm M) (nonzero : canonicalClass seed ≠ stagedAlgebra.zero) (i : M) :
    canonicalClass (descentAt seed i) ≠ stagedAlgebra.zero := by
  obtain ⟨tr,h⟩ := filterHistory_exists seed i
  intro empty
  have eq : descentAt seed i = zeroName := canonicalClass_injective (by simpa [zeroName] using empty)
  apply h.name_nonzero (i := i) (fun same => nonzero (by rw [same]; simp [zeroName])) le_rfl
  exact h.result.symm.trans (congrArg Subtype.val eq)

noncomputable def namedUltrafilter (laws : RelationLaws (stagedAlgebra (M := M))) (seed : CanonicalTerm M)
    (subunit : stagedAlgebra.le (canonicalClass seed) (stagedAlgebra.constant .I))
    (nonzero : canonicalClass seed ≠ stagedAlgebra.zero) :
    SubidentityUltrafilter (stagedAlgebra (M := M)) := by
  let alg := stagedAlgebra (M := M)
  let chain (i : M) := canonicalClass (descentAt seed i)
  have subidentity (i : M) : alg.le (chain i) (alg.constant .I) :=
    laws.bool.le_trans (descentAt_le laws seed (Arithmetic.zero_le i)) (by simpa [descentAt_zero] using subunit)
  refine SubidentityUltrafilter.ofDescending laws (fun i j : M => i ≤ j) 0
    (fun i j => ⟨max i j,le_max_left _ _,le_max_right _ _⟩)
    chain (fun _ _ h => descentAt_le laws seed h) subidentity (descentAt_nonzero seed nonzero) ?_
  intro x _
  let request := nameClass x
  let i := request.val
  have requested : canonicalClass (requestName i) = x := by
    simp [i,requestName,request.property,request]
  by_cases empty : alg.inf (chain i) x = alg.zero
  · have complement : alg.le (chain i) (alg.neg x) := by
      apply (laws.bool.disjoint_iff_le (alg.constant .I) _ _).mp
      rw [laws.bool.involution,empty]
    exact Or.inr ⟨i,laws.bool.le_inf.mpr ⟨subidentity i,complement⟩⟩
  · have next : chain (i+1) = alg.inf (chain i) x := by
      change canonicalClass (descentAt seed (i+1)) = _
      rw [descentAt_succ,descendName,requested]
      have ne : stagedAlgebra.inf (canonicalClass (descentAt seed i)) x ≠ stagedAlgebra.zero := empty
      simp [ne,alg,chain,stagedAlgebra]
    exact Or.inl ⟨i+1,by rw [next]; exact laws.bool.inf_le_right _ _⟩

theorem namedUltrafilter_member (laws : RelationLaws (stagedAlgebra (M := M))) (seed : CanonicalTerm M)
    (subunit : stagedAlgebra.le (canonicalClass seed) (stagedAlgebra.constant .I))
    (nonzero : canonicalClass seed ≠ stagedAlgebra.zero) (x : CanonicalTerm M) :
    (namedUltrafilter laws seed subunit nonzero).member (canonicalClass x) ↔
      CodeLe x.val (unitName (M := M)).val ∧
        ∃ i trace, FilterHistory seed i trace ∧ CodeLe trace.[i] x.val := by
  change (stagedAlgebra.le (canonicalClass x) (stagedAlgebra.constant .I) ∧
    ∃ i, stagedAlgebra.le (canonicalClass (descentAt seed i)) (canonicalClass x)) ↔ _
  have unit : canonicalClass (unitName (M := M)) = stagedAlgebra.constant .I := nameClass_class _
  rw [codeLe_eval x unitName,unit]
  refine and_congr_right (fun _ => ⟨?_,?_⟩)
  · rintro ⟨i,below⟩
    obtain ⟨tr,h⟩ := filterHistory_exists seed i
    exact ⟨i,tr,h,h.result ▸ (codeLe_eval (descentAt seed i) x).mpr below⟩
  · rintro ⟨i,tr,h,below⟩
    exact ⟨i,(codeLe_eval (descentAt seed i) x).mp (h.result.symm ▸ below)⟩

end PalomarI3380.Calibration.TermWords
