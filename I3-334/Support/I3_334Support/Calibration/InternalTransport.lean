module
public import I3_334Support.Calibration.Certificates
@[expose] public section

namespace PalomarI3380.Calibration

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ArithmeticInterpretation

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem insert_formulaSet {p gamma : M} (pFormula : IsFormula GraphLanguage p)
    (context : IsFormulaSet GraphLanguage gamma) : IsFormulaSet GraphLanguage (insert p gamma) := by
  intro q member
  rcases mem_bitInsert_iff.mp member with rfl | rest
  · exact pFormula
  · exact context q rest

theorem derive_verums {gamma : M} (context : IsFormulaSet GraphLanguage gamma) (n : M) :
    Derivable graphTheory (insert (qqVerums n) gamma) := by
  induction n using ISigma1.sigma1_succ_induction with
  | zero =>
    simpa using Derivable.verum (T := graphTheory) (insert_formulaSet (by simp) context) (by simp)
  | succ k previous =>
    rw [qqVerums_succ]
    have wellFormed : IsFormula GraphLanguage (qqVerums k : M) := IsSemiformula.qqVerums k
    have joined := insert_formulaSet (show IsFormula GraphLanguage (^⊤ ^⋏ qqVerums k : M) by simp) context
    refine Derivable.and_m (p := ^⊤) (q := qqVerums k) (by simp) ?_ ?_
    · exact Derivable.verum (insert_formulaSet (by simp) joined) (by simp)
    · refine Derivable.wk (insert_formulaSet wellFormed joined) ?_ previous
      intro q member
      rcases mem_bitInsert_iff.mp member with rfl | old <;> simp [*]
  | hP => definability

theorem graphAxiomStep [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] : AxStep filterInterpretation arithmeticTheory graphTheory M := by
  intro p member marker term
  obtain ⟨s,_,w,_,rfl,valid,_,_,certificate⟩ :=
    (Craig.paddedAxiom_iff graphCertificates p).mp member
  have checked : Proof graphTheory w (kax filterInterpretation s) :=
    (graphCertificate_defined (M := M)).df ![s,w] |>.mp certificate
  have left : Derivable graphTheory (insert (kax filterInterpretation s) (0 : M)) :=
    Provable.toDerivable ⟨w,checked⟩
  let negative := neg GraphLanguage (markAt filterInterpretation marker)
  let translated := J filterInterpretation marker 0 s
  have markFormula : IsFormula GraphLanguage (markAt filterInterpretation marker) :=
    markAt_semiformula filterInterpretation term
  have notMark : IsFormula GraphLanguage negative := IsSemiformula.neg_iff.mpr markFormula
  have bodyFormula : IsFormula GraphLanguage translated := J_semiformula filterInterpretation 0 s valid marker term
  have frame := pair_formulaSet notMark bodyFormula
  have inContext :
      Derivable graphTheory (insert (kax filterInterpretation s) (insert negative (insert translated (0 : M)))) := by
    refine Derivable.wk (insert_formulaSet (kax_formula filterInterpretation valid) frame) ?_ left
    intro a ha
    simp only [mem_bitInsert_iff, not_mem_zero, or_false] at ha
    exact mem_bitInsert_iff.mpr (Or.inl ha)
  have premise : Derivable graphTheory (insert negative (insert translated (0 : M))) :=
    derivable_of_kax' filterInterpretation valid term inContext
  have pad : IsFormula GraphLanguage (qqVerums w : M) := IsSemiformula.qqVerums w
  rw [J_and valid.isUFormula (IsSemiformula.qqVerums (n := 0) w).isUFormula, J_verums]
  change Derivable graphTheory (insert negative (insert (translated ^⋏ qqVerums w) (0 : M)))
  have paddingContext : IsFormulaSet GraphLanguage (insert negative (insert (translated ^⋏ qqVerums w) (0 : M))) :=
    pair_formulaSet notMark (by simp [bodyFormula,pad])
  have bodyMember : translated ^⋏ qqVerums w ∈ (insert negative (insert (translated ^⋏ qqVerums w) (0 : M))) :=
    mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inl rfl)))
  refine Derivable.and_m (p := translated) (q := qqVerums w) bodyMember
    ?_ (derive_verums paddingContext w)
  refine Derivable.wk (insert_formulaSet bodyFormula paddingContext) ?_ premise
  intro a ha
  simp only [mem_bitInsert_iff,not_mem_zero,or_false] at ha
  rcases ha with rfl | rfl
  · exact mem_bitInsert_iff.mpr (Or.inr (mem_bitInsert_iff.mpr (Or.inl rfl)))
  · exact mem_bitInsert_iff.mpr (Or.inl rfl)

theorem marker_internal :
    (^∃ (markAt filterInterpretation (^#0 : M))) ∈ graphTheory.Δ₁Class := by
  have included : markerExists ∈ graphTheory := Or.inr List.mem_cons_self
  have quotes : (⌜markerExists⌝ : M) = ^∃ (markAt filterInterpretation (^#0 : M)) := by
    simp [markerExists,filterInterpretation,markAt,tq_eq,Sentence.quote_verum]
  rw [← quotes]
  simpa using included

theorem graph_refutation_of_arithmetic [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (templates : InterpFacts filterInterpretation graphTheory)
    (arithmeticRefutation : Bootstrapping.Provable arithmeticTheory (^⊥ : M)) :
    Bootstrapping.Provable graphTheory (^⊥ : M) :=
  stage_one_bot filterInterpretation arithmeticTheory templates graphAxiomStep marker_internal arithmeticRefutation

end PalomarI3380.Calibration
