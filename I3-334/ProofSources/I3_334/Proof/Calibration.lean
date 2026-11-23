module
public import I3_334.Search.SearchSoundness
public import I3_334.Calibration.ModelBridge
public import I3_334Support.Calibration.Refutation
public import I3_334Support.Calibration.Godel
@[expose] public section

namespace PalomarI3334

open PalomarI3380 PalomarI3380.Logic PalomarI3380.Logic.Expanded
open PalomarI3380.Calibration
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

/-- Internally coded halting traces suffice for the consistency statement
used by the second incompleteness theorem. -/
theorem nonhalting_implies_internal_consistency :
    ZFCI3Provable (.imp (Neg haltingSentence) (readArithmetic arithmeticTheory.standardProvability.con)) := by
  have closed : Closed (.imp (Neg haltingSentence) (readArithmetic arithmeticTheory.standardProvability.con)) :=
    ⟨⟨haltingSentence_represents.1,trivial⟩,readArithmetic_closed _⟩
  apply zfci3_complete closed
  intro V E inhabited model env nonhalting
  have zfc : ZFCModel E := fun p h => model p (h.elim Or.inl (fun ax => Or.inr (Or.inl ax)))
  obtain ⟨w,omega⟩ := zfc.omega env
  let D : OmegaDomain (ClassAxioms.from_ordinary zfc) inhabited := ⟨w,omega⟩
  letI : D.Points↓[ℒₒᵣ] ⊧* 𝗣𝗔 := D.models_peano
  have distinct : (TermWords.stagedAlgebra (M := D.Points)).constant .D ≠
      TermWords.stagedAlgebra.constant .J := by
    intro collapsed
    have halted := SearchProgram.coded_halts_of_legacyCollapse collapsed
    have history := D.internal_halts_iff_arithmetic334.mpr halted
    exact nonhalting ((haltingSentence_represents.2 V E inhabited model env).mpr history)
  exact (readArithmetic_eval D _ env).mpr (con_eval.mpr (model_distinction_excludes_refutation D distinct))

theorem literal_nonhalting_unprovable (consistent : ZFCI3Consistent) :
    ¬ ZFCI3Provable (Neg haltingSentence) := by
  letI : 𝗜𝚺₁ ⪯ arithmeticTheory :=
    FFL.Entailment.WeakerThan.trans (𝓣 := 𝗣𝗔) inferInstance arithmeticTheory_extends_pa
  letI : FFL.Entailment.Consistent arithmeticTheory := arithmeticTheory_consistent consistent
  exact unprovable_neg_of_internal_consistency nonhalting_implies_internal_consistency
    (fun _ => arithmeticTheory_absorb)

end PalomarI3334
