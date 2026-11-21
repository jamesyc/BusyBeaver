module
public import I3_380.Calibration.InternalGraphSoundness
public import I3_380.Calibration.InternalRewrite
public import I3_380.Calibration.InternalTransport
public import I3_380.Calibration.InterpretationFacts
public import I3_380.Calibration.ArithmeticTheoryModels
public import I3_380.Calibration.Godel
public import I3_380.Arithmetic.InternalHalting
@[expose] public section

namespace PalomarI3380.Calibration

open Logic.Expanded
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding CodedGraph

theorem model_nonhalting_excludes_refutation
    {V : Type} {E G : V → V → Prop} {L : ClassAxioms E G} {inhabited : Nonempty V}
    (D : OmegaDomain L inhabited)
    (nonhalting : ¬(ArithmeticMachine.haltsDef 380 packedLiteral).val.Evalb (![] : Fin 0 → D.Points)) :
    ¬Bootstrapping.Provable arithmeticTheory (^⊥ : D.Points) := by
  have distinct : (TermWords.stagedAlgebra (M := D.Points)).constant .D ≠ TermWords.stagedAlgebra.constant .J :=
    fun collapsed => nonhalting (TermWords.model_halts_of_distinction_failure collapsed)
  obtain ⟨P,model⟩ := CodedGraph.Presentation.of_distinction D distinct
  obtain ⟨truth⟩ := CodedGraph.TruthTable.exists_table D P
  exact fun bad => truth.no_refutation D model (graph_refutation_of_arithmetic interpretation_facts bad)

theorem con_eval {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    arithmeticTheory.standardProvability.con.Evalb (![] : Fin 0 → M) ↔
       ¬Bootstrapping.Provable arithmeticTheory (^⊥ : M) := by
  simp [ProvabilityAbstraction.Provability.con,standardProvability_def,Function.comp_def,
    FFL.FirstOrder.Sentence.quote_falsum]

theorem source_proves_consistency_from_nonhalting :
    Logic.ZFCI3Provable (.imp (Logic.Neg Logic.haltingSentence)
      (Logic.readArithmetic arithmeticTheory.standardProvability.con)) := by
  have closed : Logic.Closed (.imp (Logic.Neg Logic.haltingSentence)
      (Logic.readArithmetic arithmeticTheory.standardProvability.con)) :=
    ⟨⟨Logic.haltingSentence_represents.1,trivial⟩,Logic.readArithmetic_closed _⟩
  apply Logic.zfci3_complete closed
  intro V E inhabited model env nonhalting
  have zfc : Logic.ZFCModel E := fun p h => model p (h.elim Or.inl (fun ax => Or.inr (Or.inl ax)))
  obtain ⟨w,omega⟩ := zfc.omega env
  let D : OmegaDomain (ClassAxioms.from_ordinary zfc) inhabited := ⟨w,omega⟩
  have noHalt : ¬(ArithmeticMachine.haltsDef 380 packedLiteral).val.Evalb (![] : Fin 0 → D.Points) := by
    intro halting
    exact nonhalting ((Logic.haltingSentence_represents.2 V E inhabited model env).mpr
      (D.internal_halts_iff_arithmetic.mpr halting))
  exact (Logic.readArithmetic_eval D _ env).mpr (con_eval.mpr (model_nonhalting_excludes_refutation D noHalt))

theorem calibration : Logic.ArithmeticCalibration arithmeticTheory where
  extendsSigmaOne :=
    FFL.Entailment.WeakerThan.trans (𝓣 := 𝗣𝗔) inferInstance arithmeticTheory_extends_pa
  consistent := arithmeticTheory_consistent
  internalConsistency := source_proves_consistency_from_nonhalting
  absorb _ := arithmeticTheory_absorb

end PalomarI3380.Calibration
