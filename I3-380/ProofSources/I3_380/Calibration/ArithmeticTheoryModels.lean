module
public import I3_380.Calibration.Certificates
public import I3_380.Calibration.TranslationSemantics
public import I3_380.Calibration.FilterSatisfiability
public import I3_380.Logic.Completeness
public import I3_380.EquationalConsistency
@[expose] public section

namespace PalomarI3380.Calibration

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic
open Logic.Expanded

theorem source_reads_pa {φ : ArithmeticSentence} (pa : 𝗣𝗔 ⊢ φ) :
    Logic.ZFCI3Provable (Logic.readArithmetic φ) := by
  apply Logic.zfci3_complete (Logic.readArithmetic_closed φ)
  intro V E inhabited model env
  have zfc : Logic.ZFCModel E := fun p h => model p (h.elim Or.inl (fun choice => Or.inr (Or.inl choice)))
  obtain ⟨w,omega⟩ := zfc.omega env
  let D : OmegaDomain (ClassAxioms.from_ordinary zfc) inhabited := ⟨w,omega⟩
  exact (Logic.readArithmetic_eval D φ env).mpr (Theory.Proof.sound pa D.models_peano)

theorem graphTheory_proves_translation {φ : ArithmeticSentence}
    (source : Logic.ZFCI3Provable (Logic.readArithmetic φ)) :
    graphTheory ⊢ translatedSentence φ := by
  apply Theory.Proof.complete
  apply consequence_iff_eq.mpr
  intro A inhabited sourceGraph eq model
  let graphs := graphTheory_has_operations model
  letI : Tarski.Structure FilterLanguage A := restoreStructure graphs
  letI : Tarski.Structure.Eq FilterLanguage A := restoreStructure_eq graphs
  have restored : @graphStructure A (restoreStructure graphs) = sourceGraph :=
    restoreStructure_relational graphs
  obtain ⟨C,inhabited,sourceModel⟩ := source_model_of_filterTheory (filterTheory_of_graph model)
  let env := fun _ : Nat => Classical.choice inhabited
  have zfc : Logic.ZFCModel C.mem := fun p h =>
    sourceModel p (h.elim Or.inl (fun choice => Or.inr (Or.inl choice)))
  obtain ⟨w,omega⟩ := zfc.omega env
  let D : OmegaDomain (ClassAxioms.from_ordinary zfc) inhabited := ⟨w,omega⟩
  obtain ⟨rep,_⟩ := C.asPoint_onto (env 0)
  obtain ⟨Γ,axioms,proof⟩ := source
  have reads : Logic.eval C.mem (Logic.readArithmetic φ) env :=
    Logic.NDSemantics.sound C.mem proof env (fun p hp => sourceModel p (axioms p hp) env)
  have truth := (Logic.readArithmetic_eval D φ env).mp reads
  have checked := (translatedSentence_reads C D φ rep).mpr truth
  change @Semiformula.Evalb GraphLanguage A 0 (graphStructure (A := A)) ![] (translatedSentence φ) at checked
  rw [restored] at checked
  exact checked

theorem arithmeticTheory_absorb {φ : ArithmeticSentence}
    (proved : Logic.ZFCI3Provable (Logic.readArithmetic φ)) : arithmeticTheory ⊢ φ :=
  arithmeticTheory_admits (graphTheory_proves_translation proved)

theorem arithmeticTheory_extends_pa : 𝗣𝗔 ⪯ arithmeticTheory :=
  FFL.Entailment.weakerThan_iff.mpr fun pa => arithmeticTheory_absorb (source_reads_pa pa)

theorem arithmeticTheory_consistent (source : Logic.ZFCI3Consistent) :
    FFL.Entailment.Consistent arithmeticTheory := by
  have unproved := equational_underivability_of_consistency source
  obtain ⟨A,nonempty,structure',equal,model⟩ :=
    satisfiable_iff_eq.mp (filter_satisfiable_of_underivability unproved)
  letI : Nonempty A := nonempty
  letI : Tarski.Structure FilterLanguage A := structure'
  letI : Tarski.Structure.Eq FilterLanguage A := equal
  letI : Tarski.Structure GraphLanguage A := graphStructure
  have typedModel : A↓[GraphLanguage] ⊧* graphTheory := graphTheory_of_filter model
  obtain ⟨C,inh,sourceModel⟩ := source_model_of_filterTheory model
  let env := fun _ : Nat => Classical.choice inh
  have zfc : Logic.ZFCModel C.mem := fun p h =>
    sourceModel p (h.elim Or.inl (fun choice => Or.inr (Or.inl choice)))
  obtain ⟨w,omega⟩ := zfc.omega env
  let D : OmegaDomain (ClassAxioms.from_ordinary zfc) inh := ⟨w,omega⟩
  obtain ⟨rep,_⟩ := C.asPoint_onto (env 0)
  letI : D.Points↓[ℒₒᵣ] ⊧* arithmeticTheory := models_theory_iff.mpr fun p member => by
    obtain ⟨original,certificate,rfl,accepted⟩ := Craig.unpad graphCertificates member
    have proof : Proof graphTheory certificate (⌜translatedSentence original⌝ : Nat) := by
      have admitted := ((graphCertificate_defined (M := Nat)).df ![(⌜original⌝ : Nat),certificate]).mp accepted
      simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,translatedSentence_quote] using admitted
    have derived : graphTheory ⊢ translatedSentence original := provable_iff_provable.mp ⟨certificate,proof⟩
    have truth := (translatedSentence_reads C D original rep).mp (Theory.Proof.sound derived typedModel)
    have padding : ∀ k, (Craig.verums k).Evalb (![] : Fin 0 → D.Points) := by
      intro k
      induction k <;> simp [Craig.verums, *]
    exact ⟨truth,padding certificate⟩
  exact FFL.FirstOrder.consistent_of_model arithmeticTheory D.Points

end PalomarI3380.Calibration
