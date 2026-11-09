module

public import PA215PA.Theory
public import PA215PA.ActualRefutationGraph
public import User211PAHaltingFormula

@[expose] public section
namespace PA211.UserCandidate.PA.InternalActualRefutation
open PA215 PA215.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

/-- Uses the explicit unchanged V1 actual checker graph, not the earlier chosen
numeralwise representation or Foundation's PA proof predicate. -/
noncomputable def refutationHaltingSentence : ArithmeticSentence :=
  “∀ code, !ActualRefutationGraph.formula code → !HaltingFormula.traceSentence”
noncomputable def noActualRefutationSentence : ArithmeticSentence :=
  “∀ code, ¬!ActualRefutationGraph.formula code”
noncomputable def nonhaltingNoActualRefutationSentence : ArithmeticSentence :=
  “!HaltingFormula.nonhaltingSentence → !noActualRefutationSentence”

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
theorem refutationHalting_correct :
    (V ⊧/![] refutationHaltingSentence) ↔
      ∀ code : V,ActualCheckerBlueprint.verifyValue code=2 → V ⊧/![] HaltingFormula.traceSentence := by
  simp [refutationHaltingSentence,ActualRefutationGraph.formula_graph]
theorem noActualRefutation_correct :
    (V ⊧/![] noActualRefutationSentence) ↔
      ∀ code : V,ActualCheckerBlueprint.verifyValue code≠2 := by
  simp [noActualRefutationSentence,ActualRefutationGraph.formula_graph]
theorem nonhaltingNoActualRefutation_correct :
    (V ⊧/![] nonhaltingNoActualRefutationSentence) ↔
      ((¬V ⊧/![] HaltingFormula.traceSentence) →
        ∀ code : V,ActualCheckerBlueprint.verifyValue code≠2) := by
  simp [nonhaltingNoActualRefutationSentence,HaltingFormula.nonhaltingSentence,
    noActualRefutation_correct]

/-- Pure logical composition. The antecedent runtime theorem is not asserted by
this lemma, and no equivalence with Foundation consistency is claimed. -/
theorem pa_proves_runtime_contraposition : theory ⊢
    (refutationHaltingSentence 🡒 nonhaltingNoActualRefutationSentence) := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [models_iff,LogicalConnective.HomClass.map_imply,
    refutationHalting_correct,nonhaltingNoActualRefutation_correct]
  intro h hn code hc
  exact hn (h code hc)
#print axioms refutationHalting_correct
#print axioms noActualRefutation_correct
#print axioms nonhaltingNoActualRefutation_correct
#print axioms pa_proves_runtime_contraposition
end PA211.UserCandidate.PA.InternalActualRefutation

