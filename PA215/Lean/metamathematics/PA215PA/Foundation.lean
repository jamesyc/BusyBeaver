import Foundation.FirstOrder.Incompleteness.Consistency
import PA215PA.Theory
import PA215PA.HaltingFormula

/-! Ordinary first-order Peano arithmetic and the second incompleteness theorem.

The language has zero, one, addition, multiplication, equality, and order,
with full first-order induction. For a sentence N, an internal PA proof of
N → Con(PA) makes N unprovable under consistency. NonhaltingUnprovability
instantiates this argument for the machine's arithmetic nonhalting sentence. -/

namespace PA215.PA

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

/-- Foundation's arithmetized consistency sentence for this exact theory. -/
noncomputable def consistencySentence : ArithmeticSentence := theory.consistent.val

/-- The imported second incompleteness theorem instantiated at PA. -/
theorem consistency_unprovable (h : Consistent) : theory ⊬ consistencySentence := by
  let : FFL.Entailment.Consistent theory := h
  exact ProvabilityAbstraction.con_unprovable (𝔅 := theory.standardProvability)

/-- If PA proves that a sentence implies its own consistency, consistency of PA rules out a proof of that sentence. -/
theorem unprovable_of_internal_consistency_implication
    (sentence : ArithmeticSentence)
    (hcons : Consistent)
    (hinternal : theory ⊢ sentence 🡒 consistencySentence) :
    theory ⊬ sentence := by
  intro hsentence
  exact consistency_unprovable hcons (hinternal ⨀ hsentence)

/-- Standard-model correctness of the exact arithmetized consistency sentence. -/
theorem consistencySentence_correct :
    (Nat ⊧/![] consistencySentence) ↔ Consistent := by
  simp [consistencySentence, Consistent, Bootstrapping.standard_consistent]

/-- Specialization of the incompleteness argument to the PA215 nonhalting sentence. -/
theorem nonhalting_unprovable_of_internal_consistency_implication
    (hcons : Consistent)
    (hinternal : theory ⊢ HaltingFormula.nonhaltingSentence 🡒 consistencySentence) :
    theory ⊬ HaltingFormula.nonhaltingSentence :=
  unprovable_of_internal_consistency_implication _ hcons hinternal

#print axioms consistencySentence_correct
#print axioms nonhalting_unprovable_of_internal_consistency_implication
#print axioms consistency_unprovable
#print axioms unprovable_of_internal_consistency_implication

end PA215.PA
