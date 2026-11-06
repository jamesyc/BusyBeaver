import PA215PA.InternalActualRefutationConsistency
import PA215PA.InternalActualRefutationHalting

/-! PA proves that the machine nonhalting sentence implies its consistency sentence. Under external syntactic consistency, the second incompleteness theorem therefore excludes a PA proof of nonhalting. -/
namespace PA215.PA.InternalUnprovability
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

theorem pa_proves_nonhalting_consistency :
    theory ⊢ HaltingFormula.nonhaltingSentence 🡒 consistencySentence :=by
  have h:theory ⊢ HaltingFormula.nonhaltingSentence 🡒 InternalActualRefutation.noActualRefutationSentence:=by
    simpa [InternalActualRefutation.nonhaltingNoActualRefutationSentence,Rewriting.subst] using
      InternalActualRefutation.pa_proves_nonhalting_no_actual_refutation
  exact C_trans h InternalActualRefutation.pa_proves_no_actual_refutation_consistency

/-- Meta-level syntactic consistency of the fixed ordinary PA theory implies
that PA does not prove the original machine nonhalting sentence. -/
theorem nonhalting_unprovable (hcons:PA215.PA.Consistent):
    theory ⊬ HaltingFormula.nonhaltingSentence :=
  nonhalting_unprovable_of_internal_consistency_implication hcons pa_proves_nonhalting_consistency

#print pa_proves_nonhalting_consistency
#print nonhalting_unprovable
#print axioms pa_proves_nonhalting_consistency
#print axioms nonhalting_unprovable
end PA215.PA.InternalUnprovability
