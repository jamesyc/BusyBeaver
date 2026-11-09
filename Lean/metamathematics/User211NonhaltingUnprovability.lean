import User211RefutationHalting
import PA215PA.InternalActualRefutationConsistency
import PA215PA.Foundation
import User211EndpointExactHaltingFormula
import PA211.UserCandidate.StateBound
namespace PA211.UserCandidate.PA.InternalUnprovability
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

theorem pa_proves_auxiliary_nonhalting_consistency :
    theory ⊢ HaltingFormula.nonhaltingSentence 🡒 PA215.PA.consistencySentence := by
  have h : theory ⊢ HaltingFormula.nonhaltingSentence 🡒 InternalActualRefutation.noActualRefutationSentence := by
    simpa [InternalActualRefutation.nonhaltingNoActualRefutationSentence,Rewriting.subst] using
      InternalActualRefutation.pa_proves_nonhalting_no_actual_refutation
  have hc : theory ⊢ InternalActualRefutation.noActualRefutationSentence 🡒 PA215.PA.consistencySentence := by
    simpa only [InternalActualRefutation.noActualRefutationSentence,
      PA215.PA.InternalActualRefutation.noActualRefutationSentence] using
      PA215.PA.InternalActualRefutation.pa_proves_no_actual_refutation_consistency
  exact C_trans h hc

/-- Ordinary first-order PA proves that nonhalting of the exact 422-row
physical machine implies the usual arithmetized consistency sentence for PA.
The auxiliary 430-row encoding is eliminated by an all-model invariant. -/
theorem pa_proves_nonhalting_consistency :
    theory ⊢ ExactHaltingFormula.nonhaltingSentence 🡒 PA215.PA.consistencySentence :=
  C_trans ExactHaltingFormula.pa_proves_exact_to_auxiliary
    pa_proves_auxiliary_nonhalting_consistency

/-- One-sided unprovability under ordinary PA consistency. -/
theorem nonhalting_unprovable (hcons : PA215.PA.Consistent) :
    theory ⊬ ExactHaltingFormula.nonhaltingSentence :=
  PA215.PA.unprovable_of_internal_consistency_implication _ hcons pa_proves_nonhalting_consistency

/-- Standard-model truth of the same literal physical-machine sentence. -/
theorem nonhalting_true (hcons : PA215.PA.Consistent) :
    Nat ⊧/![] ExactHaltingFormula.nonhaltingSentence :=
  ExactHaltingFormula.sentence_iff_physical_nonhalting.mpr
    (PA211.UserCandidate.PA.consistent_machine_nonhalting hcons)

/-- The actual partial transition function has a domain contained in the
specified list of exactly 211 distinct physical working controls. -/
theorem physical_state_bound :
    CandidateTable.workingLabels.length = 211 ∧
    CandidateTable.workingLabels.Nodup ∧
    ∀ q b, CandidateTable.machine q b ≠ none → q ∈ CandidateTable.workingLabels :=
  ⟨CandidateTable.working_count, CandidateTable.working_nodup,
    fun _ _ h => PA211.UserCandidate.StateBound.domain h⟩

/-- The concrete 211-state binary machine is nonhalting, and its exact
422-row arithmetic nonhalting sentence is unprovable in ordinary PA,
assuming ordinary PA is consistent. This does not assert two-sided
independence from consistency alone. -/
theorem final_endpoint (hcons : PA215.PA.Consistent) :
    (CandidateTable.workingLabels.length = 211 ∧
      CandidateTable.workingLabels.Nodup ∧
      ∀ q b, CandidateTable.machine q b ≠ none → q ∈ CandidateTable.workingLabels) ∧
    ExactHaltingFormula.rows.length = 422 ∧
    (¬ PA215.Zip.Halts CandidateTable.machine PA213.Startup.blank) ∧
    (Nat ⊧/![] ExactHaltingFormula.nonhaltingSentence) ∧
    (theory ⊬ ExactHaltingFormula.nonhaltingSentence) :=
  ⟨physical_state_bound, ExactHaltingFormula.rows_count,
    PA211.UserCandidate.PA.consistent_machine_nonhalting hcons,
    nonhalting_true hcons, nonhalting_unprovable hcons⟩

#print axioms physical_state_bound
#print axioms final_endpoint
#print axioms nonhalting_true
#print pa_proves_nonhalting_consistency
#print nonhalting_unprovable
#print axioms pa_proves_nonhalting_consistency
#print axioms nonhalting_unprovable
end PA211.UserCandidate.PA.InternalUnprovability
