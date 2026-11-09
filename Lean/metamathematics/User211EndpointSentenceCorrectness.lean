/- Exact211: fresh physical interpretation of the unchanged original coded source. -/
import User211EndpointTraceAdequacy
import User211EndpointPhysicalAdequacy
import User211ConsistentNonhalting
namespace PA211.UserCandidate.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
/-- The arithmetic sentence is semantically faithful to the exact 422-row,
211-control physical table, not only to the auxiliary total dense-tag table. -/
theorem sentence_iff_physical_nonhalting :
    (Nat ⊧/![] HaltingFormula.nonhaltingSentence) ↔
      ¬ PA215.Zip.Halts CandidateTable.machine PA213.Startup.blank := by
  rw [HaltingFormula.nonhaltingSentence_iff, ← NatTape.blank_halts_iff]
  exact not_congr PhysicalAdequacy.blank_halts_iff.symm

theorem consistent_sentence_true (hcons : PA215.PA.Consistent) :
    Nat ⊧/![] HaltingFormula.nonhaltingSentence :=
  sentence_iff_physical_nonhalting.mpr (consistent_machine_nonhalting hcons)
#print axioms sentence_iff_physical_nonhalting
#print axioms consistent_sentence_true
end PA211.UserCandidate.PA
