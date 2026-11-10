import User211NonhaltingUnprovability
import PA211.UserCandidate.Dense
import User211LiteralArithmeticBinding
namespace PA211.UserCandidate.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
/-- The minimized 211-state/422-row table, literal labels and blank tape.
The consistency assumption is ordinary PA. This is one-sided unprovability. -/
theorem literal_final_endpoint (hcons : PA215.PA.Consistent) :
    CandidateTable.workingDense.length = 211 ∧
    CandidateTable.workingDense.length * 2 = 422 ∧
    (¬ PA215.Zip.Halts Dense.machine (PA215.Zip.zc 0 [] [])) ∧
    ExactHaltingFormula.rows.length = 422 ∧
    (Nat ⊧/![] ExactHaltingFormula.nonhaltingSentence) ∧
    (theory ⊬ ExactHaltingFormula.nonhaltingSentence) := by
  refine ⟨Dense.working_count, Dense.defined_row_count, consistent_literal_nonhalting hcons,
    ExactHaltingFormula.rows_count, InternalUnprovability.nonhalting_true hcons,
    InternalUnprovability.nonhalting_unprovable hcons⟩
#print axioms literal_final_endpoint
end PA211.UserCandidate.PA
