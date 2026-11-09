module

public import User211PAMachine
public import User211PAStepFormula
public import PA211.UserCandidate.Dense

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.PA
/-- Direct binding of the arithmetic rows to the minimized candidate's literal control labels.
No sparse relabeling is needed to read this theorem. -/
theorem literal_arithmetic_binding : ∀ q : WorkingState, active q → ∀ b,
    Dense.machine q.val b = some ((row q b).write, (row q b).right,
      StepFormula.controlCode (row q b).next) := by decide +kernel
#print axioms literal_arithmetic_binding
end PA211.UserCandidate.PA
