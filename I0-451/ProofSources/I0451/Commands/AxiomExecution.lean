module
public import I0451.Commands.AxiomCommand

@[expose] public section
namespace I0451.Runtime

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
theorem axiomBlock_checked :
    checkFormulaBlock 140 axCursor (symbolicInput true) (axiomPost (symbolicInput true)) = true := by
  decide +kernel

theorem literal_axiom (s : Registers) (firstZero : s scratchOne = 0) (secondZero : s scratchTwo = 0) :
    Executes (.branch axCursor) s .normal (axiomResult s) := by
  have ran := checkFormulaBlock_sound axiomBlock_checked s
  rw [eval_axiomPost, eval_symbolicInput _ firstZero secondZero] at ran
  exact ran

end I0451.Runtime
