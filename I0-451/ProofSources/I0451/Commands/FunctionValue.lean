module
public import I0451.Commands.Symbolic

/-! The shared function-evaluation formula macro is checked once.
Its contract is reused at every literal invocation in EXTRA. -/
@[expose] public section
namespace I0451.Runtime

def valueCursor : Cursor := ⟨279, true, true⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
theorem valueBlock_checked :
    checkFormulaBlock 95 valueCursor (symbolicInput true)
      (Operation.functionValue.symbolic (symbolicInput true)) = true := by
  decide +kernel

theorem literal_value (s : Registers) (clean : Operation.functionValue.applicable s) :
    Executes (.branch valueCursor) s .normal (Operation.functionValue.apply s) := by
  obtain ⟨z₁, z₂⟩ := clean rfl
  have ran := checkFormulaBlock_sound valueBlock_checked s
  rw [Operation.eval_symbolic, eval_symbolicInput _ z₁ z₂] at ran
  exact ran

def extraBlocks : List ClosedBlock :=
  ⟨valueCursor, .functionValue, literal_value⟩ :: formulaBlocks

end I0451.Runtime
