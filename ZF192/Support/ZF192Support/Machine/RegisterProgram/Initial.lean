module
public import ZF192Support.Machine.RegisterProgram.Instructions
@[expose] public section
namespace RegisterMachine.Source
set_option maxRecDepth 100000

/-- The calibrated source state: site 25, logical register 0 (source register 6) equal to 2.
Only its nine-register projection is used. -/
def initialFile : List Nat := [0, 0, 0, 0, 0, 0, 2, 0, 0] ++ List.replicate 26 1
def initialState : State := ⟨25, 0, initialFile⟩

theorem initial_valid : Valid 4341 initialState := by
  constructor <;> decide +kernel
end RegisterMachine.Source
