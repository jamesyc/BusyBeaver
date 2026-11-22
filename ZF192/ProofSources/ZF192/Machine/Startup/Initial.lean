module
public import ZF192Support.Machine.RegisterProgram.Projection

@[expose] public section
namespace M192.Calibration
open RegisterMachine.Source

/-- The prescribed contextual source seed in file order. -/
def sourceStart : ScalarState := ⟨22, fun r => if r = 0 then 2 else 0⟩

end M192.Calibration
