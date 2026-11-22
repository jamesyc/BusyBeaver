module
public import ZF192.Machine.Startup
public import ZF192.Machine.FrameLayout
public import ZF192.Machine.Startup.Initial

@[expose] public section
namespace M192.Startup
open BinaryTape M192.Calibration

set_option maxRecDepth 100000
set_option maxHeartbeats 64000000

/-- The padding outside the fixed 38-cell program window. -/
def startupPadding : Nat := 47

/-- The 112 cells to the right of the guard endpoint at the blank-run checkpoint. -/
def rightTail : List Bool :=
  [false, false, false, true, true, true, false, false, true, true, true, true, true, true, false, false,
   true, true, true, true, false, true, true, false, true, true, true, true, false, true, true, false,
   true, true, false, false, true, true, true, true, true, true, false, false, true, false, false, true,
   true, false, true, true, false, false, true, true, true, true, true, true, true, true, true, true,
   true, true, true, true, true, true, true, true, false, true, true, true, false, true, true, true,
   true, true, true, false, true, true, true, true, true, true, true, true, true, false, true, true,
   true, true, false, true, true, false, true, true, false, false, true, true, true, true, true, true]

theorem final_exact : unpack checkpoint5 = frameN sourceStart.pc sourceStart.registers startupPadding rightTail := by
  decide +kernel

theorem blank_to_frame :
    Reach literal (zc 0 [] []) (frameN sourceStart.pc sourceStart.registers startupPadding rightTail) :=
  ⟨44181, by simpa only [final_exact] using startup_exact⟩

end M192.Startup
