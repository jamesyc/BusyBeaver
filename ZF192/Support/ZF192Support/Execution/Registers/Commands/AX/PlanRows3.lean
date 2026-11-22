module
public import ZF192Support.Execution.Registers.Commands.AX.Scan

@[expose] public section
namespace ZF192Support.NativeAXSymbolic

set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

def chunk12 : List Op := (readPlan 17 3902).getD []
theorem rows12 : checkPlan 3902 chunk12 4187 = true := by decide +kernel

end ZF192Support.NativeAXSymbolic
