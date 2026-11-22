module
public import ZF192Support.Execution.Registers.Commands.AX.Scan

@[expose] public section
namespace ZF192Support.NativeAXSymbolic

set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

def chunk08 : List Op := (readPlan 24 2584).getD []
theorem rows08 : checkPlan 2584 chunk08 2904 = true := by decide +kernel
def chunk09 : List Op := (readPlan 24 2904).getD []
theorem rows09 : checkPlan 2904 chunk09 3226 = true := by decide +kernel
def chunk10 : List Op := (readPlan 24 3226).getD []
theorem rows10 : checkPlan 3226 chunk10 3566 = true := by decide +kernel
def chunk11 : List Op := (readPlan 24 3566).getD []
theorem rows11 : checkPlan 3566 chunk11 3902 = true := by decide +kernel

end ZF192Support.NativeAXSymbolic
