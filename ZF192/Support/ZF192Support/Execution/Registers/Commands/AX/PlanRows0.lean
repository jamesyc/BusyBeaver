module
public import ZF192Support.Execution.Registers.Commands.AX.Scan

@[expose] public section
namespace ZF192Support.NativeAXSymbolic

set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

def chunk00 : List Op := (readPlan 24 50).getD []
theorem rows00 : checkPlan 50 chunk00 396 = true := by decide +kernel
def chunk01 : List Op := (readPlan 24 396).getD []
theorem rows01 : checkPlan 396 chunk01 752 = true := by decide +kernel
def chunk02 : List Op := (readPlan 24 752).getD []
theorem rows02 : checkPlan 752 chunk02 1056 = true := by decide +kernel
def chunk03 : List Op := (readPlan 24 1056).getD []
theorem rows03 : checkPlan 1056 chunk03 1354 = true := by decide +kernel

end ZF192Support.NativeAXSymbolic
