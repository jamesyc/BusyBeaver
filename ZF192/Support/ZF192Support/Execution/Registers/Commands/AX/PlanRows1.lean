module
public import ZF192Support.Execution.Registers.Commands.AX.Scan

@[expose] public section
namespace ZF192Support.NativeAXSymbolic

set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

def chunk04 : List Op := (readPlan 24 1354).getD []
theorem rows04 : checkPlan 1354 chunk04 1696 = true := by decide +kernel
def chunk05 : List Op := (readPlan 24 1696).getD []
theorem rows05 : checkPlan 1696 chunk05 1988 = true := by decide +kernel
def chunk06 : List Op := (readPlan 24 1988).getD []
theorem rows06 : checkPlan 1988 chunk06 2310 = true := by decide +kernel
def chunk07 : List Op := (readPlan 24 2310).getD []
theorem rows07 : checkPlan 2310 chunk07 2584 = true := by decide +kernel

end ZF192Support.NativeAXSymbolic
