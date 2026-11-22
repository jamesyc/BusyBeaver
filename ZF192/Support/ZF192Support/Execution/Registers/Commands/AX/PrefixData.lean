module
public import ZF192Support.Execution.Registers.Commands.AX.PlanRows0
public import ZF192Support.Execution.Registers.Commands.AX.PlanRows1
public import ZF192Support.Execution.Registers.Commands.AX.PlanRows2
public import ZF192Support.Execution.Registers.Commands.AX.PlanRows3
public import ZF192Support.Execution.Registers.Commands.AX.Symbolic

@[expose] public section

namespace ZF192Support.NativeAXSymbolic

/-- The AX program assembled from the decoded macro segments. -/
def program : List Op :=
    chunk00 ++ chunk01 ++ chunk02 ++ chunk03 ++ chunk04 ++
    chunk05 ++ chunk06 ++ chunk07 ++ chunk08 ++ chunk09 ++
    chunk10 ++ chunk11 ++ chunk12

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem program_actual : run program initial = some actualResult := by decide +kernel

end ZF192Support.NativeAXSymbolic
