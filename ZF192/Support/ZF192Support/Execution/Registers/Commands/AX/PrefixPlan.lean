module
public import ZF192Support.Execution.Registers.Commands.AX.PlanCheck
public import ZF192Support.Execution.Registers.Commands.AX.PrefixData

@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace ZF192Support.NativeAXSymbolic

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem prefix_realizes : RealizesPlan (M := M) 50 program 4187 := by
  simp only [program, List.append_assoc]
  exact (checkPlan_sound rows00).append <|
    (checkPlan_sound rows01).append <|
    (checkPlan_sound rows02).append <|
    (checkPlan_sound rows03).append <|
    (checkPlan_sound rows04).append <|
    (checkPlan_sound rows05).append <|
    (checkPlan_sound rows06).append <|
    (checkPlan_sound rows07).append <|
    (checkPlan_sound rows08).append <|
    (checkPlan_sound rows09).append <|
    (checkPlan_sound rows10).append <|
    (checkPlan_sound rows11).append <|
    checkPlan_sound rows12

end ZF192Support.NativeAXSymbolic
