module
public import ModelNativeAXBindings5
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativeAXSymbolic
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
theorem op_300 : Realizes (M:=M) .cons 4086 4113 := by
 apply cons_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_301 : Realizes (M:=M) .cons 4113 4140 := by
 apply cons_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_302 : Realizes (M:=M) .push 4140 4159 := by
 apply push_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_303 : Realizes (M:=M) .incT 4159 4160 := by
 apply incT_realizes
 all_goals repeat' first | (solve | decide) | constructor
theorem op_304 : Realizes (M:=M) .cons 4160 4187 := by
 apply cons_realizes
 all_goals repeat' first | (solve | decide) | constructor
end ZF209.NativeAXSymbolic
