module
public import ZF192Support.Execution.Registers.Scheduler.CommandLift
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.NativeCommands
open ZF192Support.NativeSource ZF192Support.ModelCommands ZFR.ArithmeticRepresentation ZF192Support.MM0ModelPeano ModelOperationalConcat
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma nativeReaches_refl (s:State M) : nativeReaches s s := by
 intro initial hist hr hh;exact ⟨hist,hr,hh⟩
end ZF192Support.NativeCommands
