module
public import ModelNativeCommandLift
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativeCommands
open ZF209.NativeSource ZF209.ModelCommands ZFR.ArithmeticRepresentation ZF209.MM0ModelPeano ModelOperationalConcat
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma nativeReaches_refl (s:State M) : nativeReaches s s := by
 intro initial hist hr hh;exact ⟨hist,hr,hh⟩
end ZF209.NativeCommands
