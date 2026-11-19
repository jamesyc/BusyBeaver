module
public import ModelNativeCommandLift
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativeCommands
open ZF207.NativeSource ZF207.ModelCommands ZFR.ArithmeticRepresentation ZF207.MM0ModelPeano ModelOperationalConcat
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma nativeReaches_refl (s:State M) : nativeReaches s s := by
 intro initial hist hr hh;exact ⟨hist,hr,hh⟩
end ZF207.NativeCommands
