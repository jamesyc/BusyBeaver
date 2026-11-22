module
public import ZF192Support.Execution.Registers.Commands.MP.Prefix
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.NativeMP
open ZF192Support.NativeSource ZF192Support.NativeCommands ZFR.ArithmeticRepresentation ZF192Support.ModelCommands RegisterMachine.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma return_to_fetch (n l t w d h:M) : nativeReaches
 (commandState 4328 n l 0 ⟨t,w,d,h⟩) (commandState 25 n l 0 ⟨t,w,d,h⟩) := by
 apply nativeReaches_step
 refine ⟨4328,by decide,rfl,.jump 25,by decide,?_⟩
 rfl
lemma success (n l w d:M) : nativeReaches
 (commandState 4302 n l 0 ⟨0,w,d,0⟩) (commandState 25 n l 0 ⟨d,modelCantor 0 w,d,0⟩) := by
 have a:=push NativePush.bound_4302 n l 0 w d 0
 have b:=copy NativeCopy.bound_4321 n l 0 (modelCantor 0 w) d 0
 rw [zero_add] at b
 exact nativeReaches_trans a (nativeReaches_trans b (return_to_fetch n l d (modelCantor 0 w) d 0))
end ZF192Support.NativeMP
