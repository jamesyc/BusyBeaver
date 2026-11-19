module
public import ModelNativeInitial
public import ModelNativeBodiesComplete
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativeCommands
open ZF207.NativeSource ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
theorem literalCRefutation_initial_native_history_unconditional
 (h:ZF207.ModelCommands.compilable (1:M)) :
 ∃hist:M,∃stop:State M,nativeRunHistory (stateCode (nativeInitial (M:=M))) hist ∧
 modelListHead hist=stateCode stop ∧ stop.pc=10 :=
 literalCRefutation_initial_native_history successBodyContract_proved h
end ZF207.NativeCommands
