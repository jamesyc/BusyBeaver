module
public import ZF192Support.Execution.Registers.Scheduler.Initial
public import ZF192Support.Execution.Registers.Commands.AllBodies
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.NativeCommands
open ZF192Support.NativeSource ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
theorem literalCRefutation_initial_native_history_unconditional
 (h:ZF192Support.ModelCommands.compilable (1:M)) :
 ∃hist:M,∃stop:State M,nativeRunHistory (stateCode (nativeInitial (M:=M))) hist ∧
 modelListHead hist=stateCode stop ∧ stop.pc=10 :=
 literalCRefutation_initial_native_history successBodyContract_proved h
end ZF192Support.NativeCommands
