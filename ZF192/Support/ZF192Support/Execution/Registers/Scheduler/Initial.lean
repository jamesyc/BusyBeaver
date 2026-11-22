module
public import ZF192Support.Execution.Registers.Scheduler.SummaryHistory
public import ZF192Support.Machine.RegisterProgram.Initial
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.NativeCommands
open ZF192Support.NativeSource ZF192Support.ModelCommands ZFR.ArithmeticRepresentation ZF192Support.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def nativeInitial : State M := ⟨25,![0,0,0,0,0,0,2,0,0]⟩
lemma nativeInitial_scheduler : nativeInitial (M:=M)=commandState 25 2 0 0 ⟨0,0,0,0⟩ := rfl
/-- Produces a rooted native trace from the exact initial nine-register state.
Successful MP/AX native bodies remain the explicit premise. -/
theorem literalCRefutation_initial_native_history (hc:successBodyContract (M:=M))
 (h:ZF192Support.ModelCommands.compilable (1:M)) :
 ∃hist:M,∃stop:State M,nativeRunHistory (stateCode nativeInitial) hist ∧
 modelListHead hist=stateCode stop ∧ stop.pc=10 := by
 obtain ⟨stop,hpc,hr⟩:=literalCRefutation_native_halt hc h (storeCode (⟨0,0,0,0⟩:Store M))
 rw [storeDecode_code,←nativeInitial_scheduler] at hr
 obtain ⟨hist,hh,he⟩:=hr (stateCode nativeInitial) (modelListCons (stateCode nativeInitial) 0)
  (nativeRunHistory_singleton _) (modelListHead_cons _ _)
 exact ⟨hist,stop,hh,he,hpc⟩
end ZF192Support.NativeCommands
