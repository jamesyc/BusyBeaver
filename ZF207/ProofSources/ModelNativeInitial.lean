module
public import ModelNativeSummaryHistory
public import M207.SourceInitial
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativeCommands
open ZF207.NativeSource ZF207.ModelCommands ZFR.ArithmeticRepresentation ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def nativeInitial : State M := ⟨25,![0,0,0,0,0,0,2,0,0]⟩
lemma nativeInitial_scheduler : nativeInitial (M:=M)=commandState 25 2 0 0 ⟨0,0,0,0⟩ := rfl
/-- Produces a rooted native trace from the exact initial nine-register state.
Successful MP/AX native bodies remain the explicit premise. -/
theorem literalCRefutation_initial_native_history (hc:successBodyContract (M:=M))
 (h:ZF207.ModelCommands.compilable (1:M)) :
 ∃hist:M,∃stop:State M,nativeRunHistory (stateCode nativeInitial) hist ∧
 modelListHead hist=stateCode stop ∧ stop.pc=10 := by
 obtain ⟨stop,hpc,hr⟩:=literalCRefutation_native_halt hc h (storeCode (⟨0,0,0,0⟩:Store M))
 rw [storeDecode_code,←nativeInitial_scheduler] at hr
 obtain ⟨hist,hh,he⟩:=hr (stateCode nativeInitial) (modelListCons (stateCode nativeInitial) 0)
  (nativeRunHistory_singleton _) (modelListHead_cons _ _)
 exact ⟨hist,stop,hh,he,hpc⟩
end ZF207.NativeCommands
