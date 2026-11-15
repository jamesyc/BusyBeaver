module
public import ModelNativePhysicalLiftComplete
public import ModelNativeInitialComplete
public import ModelNativeFrameEffects
public import ModelCRefutationSentence
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativePhysicalLift
open ZFR.ArithmeticRepresentation ZF209.NativeSource ZF209.NativeCommands
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma initial_frame_relation : FrameRelation (stateCode (nativeInitial (M:=M)))
 (BinaryTape.stateCode (BinaryTape.nativeFrame 25 0 (nativeInitial (M:=M)).registers 26)) := by
 refine ⟨25,by decide,0,25,(nativeInitial (M:=M)).registers,rfl,?_⟩
 congr 2
lemma halt_frame (coverage:Coverage (M:=M)) (stop:State M) (hstop:stop.pc=10) (hist q:M)
 (hh:BinaryTape.runHistory BinaryTape.blankCode hist) (he:modelListHead hist=q)
 (hr:FrameRelation (stateCode stop) q) : BinaryTape.physicalHalts (M:=M) := by
 obtain ⟨pc,hpc,gap,spares,regs,ha,hb⟩:=hr
 have hs:=native_code_injective ha
 have hp:(pc:M)=(10:Nat):=by simpa [hstop] using (congrArg State.pc hs).symm
 have hp':pc=10:=cast_injective hp
 subst pc
 obtain ⟨code,hcode,himpl⟩:=coverage 10 (by decide)
 have hrow:M209.Source.program 10=some .halt:=by decide +kernel
 rw [hrow] at hcode
 have hc:code=M209.Source.Instruction.halt:=Option.some.inj hcode.symm
 subst code
 exact himpl gap spares regs hist hh (he.trans hb)
theorem literalCRefutation_physical_of_coverage (coverage:Coverage (M:=M))
 (h:ZF209.ModelCommands.compilable (1:M)) : BinaryTape.physicalHalts (M:=M) := by
 obtain ⟨nativeHist,stop,hnative,hend,hstop⟩:=literalCRefutation_initial_native_history_unconditional h
 obtain ⟨hist,hh,he⟩:=BinaryTape.blank_to_native_initial_frame (M:=M)
 obtain ⟨out,q,ho,hq,hr⟩:=frame_history_lift coverage (stateCode (nativeInitial (M:=M))) nativeHist hnative
  BinaryTape.blankCode hist _ hh he initial_frame_relation
 rw [hend] at hr
 exact halt_frame coverage stop hstop out q ho hq hr

end ZF209.NativePhysicalLift
