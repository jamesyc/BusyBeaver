import PA215PA.InternalStartupFrame
import PA215PA.InternalCodedSourcePhysicalTrace
import PA215PA.InternalTraceProjection
namespace PA215.PA.InternalTrace.FixedTrace
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open CodedSource
attribute [local irreducible] traceGraph frameGraph Step StepFormula.formula

def entryGraph : 𝚺ᴬ₁.Semisentence 1 := .mkSigma
  “c. ∃ regs, !(fixedFileGraph startupRegisters) regs ∧ !adjoinDef c 69 regs”

def intermediateHaltsSentence : ArithmeticSentence :=
  “∃ a n cs b, !entryGraph a ∧ !traceGraph n cs a b ∧ !fstIdxDef 0 b”

def blankHaltingBridgeSentence : ArithmeticSentence :=
  “!intermediateHaltsSentence → !HaltingFormula.traceSentence”

section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
lemma entry_correct (v : Fin 1 → V) : (V ⊧/v entryGraph.val) ↔ v 0=entryState := by
  simp [entryGraph,fixedFile_correct,adjoin_defined.df,entryState,stateCode,numeral_eq_natCast,Nat.cast_ofNat]

/-- Fixed startup followed by the proved nonstandard source-to-machine trace
refinement. The initial intermediate AX store and every spare remain exact. -/
theorem intermediate_halt_implies_blank {n cs b : V}
    (h : Trace n cs entryState b) (hb : control b=0) :
    V ⊧/![] HaltingFormula.traceSentence := by
  obtain ⟨qs,ls,rs,hstart⟩ := startup_all_models (V := V)
  obtain ⟨k,qh,lh,rh,lf,rf,hpos,hhalt⟩ :=
    trace_halt_physical h (startup_refines_all_models (V := V)) hb
  obtain ⟨qall,lall,rall,hall⟩ := segment_compose hstart hhalt
  exact prefix_halts (show Prefix (63228+k) qall lall rall 215 lf rf from hall)
end Models

/-- Ordinary PA proves the exact intermediate source-halt implication for the
original dense215 blank machine, using two fixed closed Sigma-one proofs. -/
theorem pa_proves_blank_halting_bridge : theory ⊢ blankHaltingBridgeSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [blankHaltingBridgeSentence,models_iff]
  simp only [LogicalConnective.HomClass.map_imply]
  intro h
  have hs : ∃ n cs b : V, Trace n cs entryState b ∧ control b=0 := by
    simpa [intermediateHaltsSentence,entry_correct,trace_correct,fstIdx_defined.df,CodedSource.control,eq_comm] using h
  obtain ⟨n,cs,b,ht,hb⟩ := hs
  simpa using intermediate_halt_implies_blank ht hb
#print axioms intermediate_halt_implies_blank
#print axioms pa_proves_blank_halting_bridge
end PA215.PA.InternalTrace.FixedTrace
