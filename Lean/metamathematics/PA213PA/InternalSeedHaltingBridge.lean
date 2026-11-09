module

public import PA215PA.Theory
public import PA213PA.InternalSeedPrefix159

@[expose] public section
namespace PA213.PA.InternalTrace.FixedTrace
open PA215 PA215.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open CodedSource
attribute [local irreducible] traceGraph frameGraph Step StepFormula.formula

def seedHaltsSentence : ArithmeticSentence :=
  “∃ a n cs b, !seedGraph a ∧ !traceGraph n cs a b ∧ !fstIdxDef 0 b”

def seedHaltingBridgeSentence : ArithmeticSentence :=
  “!seedHaltsSentence → !HaltingFormula.traceSentence”

/-- The clean AX seed and the actual startup intermediate are related by the
fixed159-step prefix, not identified as equal configurations. -/
theorem seed_halt_implies_blank {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
    {n cs b : V} (h : Trace n cs seedState b) (hb : control b=0) :
    V ⊧/![] HaltingFormula.traceSentence := by
  obtain ⟨k,ds,c,hc,hz⟩ := seed_halts_iff_intermediate.mp ⟨n,cs,b,h,hb⟩
  exact intermediate_halt_implies_blank hc hz

/-- Actual ordinary PA implication, with the literal clean seed as antecedent. -/
theorem pa_proves_seed_halting_bridge : theory ⊢ seedHaltingBridgeSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [seedHaltingBridgeSentence,models_iff]
  simp only [LogicalConnective.HomClass.map_imply]
  intro h
  have hs : ∃ n cs b : V, Trace n cs seedState b ∧ control b=0 := by
    simpa [seedHaltsSentence,seed_correct,trace_correct,fstIdx_defined.df,CodedSource.control,eq_comm] using h
  obtain ⟨n,cs,b,ht,hb⟩ := hs
  simpa using seed_halt_implies_blank ht hb
#print axioms seed_halt_implies_blank
#print axioms pa_proves_seed_halting_bridge
end PA213.PA.InternalTrace.FixedTrace

