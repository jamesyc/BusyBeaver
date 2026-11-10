import PA215PA.CommandInvariant
import PA215PA.NativeSoundness

/-! Discharge the arithmetic interpreter's no-refutation premise using the
actual native-to-PA proof, not a new supplier. The arithmetic-command prefix
credit hypothesis is explicit until joined to the literal enumerated schedule.
Literal source/machine simulation is NOT asserted by this module. -/
namespace PA215.PA.CommandSemantics
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open PA215.Source PA215.Source.Enumeration NativeCalculus

theorem no_native_refutation (hcons : PA215.PA.Consistent) : ¬ Proved 1 := by
  letI : FFL.Entailment.Consistent theory := hcons
  intro h
  have hbot : theory ⊬ (⊥ : ArithmeticSentence) := FFL.Entailment.Consistent.not_bot
  exact hbot (NativeHFS.native_refutation_PA_bottom h)

/-- The completed initial AX command: saved unsafe1 over initial1 is opaque4.
Only nine freshly proved heads are included in the wrapper invariant. -/
def initialCommandState : State :=
  ⟨AXCode.gate 0 0 0,AXCode.outputStack 0 0 0 0 0 1 1,0,0⟩

theorem initial_command_invariant : Invariant 4 9 initialCommandState := by
  constructor
  · exact ⟨core_gate_proved 0 0 0,⟨.truth⟩⟩
  · have hheads := core_heads_proved 0 0 0 0 0 (by omega) (show Proved 0 from ⟨.truth⟩)
    have hw := WrapperStack.initial_nine (P := Proved)
      (heads := AXCode.pa135Heads 0 0 0 0 0) (by rfl) hheads
    simpa only [initialCommandState,AXCode.outputStack,AXCode.stackCode,WrapperStack.encode] using hw

theorem run_safe_of_PA_consistency (hcons : PA215.PA.Consistent) (cs : List Command)
    (hcredit : ∀ p r, cs = p ++ r → (-3 : Int) ≤ weight p) :
    ∃ out depth, run cs initialCommandState = some out ∧ Invariant 4 depth out ∧ 6 ≤ depth := by
  obtain ⟨out,depth,hr,hi,hbound⟩ := run_invariant (no_native_refutation hcons)
    cs initialCommandState 4 9 initial_command_invariant (fun p r he => by
      have hc := hcredit p r he
      omega)
  have hc := hcredit cs [] (by simp)
  exact ⟨out,depth,hr,hi,by omega⟩

theorem no_command_halt_of_PA_consistency (hcons : PA215.PA.Consistent) (cs : List Command)
    (hcredit : ∀ p r, cs = p ++ r → (-3 : Int) ≤ weight p) :
    run cs initialCommandState ≠ none := by
  obtain ⟨out,depth,hr,_,_⟩ := run_safe_of_PA_consistency hcons cs hcredit
  simp [hr]

#print axioms no_native_refutation
#print axioms initial_command_invariant
#print axioms run_safe_of_PA_consistency
end PA215.PA.CommandSemantics
