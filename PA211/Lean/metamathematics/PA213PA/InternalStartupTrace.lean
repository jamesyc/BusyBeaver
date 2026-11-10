import PA213PA.InternalFixedTraceSigma
import PA213PA.Startup.Data
import PA213PA.TraceAdequacy
namespace PA213.PA.InternalTrace.FixedTrace
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open HaltingFormula
attribute [local irreducible] Step StepFormula.formula

private lemma len_prefix (n : Nat) (f : Nat → Nat) : len (encodePrefix n f)=n := by
  induction n generalizing f with
  | zero => simp [encodePrefix]
  | succ n ih => simp [encodePrefix,ih]

/-- Standard finite execution supplies a witness for the existing HFS Segment.
The construction is used only before fixed Sigma-one completeness. -/
theorem run_segment (n : Nat) (c d : NatTape.Configuration)
    (h : NatTape.run n c=some d) :
    ∃ qs ls rs : Nat, Segment n qs ls rs (StepFormula.controlCode c.control) c.left c.right
      (StepFormula.controlCode d.control) d.left d.right := by
  obtain ⟨f,h0,hn,hs⟩ := (run_iff_path n c d).mp h
  let qs := encodePrefix (n+1) (fun i => StepFormula.controlCode (f i).control)
  let ls := encodePrefix (n+1) (fun i => (f i).left)
  let rs := encodePrefix (n+1) (fun i => (f i).right)
  have hq (i : Nat) (hi : i≤n) : qs.[i]=StepFormula.controlCode (f i).control :=
    nth_encodePrefix _ _ _ (by omega)
  have hl (i : Nat) (hi : i≤n) : ls.[i]=(f i).left := nth_encodePrefix _ _ _ (by omega)
  have hr (i : Nat) (hi : i≤n) : rs.[i]=(f i).right := nth_encodePrefix _ _ _ (by omega)
  refine ⟨qs,ls,rs,len_prefix _ _,len_prefix _ _,len_prefix _ _,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hq 0 (by omega),h0]
  · rw [hl 0 (by omega),h0]
  · rw [hr 0 (by omega),h0]
  · rw [hq n (by omega),hn]
  · rw [hl n (by omega),hn]
  · rw [hr n (by omega),hn]
  · intro i hi
    rw [hq i (by omega),hl i (by omega),hr i (by omega),
      hq (i+1) (by omega),hl (i+1) (by omega),hr (i+1) (by omega)]
    unfold Step
    exact (StepFormula.formula_correct _ _ _ _ _ _).mpr
      ((StepFormula.relation_iff_step _ _).mpr (hs i hi))

/-- Reuses the exact already checked 64,764-step startup, not a new trajectory. -/
theorem startup_segment : ∃ qs ls rs : Nat, Segment 64764 qs ls rs 0 0 0
    81 1 Startup.finalConfig.right := by
  have h := run_segment 64764 NatTape.blank Startup.finalConfig Startup.blank_run_64764
  simpa [NatTape.blank, StepFormula.controlCode, start, target, Startup.final_control, Startup.final_left] using h

def startupSentence : ArithmeticSentence := sentence 64764 81 1 Startup.finalConfig.right

/-- Fixed closed arithmetic startup execution is provable in ordinary PA. -/
theorem pa_proves_startup : theory ⊢ startupSentence :=
  pa_proves_fixed 64764 81 1 Startup.finalConfig.right startup_segment

/-- This all-model consequence comes from the proved fixed sentence, not from
silently applying a standard Nat trajectory to arbitrary model inputs. -/
theorem startup_all_models {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory] :
    ∃ qs ls rs : V, Segment 64764 qs ls rs 0 0 0 81 1 (Startup.finalConfig.right : V) := by
  have h := consequence_iff.mp (Theory.Proof.sound pa_proves_startup) V inferInstance
  simpa [startupSentence,sentence,models_iff,segment_correct,numeral_eq_natCast,Nat.cast_ofNat] using h
#print axioms run_segment
#print axioms startup_segment
#print axioms pa_proves_startup
#print axioms startup_all_models
end PA213.PA.InternalTrace.FixedTrace

