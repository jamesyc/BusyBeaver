import PA215PA.InternalCodedSourceNatView
import PA215PA.InternalCodedSourcePhysicalStep
import PA215PA.InternalCodedSourceTraceCompose
set_option maxRecDepth 100000
namespace PA215.PA.InternalTrace.CodedSource
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
attribute [local irreducible] Source.exactSites

def SourceValid (c : Source.Configuration) : Prop :=
  c.control≠.exited ∧ controlCode c.control<3948

lemma encodeSource_valid (c : Source.Configuration) (h : SourceValid c) : ValidState (encodeSource c) := by
  refine ⟨encodeSource_store_valid c,?_⟩
  have hc := (coe_coe_lt (M := Nat) (n := controlCode c.control) (m := 3948)).mpr h.2
  simpa only [encodeSource,control_state,natCast_nat,Nat.cast_ofNat] using hc

lemma encodeSource_step (c : Source.Configuration) (h : SourceValid c) :
    stepValue (encodeSource c)=encodeSource (Source.cycleStep Source.exactSites c) := by
  cases c with
  | mk q rs =>
    cases q with
    | «at» i =>
      have hi : i<3947 := by have hb : i+1<3948 := h.2; omega
      have hc := step_cyclic_calibration (encodeSource ⟨.at i,rs⟩) i hi
        (by simp only [encodeSource,control_state,controlCode,natCast_nat]) (encodeSource_store_valid _)
      rw [encodeSource_registers] at hc
      simp only [natCast_nat] at hc
      change control (stepValue (encodeSource ⟨.at i,rs⟩))=
          (controlCode (ModelSource.cycleStep (natView ⟨.at i,rs⟩)).control : Nat) ∧
        registers (store (stepValue (encodeSource ⟨.at i,rs⟩)))=
          (ModelSource.cycleStep (natView ⟨.at i,rs⟩)).registers at hc
      rw [cycle_natView] at hc
      apply state_ext (step_valid _ (encodeSource_valid _ h)).1 (encodeSource_store_valid _)
      · simpa only [encodeSource,control_state,natView,natCast_nat] using hc.1
      · rw [encodeSource_registers]; exact hc.2
    | halted => simp [encodeSource,controlCode,step_halted,Source.cycleStep,Source.step,Source.restart]
    | exited => exact False.elim (h.1 rfl)
    | malformed => exact False.elim ((Nat.lt_irrefl 3948) h.2)

lemma sourceValid_step (c : Source.Configuration) (h : SourceValid c) :
    SourceValid (Source.cycleStep Source.exactSites c) := by
  constructor
  · unfold Source.cycleStep
    cases hs : Source.step Source.exactSites c with
    | mk q rs => cases q <;> simp [Source.restart]
  · have hv := (step_valid (encodeSource c) (encodeSource_valid c h)).2
    rw [encodeSource_step c h] at hv
    apply (coe_coe_lt (M := Nat)).mp
    simpa only [encodeSource,control_state,natCast_nat,Nat.cast_ofNat] using hv

/-- Exact external finite source proofs calibrate to standard coded traces.
Nonstandard execution is handled separately by the internal Trace theorems. -/
theorem cycles_to_trace {n : Nat} {a b : Source.Configuration}
    (h : Source.CycleSteps Source.exactSites n a b) (ha : SourceValid a) :
    ∃ cs : Nat, Trace n cs (encodeSource a) (encodeSource b) := by
  induction h with
  | refl a => exact ⟨_,trace_zero _⟩
  | @cons n a b h ih =>
    obtain ⟨cs,hcs⟩ := ih (sourceValid_step a ha)
    exact trace_prepend (encodeSource a) (encodeSource_step a ha) hcs

#print axioms encodeSource_step
#print axioms sourceValid_step
#print axioms cycles_to_trace
end PA215.PA.InternalTrace.CodedSource
