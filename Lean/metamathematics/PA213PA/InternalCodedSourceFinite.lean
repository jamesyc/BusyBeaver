module

public import PA215PA.Theory
public import PA213PA.InternalCodedSourceDrainSpec

@[expose] public section
namespace PA213.PA.InternalTrace.CodedSource
open PA215 PA215.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def finiteRun : Nat → V → V
  | 0,a => a
  | n+1,a => finiteRun n (stepValue a)
theorem finiteRun_trace (n : Nat) (a : V) : ∃ cs,Trace (n:V) cs a (finiteRun n a) := by
  induction n generalizing a with
  | zero => exact ⟨?[a],by simpa [finiteRun] using trace_zero a⟩
  | succ n ih =>
    obtain ⟨cs,h⟩ := ih (stepValue a)
    obtain ⟨ds,hd⟩ := trace_prepend a rfl h
    exact ⟨ds,by simpa only [Nat.cast_add,Nat.cast_one,finiteRun] using hd⟩
#print axioms finiteRun_trace
end PA213.PA.InternalTrace.CodedSource

