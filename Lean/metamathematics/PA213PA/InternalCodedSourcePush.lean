module

public import PA215PA.Theory
public import PA213PA.InternalCodedSourcePushStores

@[expose] public section
namespace PA213.PA.InternalTrace.CodedSource
open PA215 PA215.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

/-- Full nineteen-row push, assembled from all-model source loops. -/
theorem push (offset : Nat) (hb : offset+44<3947)
    (bound : Source.AXPushParam.Bound Source.exactSites offset)
    (xs : V) (hv : ValidStore xs) (hx : registers xs 6=0) (hy : registers xs 7=0) :
    ∃ k cs, 0<k ∧ Trace k cs (stateCode ((offset+26:Nat):V) xs)
      (stateCode ((offset+45:Nat):V) (pushEnd xs)) := by
  have htw : registers (pushAfterT xs) 2=registers xs 2 := by
    rw [pushAfterT_registers xs hv hx];simp [PhysicalRegisters.write]
  have hwy : registers (pushAfterW xs) 7=0 := by
    rw [pushAfterW_registers xs hv hx];simpa [PhysicalRegisters.write] using hy
  have hpy : registers (pushAfterPair xs) 7=
      SourceCantorInternal.pairValue (registers xs 1) (registers xs 2) := by
    rw [pushAfterPair_registers xs hv hx];simp [PhysicalRegisters.write]
  obtain ⟨as,ha⟩ := push_drain_t offset hb bound (registers xs 1) xs hv rfl
  obtain ⟨bs,hb'⟩ := push_drain_w offset hb bound (registers xs 2) _ (pushAfterT_valid xs hv) htw
  obtain ⟨k,cs,hk,hc⟩ := pair offset (by omega) (push_pair_bound offset bound) _ (pushAfterW_valid xs hv) hwy
  obtain ⟨ds,hd⟩ := push_drain_y offset hb bound _ _ (pushAfterPair_valid xs hv) hpy
  rw [pushEnd_composition xs hv hx hy] at hd
  obtain ⟨es,he⟩ := trace_compose ha hb'
  obtain ⟨fs,hf⟩ := trace_compose he hc
  obtain ⟨gs,hg⟩ := trace_compose hf hd
  refine ⟨_,gs,?_,hg⟩
  have hp : 0 < 3*SourceCantorInternal.pairValue (registers xs 1) (registers xs 2)+1 := by simp
  exact lt_of_lt_of_le hp (by simp)
#print axioms push
end PA213.PA.InternalTrace.CodedSource

