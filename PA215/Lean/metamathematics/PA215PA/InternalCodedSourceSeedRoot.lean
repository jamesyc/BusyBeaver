import PA215PA.InternalAXCommandStore
import PA215PA.InternalCodedSourceCommandBlocks
import PA215PA.InternalSeedPrefix159
namespace PA215.PA.InternalTrace.CodedSource
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def cleanSeedStore : V := FixedTrace.fixedFile FixedTrace.seedRegisters
lemma cleanSeedStore_valid : ValidStore (cleanSeedStore (V:=V)) := by
  simp [cleanSeedStore,ValidStore,FixedTrace.fixedFile_length,FixedTrace.seedRegisters]
lemma cleanSeedStore_registers : registers (cleanSeedStore (V:=V))=![0,1,1,0,0,0,0,0,0] := by
  simp [cleanSeedStore,registers,FixedTrace.fixedFile_nth,FixedTrace.seedRegisters,
    funext_iff,Fin.forall_fin_succ]

/-- The fixed clean AX seed first reaches the literal root with arbitrary
arithmetic command state. No equality to a reset arithmetic state is needed. -/
theorem seed_to_root : ∃ k cs xs : V,0<k ∧
    Trace k cs FixedTrace.seedState (stateCode 1 xs) ∧
    ValidStore xs ∧ CommandClean xs ∧ registers xs 0=0 ∧ registers xs 8=0 := by
  have hx : registers (cleanSeedStore (V:=V)) 6=0 := by rw [cleanSeedStore_registers];rfl
  have hy : registers (cleanSeedStore (V:=V)) 7=0 := by rw [cleanSeedStore_registers];rfl
  obtain ⟨k,cs,hk,ht⟩ := ax_block (cleanSeedStore (V:=V)) cleanSeedStore_valid hx hy
  obtain ⟨ds,hd⟩ := trace_compose ht (mp_return_trace (axEnd (cleanSeedStore (V:=V))))
  refine ⟨k+1,ds,axEnd (cleanSeedStore (V:=V)),by simp,?_,axEnd_valid _,?_,?_,?_⟩
  · exact hd
  · have h := axEnd_frame (cleanSeedStore (V:=V))
    exact ⟨h.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2⟩
  · rw [(axEnd_frame _).1,cleanSeedStore_registers]
    rfl
  · rw [(axEnd_frame _).2.1,cleanSeedStore_registers]
    simp [SourceCantorInternal.decodeRight]
#print axioms cleanSeedStore_valid
#print axioms cleanSeedStore_registers
#print axioms seed_to_root
end PA215.PA.InternalTrace.CodedSource
