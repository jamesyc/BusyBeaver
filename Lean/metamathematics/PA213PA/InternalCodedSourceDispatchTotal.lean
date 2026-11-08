import PA215PA.Theory
import PA213PA.InternalCodedSourceDispatchAX
import PA215PA.SourceCommandDecodeInternal
namespace PA213.PA.InternalTrace.CodedSource
open PA215 PA215.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal SourceCommandEncodingInternal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

theorem dispatch_command (xs raw : V) (hv : ValidStore xs)
    (ha : registers xs 3=decodeLeft raw) (hl : registers xs 8=decodeRight raw)
    (hx : registers xs 6=0) (hy : registers xs 7=0) :
    ∃k cs d,0<k ∧ Trace k cs (stateCode 24 xs) d ∧
      CommandRelation d (registers xs 0) (residual raw)
        (ActualCommandStepGraph.stepValue (commandAtom raw) (commandState xs)) := by
  rcases zero_or_succ (decodeLeft raw) with hzero | ⟨a,hsucc⟩
  · have hc : CommandClean xs := ⟨ha.trans hzero,hx,hy⟩
    obtain ⟨k,cs,hk,ht⟩ := dispatch_shift xs hv hc
    have hr := shiftOutcome_relation xs hv hc
    rw [hl] at hr
    refine ⟨k,cs,shiftOutcome xs,hk,ht,?_⟩
    simpa [residual,commandAtom,hzero] using hr
  · rcases zero_or_succ a with azero | ⟨b,asucc⟩
    · have hone : decodeLeft raw=1 := by simpa only [azero,zero_add] using hsucc
      obtain ⟨k,cs,hk,ht⟩ := dispatch_mp xs hv (ha.trans hone) hx hy
      have hr := dispatchMPEnd_relation xs hv hx hy
      rw [hl] at hr
      refine ⟨k,cs,stateCode 1 (dispatchMPEnd xs),hk,ht,?_⟩
      simpa [residual,commandAtom,hone,ActualCommandStepGraph.mpCode] using hr
    · have hmany : decodeLeft raw=(b+1)+1 := by simpa only [asucc] using hsucc
      obtain ⟨k,cs,hk,ht⟩ := dispatch_ax xs b hv (ha.trans hmany) hx hy
      have hr := dispatchAXEnd_relation xs b hv
      rw [hl] at hr
      refine ⟨k,cs,stateCode 1 (dispatchAXEnd xs b),hk,ht,?_⟩
      have hn : (b+1)+1≠1 := by simp
      have hn2 : b+2≠1 := by simpa only [add_assoc,one_add_one_eq_two] using hn
      simpa [residual,commandAtom,hmany,ActualCommandStepGraph.axCode,add_assoc,one_add_one_eq_two,hn2] using hr
#print axioms dispatch_command
end PA213.PA.InternalTrace.CodedSource

