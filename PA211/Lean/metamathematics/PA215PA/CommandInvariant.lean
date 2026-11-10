import PA215.Source.WrapperStack
import PA215PA.CommandSemantics

/-! Native proof witnesses above the SAME opaque stack tail are preserved
by the exact arithmetic commands. NoRefutation is explicit here; its actual
PA-consistency discharge belongs to the soundness composition module.
This does not substitute arithmetic commands for literal source execution. -/
namespace PA215.PA.CommandSemantics
open PA215.Source PA215.Source.Cantor PA215.Source.Enumeration NativeCalculus

def Invariant (tail depth : Nat) (s : State) : Prop :=
  TopSound s ∧ WrapperStack.Safe Proved tail depth s.w

theorem step_invariant (hn : ¬ Proved 1) (c : Command) (s : State) (tail depth : Nat)
    (hs : Invariant tail depth s) (hcredit : 0 ≤ (depth : Int) + commandWeight c) :
    ∃ out depth', step c s = some out ∧ Invariant tail depth' out ∧
      (depth : Int) + commandWeight c ≤ (depth' : Int) := by
  rcases hs with ⟨ht,hw⟩
  cases c with
  | shift =>
    have hd : depth = (depth-1)+1 := by simp only [commandWeight] at hcredit; omega
    have hp := WrapperStack.pop (P := Proved) (tail := tail) (depth := depth-1) (stack := s.w)
      (by simpa only [← hd] using hw)
    have hg : s.t+s.h ≠ 1 := by
      intro he
      apply hn
      exact shift_halt_refutation s ht (by simp [step,he])
    refine ⟨⟨s.h,(decode s.w).2,s.d,(decode s.w).1⟩,depth-1,?_,?_,?_⟩
    · simp [step,hg]
    · exact ⟨⟨ht.2,hp.1⟩,hp.2⟩
    · simp only [commandWeight]; omega
  | mp x =>
    by_cases he : wim s.t (s.d+x) = s.h
    · let out : State := ⟨s.d+x,pair 0 s.w,s.d+x,0⟩
      have hr : step (.mp x) s = some out := by simp [step,he,out]
      refine ⟨out,depth+1,hr,⟨mp_preserves_top x s out ht hr,?_⟩,?_⟩
      · exact WrapperStack.push hw (show Proved 0 from ⟨.truth⟩)
      · simp only [commandWeight]; omega
    · let out : State := ⟨0,s.w,s.d+x,0⟩
      have hr : step (.mp x) s = some out := by simp [step,he,out]
      exact ⟨out,depth,hr,⟨mp_preserves_top x s out ht hr,hw⟩,by simp [commandWeight]⟩
  | ax c x y =>
    let heads := AXCode.pa135Heads (s.d+x) (s.h+y) c s.d s.h ++ [s.t]
    have hlen : heads.length = 10 := by simp [heads,AXCode.pa135Heads]
    have hh : ∀ n ∈ heads, Proved n := by
      intro n hn'
      rcases List.mem_append.mp hn' with h | h
      · exact ax_heads_sound c x y s ht.2 n h
      · simpa only [List.mem_singleton.mp h] using ht.1
    let out : State := ⟨AXCode.gate (s.d+x) (s.h+y) c,
      AXCode.outputStack (s.d+x) (s.h+y) c s.d s.h s.t s.w,0,0⟩
    refine ⟨out,depth+10,rfl,⟨⟨core_gate_proved _ _ _,⟨.truth⟩⟩,?_⟩,?_⟩
    · have hp := WrapperStack.prepend hh hw
      rw [hlen] at hp
      simpa only [Nat.add_comm,WrapperStack.encode,AXCode.outputStack,AXCode.stackCode,heads,out] using hp
    · simp [commandWeight]

theorem run_invariant (hn : ¬ Proved 1) (cs : List Command) (s : State) (tail depth : Nat)
    (hs : Invariant tail depth s)
    (hcredit : ∀ p r, cs = p ++ r → 0 ≤ (depth : Int) + weight p) :
    ∃ out depth', run cs s = some out ∧ Invariant tail depth' out ∧
      (depth : Int) + weight cs ≤ (depth' : Int) := by
  induction cs generalizing s depth with
  | nil => exact ⟨s,depth,rfl,hs,by simp [weight]⟩
  | cons c cs ih =>
    have hc := hcredit [c] cs rfl
    simp only [weight,Int.add_zero] at hc
    obtain ⟨mid,k,hstep,hm,hk⟩ := step_invariant hn c s tail depth hs hc
    have hrest : ∀ p r, cs = p ++ r → 0 ≤ (k : Int) + weight p := by
      intro p r he
      have hp := hcredit (c::p) r (by simp [he])
      simp only [weight] at hp
      change 0 ≤ (depth : Int) + (commandWeight c + weight p) at hp
      omega
    obtain ⟨out,k',hrun,ho,hbound⟩ := ih mid k hm hrest
    refine ⟨out,k',?_,ho,?_⟩
    · simp only [run,hstep,Option.bind_some,hrun]
    · change (depth : Int) + (commandWeight c + weight cs) ≤ (k' : Int)
      omega

#print axioms step_invariant
#print axioms run_invariant
end PA215.PA.CommandSemantics
