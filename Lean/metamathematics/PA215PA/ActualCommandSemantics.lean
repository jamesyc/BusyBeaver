module

public import PA215PA.ActualAXBridge
public import PA215PA.CommandPASafety
public import PA215.Source.EnumerationSchedule

@[expose] public section

/-! Arithmetic interpreter for the literal AX profile. The S and MP commands share their semantics with CommandSemantics. ActualAXBridge supplies the finite witnesses for the AX heads and gate used in forward PA soundness. -/
namespace PA215.PA.ActualCommandSemantics
open PA215.Source PA215.Source.Cantor PA215.Source.Enumeration NativeCalculus
open CommandSemantics (Invariant TopSound)
abbrev State := CommandSemantics.State

def step : Command → State → Option State
  | .ax c x y, s => some ⟨ActualAXCode.gate (s.d+x) (s.h+y) c,
      (ActualAXCode.pa135Heads (s.d+x) (s.h+y) c s.d s.h ++ [s.t]).foldr pair s.w,0,0⟩
  | c, s => CommandSemantics.step c s

def run : List Command → State → Option State
  | [], s => some s
  | c::cs, s => (step c s).bind (run cs)

theorem step_invariant (hn : ¬ Proved 1) (c : Command) (s : State) (tail depth : Nat)
    (hs : Invariant tail depth s) (hcredit : 0 ≤ (depth : Int) + commandWeight c) :
    ∃ out depth', step c s = some out ∧ Invariant tail depth' out ∧
      (depth : Int) + commandWeight c ≤ (depth' : Int) := by
  cases c with
  | shift => exact CommandSemantics.step_invariant hn .shift s tail depth hs hcredit
  | mp x => exact CommandSemantics.step_invariant hn (.mp x) s tail depth hs hcredit
  | ax c x y =>
    rcases hs with ⟨ht,hw⟩
    let heads := ActualAXCode.pa135Heads (s.d+x) (s.h+y) c s.d s.h ++ [s.t]
    have hlen : heads.length = 10 := by simp [heads,ActualAXCode.pa135Heads]
    have hh : ∀ n ∈ heads, Proved n := by
      intro n hn'
      rcases List.mem_append.mp hn' with h | h
      · exact actual_heads_proved _ _ _ _ _ (by omega) ht.2 n h
      · simpa only [List.mem_singleton.mp h] using ht.1
    let out : State := ⟨ActualAXCode.gate (s.d+x) (s.h+y) c,heads.foldr pair s.w,0,0⟩
    refine ⟨out,depth+10,rfl,⟨⟨actual_gate_proved _ _ _,⟨.truth⟩⟩,?_⟩,?_⟩
    · have hp := WrapperStack.prepend hh hw
      rw [hlen] at hp
      simpa only [Nat.add_comm,WrapperStack.encode,out] using hp
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
      change 0 ≤ (depth : Int) + (commandWeight c + weight p) at hp
      omega
    obtain ⟨out,k',hrun,ho,hbound⟩ := ih mid k hm hrest
    refine ⟨out,k',?_,ho,?_⟩
    · simp only [run,hstep,Option.bind_some,hrun]
    · change (depth : Int) + (commandWeight c + weight cs) ≤ (k' : Int)
      omega

def initialState : State :=
  ⟨ActualAXCode.gate 0 0 0,(ActualAXCode.pa135Heads 0 0 0 0 0 ++ [1]).foldr pair 1,0,0⟩

theorem initial_invariant : Invariant 4 9 initialState := by
  constructor
  · exact ⟨actual_gate_proved 0 0 0,⟨.truth⟩⟩
  · have hheads := actual_heads_proved 0 0 0 0 0 (by omega) (show Proved 0 from ⟨.truth⟩)
    exact WrapperStack.initial_nine (P := Proved)
      (heads := ActualAXCode.pa135Heads 0 0 0 0 0) (by rfl) hheads

theorem running_schedule_safe (hcons : PA215.PA.Consistent) (n : Nat)
    (p rest : List Command) (hp : word n = p ++ rest) :
    ∃ out depth, run (schedule n ++ p) initialState = some out ∧
      Invariant 4 depth out ∧ 6 ≤ depth := by
  have hcredit (q r : List Command) (he : schedule n ++ p = q ++ r) : (-3 : Int) ≤ weight q :=
    running_schedule_credit n p rest q hp ⟨r,he.symm⟩
  obtain ⟨out,depth,hr,hi,hbound⟩ := run_invariant (CommandSemantics.no_native_refutation hcons)
    (schedule n ++ p) initialState 4 9 initial_invariant (fun q r he => by
      have hc := hcredit q r he
      omega)
  have hc := hcredit (schedule n ++ p) [] (by simp)
  exact ⟨out,depth,hr,hi,by omega⟩

theorem running_schedule_nonhalting (hcons : PA215.PA.Consistent) (n : Nat)
    (p rest : List Command) (hp : word n = p ++ rest) :
    run (schedule n ++ p) initialState ≠ none := by
  obtain ⟨out,depth,hr,_,_⟩ := running_schedule_safe hcons n p rest hp
  simp [hr]

#print axioms actual_gate_proved
#print axioms initial_invariant
#print axioms running_schedule_safe
#print axioms running_schedule_nonhalting
end PA215.PA.ActualCommandSemantics
