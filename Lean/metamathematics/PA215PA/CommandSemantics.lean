import PA215.Source.Enumeration
import PA215PA.AXCodeBridge

/-! Exact closed arithmetic command semantics from the retained source
THEOREM.md section 3. This is NOT Source.step: transfer from literal graph
execution is a separate obligation. Uses the real enumeration command datatype
and pure AXCode; the arithmetic-to-native codec equality is already explicit. -/
namespace PA215.PA.CommandSemantics
open PA215.Source.Cantor PA215.Source.Enumeration
open NativeCalculus

structure State where
  t : Nat
  w : Nat
  d : Nat
  h : Nat
  deriving DecidableEq, Repr

/-- `none` means the command's actual halting guard fired, not failure. -/
def step : Command → State → Option State
  | .shift, s => if s.t + s.h = 1 then none else
      some ⟨s.h,(decode s.w).2,s.d,(decode s.w).1⟩
  | .mp x, s =>
      let y := s.d + x
      if wim s.t y = s.h then some ⟨y,pair 0 s.w,y,0⟩ else some ⟨0,s.w,y,0⟩
  | .ax c x y, s =>
      let a := s.d+x
      let b := s.h+y
      some ⟨PA215.Source.AXCode.gate a b c,
        PA215.Source.AXCode.outputStack a b c s.d s.h s.t s.w,0,0⟩

def run : List Command → State → Option State
  | [], s => some s
  | c :: cs, s => (step c s).bind (run cs)

theorem run_append (xs ys : List Command) (s : State) :
    run (xs ++ ys) s = (run xs s).bind (run ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append,run]
    cases h : step x s <;> simp [ih]

theorem halt_prefix (xs ys : List Command) (s : State) (h : run xs s = none) :
    run (xs ++ ys) s = none := by rw [run_append,h]; rfl

/-- The exceptional zero alias makes MP(0) a push, not a neutral jump. -/
theorem mp_zero_alias (w : Nat) :
    step (.mp 0) ⟨0,w,0,0⟩ = some ⟨0,pair 0 w,0,0⟩ := by
  simp [step,wim,PA215.Source.Cantor.implication,pair,triangle]

def D : List Command := [.ax 0 0 0]
def H : List Command := D ++ List.replicate 11 .shift
def PUSH : List Command := D ++ List.replicate 9 .shift ++ [.mp 0]
def DISCARD : List Command := [.mp 1,.ax 1 0 0] ++ List.replicate 10 .shift ++ [.mp 0]
def J (u : Nat) : List Command := if u = 0 then [] else [.mp u]

theorem jump_zero : J 0 = [] := rfl

def TopSound (s : State) : Prop := Proved s.t ∧ Proved s.h

theorem shift_halt_refutation (s : State) (hs : TopSound s) (hhalt : step .shift s = none) :
    Proved 1 := by
  have hsum : s.t + s.h = 1 := by
    by_cases hn : s.t + s.h = 1
    · exact hn
    · simp [step,hn] at hhalt
  have h : s.t = 1 ∨ s.h = 1 := by omega
  rcases h with h | h
  · simpa [h] using hs.1
  · simpa [h] using hs.2

theorem mp_preserves_top (x : Nat) (s out : State) (hs : TopSound s)
    (hr : step (.mp x) s = some out) : TopSound out := by
  simp only [step] at hr
  split at hr
  · rename_i he
    cases hr
    constructor
    · apply mp_proved hs.1
      simpa only [he] using hs.2
    · exact ⟨.truth⟩
  · cases hr
    exact ⟨⟨.truth⟩,⟨.truth⟩⟩

theorem ax_preserves_top (c x y : Nat) (s : State) :
    ∃ out, step (.ax c x y) s = some out ∧ TopSound out := by
  refine ⟨_,rfl,?_,?_⟩
  · exact core_gate_proved _ _ _
  · exact ⟨.truth⟩

theorem ax_heads_sound (c x y : Nat) (s : State) (hh : Proved s.h) :
    ∀ n ∈ PA215.Source.AXCode.pa135Heads (s.d+x) (s.h+y) c s.d s.h, Proved n :=
  core_heads_proved _ _ _ _ _ (by omega) hh

#print axioms run_append
#print axioms shift_halt_refutation
#print axioms mp_preserves_top
#print axioms ax_heads_sound
end PA215.PA.CommandSemantics
