module
public import I0451.InterpreterSound

/-! The permanent-space startup. The literal loader reaches a small-slot
frame. The proved interpreter then executes 126 instructions to reach
slot 107, without replaying the long unary scans as concrete tape steps. -/

@[expose] public section
namespace I0451.Runtime

def runMacros : Nat → RegisterFrame → Option RegisterFrame
  | 0, f => some f
  | n + 1, f => match macroStep f with
    | .next g => runMacros n g
    | _ => none

theorem runMacros_sound {n : Nat} {f g : RegisterFrame}
    (trace : runMacros n f = some g) : Reaches literal f.tape g.tape := by
  induction n generalizing f with
  | zero =>
    simp only [runMacros, Option.some.injEq] at trace
    subst g
    exact ⟨0, rfl⟩
  | succ n ih =>
    cases next : macroStep f with
    | invalid => simp [runMacros, next] at trace
    | halt => simp [runMacros, next] at trace
    | next mid =>
      have contract := macroStep_sound f
      rw [next] at contract
      obtain ⟨k, _, advance⟩ := contract
      exact (show Reaches literal _ _ from ⟨k, advance⟩).trans
        (ih (by simpa only [runMacros, next] using trace))

theorem runMacros_add (m n : Nat) (f : RegisterFrame) :
    runMacros (m + n) f = (runMacros m f).bind (runMacros n) := by
  induction m generalizing f with
  | zero => simp [runMacros]
  | succ m ih =>
    rw [Nat.succ_add, runMacros, runMacros]
    cases macroStep f
    · rfl
    · rfl
    · next g => exact ih g

theorem runMacros_join {m n total : Nat} {a b c : RegisterFrame}
    (first : runMacros m a = some b) (second : runMacros n b = some c)
    (length : m + n = total) : runMacros total a = some c := by
  subst total
  rw [runMacros_add, first]
  exact second

private def at21 : RegisterFrame :=
  ⟨[true, true, true, true, false, true, true, false, true], 39,
    fixedBlocks ++ [0, 0, 0, 0, 0, 0, 0, 0, 1]⟩

private def at42 : RegisterFrame :=
  ⟨[false, true, true, false], 56, fixedBlocks ++ [1, 0, 0, 0, 0, 0, 0, 0, 1]⟩

private def at63 : RegisterFrame :=
  ⟨[true, true, true, false, true, false, true], 70, fixedBlocks ++ [0, 0, 0, 0, 0, 0, 0, 0, 2]⟩

private def at84 : RegisterFrame :=
  ⟨[false, true, true, false], 83, fixedBlocks ++ [2, 0, 1, 0, 0, 0, 0, 0, 1]⟩

private def at105 : RegisterFrame :=
  ⟨[true, false, false, true, true, true], 93, fixedBlocks ++ [1, 0, 0, 0, 0, 0, 0, 0, 3]⟩

def readyFrame : RegisterFrame :=
  ⟨[true, true, true, true, false, false, false, true, false, true, true], 107,
    fixedBlocks ++ [0, 0, 0, 0, 1, 0, 0, 0, 3]⟩

section
set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem startup1 : runMacros 21 initialFrame = some at21 := by decide +kernel
private theorem startup2 : runMacros 21 at21 = some at42 := by decide +kernel
private theorem startup3 : runMacros 21 at42 = some at63 := by decide +kernel
private theorem startup4 : runMacros 21 at63 = some at84 := by decide +kernel
private theorem startup5 : runMacros 21 at84 = some at105 := by decide +kernel
private theorem startup6 : runMacros 21 at105 = some readyFrame := by decide +kernel
end

theorem macro_bootstrap : runMacros 126 initialFrame = some readyFrame := by
  have first : runMacros 42 initialFrame = some at42 :=
    runMacros_join (m := 21) (n := 21) startup1 startup2 rfl
  have middle : runMacros 42 at42 = some at84 :=
    runMacros_join (m := 21) (n := 21) startup3 startup4 rfl
  have last : runMacros 42 at84 = some readyFrame :=
    runMacros_join (m := 21) (n := 21) startup5 startup6 rfl
  have front : runMacros 84 initialFrame = some at84 :=
    runMacros_join (m := 42) (n := 42) first middle rfl
  exact runMacros_join (m := 84) (n := 42) front last rfl

/-- The literal machine reaches the root with the permanent-space
register frame before it can halt. -/
theorem blank_reaches_ready_frame : Reaches literal (blank 0) readyFrame.tape :=
  blank_reaches_initial_frame.trans (runMacros_sound macro_bootstrap)

end I0451.Runtime
