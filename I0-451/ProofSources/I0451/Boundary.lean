module
public import I0451.LiteralExecution

/-! Reach the next command boundary after the permanent-space startup.
The frame's packed pointer is zero and both scratch registers are zero. -/
@[expose] public section
namespace I0451.Runtime

private def phase26 : RegisterFrame :=
  ⟨[true, true, true, true, false, true, true, true, true, false, false, true], 122,
    fixedBlocks ++ [0, 1, 0, 0, 1, 0, 0, 1, 3]⟩

private def phase52 : RegisterFrame :=
  ⟨[true, true, true, true, true, false], 129, fixedBlocks ++ [0, 0, 5, 0, 1, 0, 0, 3, 3]⟩

private def phase78 : RegisterFrame :=
  ⟨[true, true, true, true, true, true, false, false, true, true, false, true, true], 140,
    fixedBlocks ++ [0, 0, 2, 5, 1, 0, 0, 0, 3]⟩

def commandBoundary : RegisterFrame :=
  ⟨List.replicate 7 false, 153, fixedBlocks ++ [0, 0, 0, 0, 1, 0, 0, 0, 3]⟩

section
set_option maxRecDepth 20000
set_option maxHeartbeats 0

private theorem boundary1 : runMacros 26 readyFrame = some phase26 := by decide +kernel
private theorem boundary2 : runMacros 26 phase26 = some phase52 := by decide +kernel
private theorem boundary3 : runMacros 26 phase52 = some phase78 := by decide +kernel
private theorem boundary4 : runMacros 26 phase78 = some commandBoundary := by decide +kernel
end

theorem reaches_boundary : runMacros 104 readyFrame = some commandBoundary :=
  runMacros_join (m := 52) (n := 52)
    (runMacros_join (m := 26) (n := 26) boundary1 boundary2 rfl)
    (runMacros_join (m := 26) (n := 26) boundary3 boundary4 rfl) rfl

theorem runMacros_permanent {f g : RegisterFrame} {n : Nat}
    (good : Permanent f) (run : runMacros n f = some g) : Permanent g := by
  induction n generalizing f with
  | zero =>
    simp only [runMacros, Option.some.injEq] at run
    exact run ▸ good
  | succ n ih =>
    have preserves := macroStep_preserves good
    cases h : macroStep f with
    | invalid => simp [runMacros, h] at run
    | halt => simp [runMacros, h] at run
    | next mid =>
      exact ih (by simpa only [h, Preserves] using preserves)
        (by simpa only [runMacros, h] using run)

theorem commandBoundary_permanent : Permanent commandBoundary :=
  runMacros_permanent ready_permanent reaches_boundary

theorem blank_halts_iff_boundary :
    Halts literal (blank 0) ↔ MacroHalts commandBoundary := by
  obtain ⟨n, reaches⟩ := blank_reaches_ready_frame.trans (runMacros_sound reaches_boundary)
  exact (halts_iff_of_run reaches).trans (halts_iff_macro commandBoundary_permanent)

end I0451.Runtime
