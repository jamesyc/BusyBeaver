import PA215.Tape
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215

/-- The local initial frame: blank left exterior, sentinel at -1, PC 1011.
    The entire tape from position 4 onward is arbitrary. -/
def continueInitialTape (suffix : Tape) : Tape := fun i =>
  if i = -1 then true else
  if i = 0 then true else
  if i = 1 then false else
  if i = 2 then true else
  if i = 3 then true else
  if i < -1 then false else suffix i

/-- Exact local target: clear the three set PC bits, preserve everything else. -/
def continueTargetTape (suffix : Tape) : Tape :=
  writeTape (writeTape (writeTape (continueInitialTape suffix) 3 false) 2 false) 0 false


private def tape0 (suffix : Tape) := continueInitialTape suffix
private def tape1 (suffix : Tape) := writeTape (tape0 suffix) (0) true
private def tape2 (suffix : Tape) := writeTape (tape1 suffix) (1) false
private def tape3 (suffix : Tape) := writeTape (tape2 suffix) (2) true
private def tape4 (suffix : Tape) := writeTape (tape3 suffix) (3) false
private def tape5 (suffix : Tape) := writeTape (tape4 suffix) (2) false
private def tape6 (suffix : Tape) := writeTape (tape5 suffix) (1) false
private def tape7 (suffix : Tape) := writeTape (tape6 suffix) (0) false
private def tape8 (suffix : Tape) := writeTape (tape7 suffix) (-1) true
private def tape9 (suffix : Tape) := writeTape (tape8 suffix) (-2) false
private def tape10 (suffix : Tape) := writeTape (tape9 suffix) (-3) false
private def tape11 (suffix : Tape) := writeTape (tape10 suffix) (-4) false
private def tape12 (suffix : Tape) := writeTape (tape11 suffix) (-5) false
private def tape13 (suffix : Tape) := writeTape (tape12 suffix) (-6) false
private def tape14 (suffix : Tape) := writeTape (tape13 suffix) (-7) false
private def tape15 (suffix : Tape) := writeTape (tape14 suffix) (-8) false
private def tape16 (suffix : Tape) := writeTape (tape15 suffix) (-9) false
private def tape17 (suffix : Tape) := writeTape (tape16 suffix) (-10) false
private def tape18 (suffix : Tape) := writeTape (tape17 suffix) (-9) false
private def tape19 (suffix : Tape) := writeTape (tape18 suffix) (-8) false
private def tape20 (suffix : Tape) := writeTape (tape19 suffix) (-7) false
private def tape21 (suffix : Tape) := writeTape (tape20 suffix) (-6) false
private def tape22 (suffix : Tape) := writeTape (tape21 suffix) (-5) false
private def tape23 (suffix : Tape) := writeTape (tape22 suffix) (-4) false
private def tape24 (suffix : Tape) := writeTape (tape23 suffix) (-3) false
private def tape25 (suffix : Tape) := writeTape (tape24 suffix) (-2) false
private def tape26 (suffix : Tape) := writeTape (tape25 suffix) (-1) true
private def cfg0 (suffix : Tape) : Configuration := ⟨target 81, 0, tape0 suffix⟩
private def cfg1 (suffix : Tape) : Configuration := ⟨target 211, 1, tape1 suffix⟩
private def cfg2 (suffix : Tape) : Configuration := ⟨target 12, 2, tape2 suffix⟩
private def cfg3 (suffix : Tape) : Configuration := ⟨target 19, 3, tape3 suffix⟩
private def cfg4 (suffix : Tape) : Configuration := ⟨target 104, 2, tape4 suffix⟩
private def cfg5 (suffix : Tape) : Configuration := ⟨target 11, 1, tape5 suffix⟩
private def cfg6 (suffix : Tape) : Configuration := ⟨target 17, 0, tape6 suffix⟩
private def cfg7 (suffix : Tape) : Configuration := ⟨target 2, -1, tape7 suffix⟩
private def cfg8 (suffix : Tape) : Configuration := ⟨target 3, -2, tape8 suffix⟩
private def cfg9 (suffix : Tape) : Configuration := ⟨target 4, -3, tape9 suffix⟩
private def cfg10 (suffix : Tape) : Configuration := ⟨target 6, -4, tape10 suffix⟩
private def cfg11 (suffix : Tape) : Configuration := ⟨target 10, -5, tape11 suffix⟩
private def cfg12 (suffix : Tape) : Configuration := ⟨target 16, -6, tape12 suffix⟩
private def cfg13 (suffix : Tape) : Configuration := ⟨target 24, -7, tape13 suffix⟩
private def cfg14 (suffix : Tape) : Configuration := ⟨target 35, -8, tape14 suffix⟩
private def cfg15 (suffix : Tape) : Configuration := ⟨target 50, -9, tape15 suffix⟩
private def cfg16 (suffix : Tape) : Configuration := ⟨target 74, -10, tape16 suffix⟩
private def cfg17 (suffix : Tape) : Configuration := ⟨target 74, -9, tape17 suffix⟩
private def cfg18 (suffix : Tape) : Configuration := ⟨target 74, -8, tape18 suffix⟩
private def cfg19 (suffix : Tape) : Configuration := ⟨target 74, -7, tape19 suffix⟩
private def cfg20 (suffix : Tape) : Configuration := ⟨target 74, -6, tape20 suffix⟩
private def cfg21 (suffix : Tape) : Configuration := ⟨target 74, -5, tape21 suffix⟩
private def cfg22 (suffix : Tape) : Configuration := ⟨target 74, -4, tape22 suffix⟩
private def cfg23 (suffix : Tape) : Configuration := ⟨target 74, -3, tape23 suffix⟩
private def cfg24 (suffix : Tape) : Configuration := ⟨target 74, -2, tape24 suffix⟩
private def cfg25 (suffix : Tape) : Configuration := ⟨target 74, -1, tape25 suffix⟩
private def cfg26 (suffix : Tape) : Configuration := ⟨dispatcher, 0, tape26 suffix⟩
private theorem step0 (suffix : Tape) : step (cfg0 suffix) = some (cfg1 suffix) := rfl
private theorem step1 (suffix : Tape) : step (cfg1 suffix) = some (cfg2 suffix) := rfl
private theorem step2 (suffix : Tape) : step (cfg2 suffix) = some (cfg3 suffix) := rfl
private theorem step3 (suffix : Tape) : step (cfg3 suffix) = some (cfg4 suffix) := rfl
private theorem step4 (suffix : Tape) : step (cfg4 suffix) = some (cfg5 suffix) := rfl
private theorem step5 (suffix : Tape) : step (cfg5 suffix) = some (cfg6 suffix) := rfl
private theorem step6 (suffix : Tape) : step (cfg6 suffix) = some (cfg7 suffix) := rfl
private theorem step7 (suffix : Tape) : step (cfg7 suffix) = some (cfg8 suffix) := rfl
private theorem step8 (suffix : Tape) : step (cfg8 suffix) = some (cfg9 suffix) := rfl
private theorem step9 (suffix : Tape) : step (cfg9 suffix) = some (cfg10 suffix) := rfl
private theorem step10 (suffix : Tape) : step (cfg10 suffix) = some (cfg11 suffix) := rfl
private theorem step11 (suffix : Tape) : step (cfg11 suffix) = some (cfg12 suffix) := rfl
private theorem step12 (suffix : Tape) : step (cfg12 suffix) = some (cfg13 suffix) := rfl
private theorem step13 (suffix : Tape) : step (cfg13 suffix) = some (cfg14 suffix) := rfl
private theorem step14 (suffix : Tape) : step (cfg14 suffix) = some (cfg15 suffix) := rfl
private theorem step15 (suffix : Tape) : step (cfg15 suffix) = some (cfg16 suffix) := rfl
private theorem step16 (suffix : Tape) : step (cfg16 suffix) = some (cfg17 suffix) := rfl
private theorem step17 (suffix : Tape) : step (cfg17 suffix) = some (cfg18 suffix) := rfl
private theorem step18 (suffix : Tape) : step (cfg18 suffix) = some (cfg19 suffix) := rfl
private theorem step19 (suffix : Tape) : step (cfg19 suffix) = some (cfg20 suffix) := rfl
private theorem step20 (suffix : Tape) : step (cfg20 suffix) = some (cfg21 suffix) := rfl
private theorem step21 (suffix : Tape) : step (cfg21 suffix) = some (cfg22 suffix) := rfl
private theorem step22 (suffix : Tape) : step (cfg22 suffix) = some (cfg23 suffix) := rfl
private theorem step23 (suffix : Tape) : step (cfg23 suffix) = some (cfg24 suffix) := rfl
private theorem step24 (suffix : Tape) : step (cfg24 suffix) = some (cfg25 suffix) := rfl
private theorem step25 (suffix : Tape) : step (cfg25 suffix) = some (cfg26 suffix) := rfl

private theorem run26 (suffix : Tape) : run 26 (cfg0 suffix) = some (cfg26 suffix) := by
  simp only [run, step0, step1, step2, step3, step4, step5, step6, step7, step8, step9, step10, step11, step12, step13, step14, step15, step16, step17, step18, step19, step20, step21, step22, step23, step24, step25, Option.bind_some]

private theorem tape26_eq (suffix : Tape) : tape26 suffix = continueTargetTape suffix := by
  funext i
  by_cases h0 : i = (-10)
  · subst i; rfl
  by_cases h1 : i = (-9)
  · subst i; rfl
  by_cases h2 : i = (-8)
  · subst i; rfl
  by_cases h3 : i = (-7)
  · subst i; rfl
  by_cases h4 : i = (-6)
  · subst i; rfl
  by_cases h5 : i = (-5)
  · subst i; rfl
  by_cases h6 : i = (-4)
  · subst i; rfl
  by_cases h7 : i = (-3)
  · subst i; rfl
  by_cases h8 : i = (-2)
  · subst i; rfl
  by_cases h9 : i = (-1)
  · subst i; rfl
  by_cases h10 : i = (0)
  · subst i; rfl
  by_cases h11 : i = (1)
  · subst i; rfl
  by_cases h12 : i = (2)
  · subst i; rfl
  by_cases h13 : i = (3)
  · subst i; rfl
  simp only [tape26, tape25, tape24, tape23, tape22, tape21, tape20, tape19, tape18, tape17, tape16, tape15, tape14, tape13, tape12, tape11, tape10, tape9, tape8, tape7, tape6, tape5, tape4, tape3, tape2, tape1, tape0, continueTargetTape, writeTape, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, ite_false]

/-- Original obligation 5084's universal 26-step return in dense labels.
    The complete arbitrary suffix is preserved, without a symbolic oracle. -/
theorem continue_return_26 (suffix : Tape) :
    run 26 ⟨dispatcher, 0, continueInitialTape suffix⟩ =
    some ⟨dispatcher, 0, continueTargetTape suffix⟩ := by
  have h := run26 suffix
  change run 26 ⟨dispatcher, 0, continueInitialTape suffix⟩ =
    some ⟨dispatcher, 0, tape26 suffix⟩ at h
  rw [tape26_eq] at h
  exact h

/-- Every cell of the complete right suffix is unchanged. -/
theorem continue_preserves_suffix (suffix : Tape) (i : Int) (h : 4 ≤ i) :
    continueTargetTape suffix i = suffix i := by
  have hneg : ¬i < -1 := by omega
  have hm1 : i ≠ -1 := by omega
  have h0 : i ≠ 0 := by omega
  have h1 : i ≠ 1 := by omega
  have h2 : i ≠ 2 := by omega
  have h3 : i ≠ 3 := by omega
  simp [continueTargetTape, writeTape, continueInitialTape, hneg, hm1, h0, h1, h2, h3]

theorem continue_sentinel_preserved (suffix : Tape) :
    continueTargetTape suffix (-1) = true := rfl

theorem continue_clears_pc (suffix : Tape) (i : Int) (h0 : 0 ≤ i) (h4 : i < 4) :
    continueTargetTape suffix i = false := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with h | h | h | h <;> subst i <;> rfl

end PA215
