module
public import I0451.ProofStackPush

/-! Counter comparison and its destructive store effect. The compare
loop leaves the absolute difference in its second operand. The final
test clears that difference and skips its handler when nonzero. -/
@[expose] public section
namespace I0451.Runtime

def discrepancy (x y : Nat) : Nat := (x - y) + (y - x)

def compareResult (x y : Fin 9) (s : Registers) : Registers :=
  putRegister (putRegister s x 0) y (discrepancy (s x) (s y))

def clearPair {α : Type} [Zero α] (x y : Fin 9) (s : Fin 9 → α) : Fin 9 → α :=
  putRegister (putRegister s x 0) y 0

/-- Empty decrement loop. -/
theorem clear_counter {c : Cursor} {r : Fin 9}
    (dec : outgoing c false = some (.instruction (.dec r)))
    (back : outgoing c true = some (.instruction (.restart 0))) (s : Registers) :
    Executes (.branch c) s .normal (putRegister s r 0) := by
  generalize count : s r = n
  induction n generalizing s with
  | zero =>
    have same : putRegister s r 0 = s := by rw [← count, putRegister_read]
    rw [same]
    exact .leftExit dec (.decZero r s count) rfl
  | succ n ih =>
    let reduced := putRegister s r n
    have again := ih reduced (putRegister_at _ _ _)
    rw [putRegister_overwrite] at again
    exact .repeat dec back (.decPositive r s n count) (.restart 0 reduced) again

/-- The paired-decrement loop. If the second operand reaches zero first,
the mismatch branch moves the residual first operand back, with one
unit of compensation for the decrement just taken. -/
theorem compare_loop {entry afterFirst testSecond : Cursor} {mismatch : Edge} {x y : Fin 9}
    (distinct : x ≠ y)
    (readX : outgoing entry false = some (.instruction (.dec x)))
    (testY : outgoing entry true = some (.branch afterFirst))
    (enterY : outgoing afterFirst false = some (.branch testSecond))
    (enterMismatch : outgoing afterFirst true = some mismatch)
    (readY : outgoing testSecond false = some (.instruction (.dec y)))
    (reenter : outgoing testSecond true = some (.instruction (.restart 1)))
    (remainder : ∀ s, s y = 0 →
      Executes mismatch s .normal (putRegister (putRegister s x 0) y (s x + 1)))
    (s : Registers) :
    Executes (.branch entry) s .normal (compareResult x y s) := by
  generalize count : s x = n
  induction n generalizing s with
  | zero =>
    have same : compareResult x y s = s := by
      funext j
      by_cases jy : j = y
      · simp [compareResult, putRegister, jy, discrepancy, count]
      · by_cases jx : j = x
        · simp [compareResult, putRegister, jx, distinct, count]
        · simp [compareResult, putRegister, jy, jx]
    rw [same]
    exact .leftExit readX (.decZero x s count) rfl
  | succ n ih =>
    let reduced := putRegister s x n
    have originalY : reduced y = s y := putRegister_other _ (Ne.symm distinct) _
    cases amount : s y with
    | zero =>
      have yZero := originalY.trans amount
      let final := putRegister (putRegister reduced x 0) y (reduced x + 1)
      have bTest : Executes (.branch testSecond) reduced .normal reduced :=
        .leftExit readY (.decZero y _ yZero) rfl
      have rest : Executes (.branch afterFirst) reduced .normal final :=
        executes_sequence enterY enterMismatch bTest (remainder _ yZero)
      have same : final = compareResult x y s := by
        simp [final, reduced, putRegister_overwrite, compareResult, discrepancy, count, amount]
      rw [← same]
      exact .rightExit readX testY (.decPositive x s n count) rest rfl
    | succ m =>
      let both := putRegister reduced y m
      have yPos : reduced y = m + 1 := originalY.trans amount
      have bTest : Executes (.branch testSecond) reduced (.restart 0) both :=
        .rightExit readY reenter (.decPositive y reduced m yPos) (.restart 1 both) rfl
      have rest : Executes (.branch afterFirst) reduced (.restart 0) both :=
        .leftExit enterY bTest rfl
      have xPos : both x = n := by simp [both, reduced, putRegister, distinct]
      have difference :
          discrepancy (both x) (both y) = discrepancy (s x) (s y) := by
        rw [xPos, show both y = m from putRegister_at _ _ _, count, amount]
        unfold discrepancy
        omega
      have same : compareResult x y both = compareResult x y s := by
        funext j
        by_cases jy : j = y
        · simp [compareResult, putRegister, jy, difference]
        · by_cases jx : j = x
          · simp [compareResult, putRegister, jx, distinct]
          · simp [compareResult, putRegister, both, reduced, jy, jx]
      have again := ih both xPos
      rw [same] at again
      exact .repeat readX testY (.decPositive x s n count) rest again

/-- Test the residual comparison value, clear it, and return a local
break on inequality. -/
theorem clear_or_skip {entry cleanup : Cursor} {clear : Edge} {r : Fin 9}
    (dec : outgoing entry false = some (.instruction (.dec r)))
    (body : outgoing entry true = some (.branch cleanup))
    (clearEdge : outgoing cleanup false = some clear)
    (skip : outgoing cleanup true = some (.instruction (.break 0)))
    (clearRun : ∀ s, Executes clear s .normal (putRegister s r 0))
    (s : Registers) :
    Executes (.branch entry) s
      (if s r = 0 then .normal else .break 0) (putRegister s r 0) := by
  cases count : s r with
  | zero =>
    have same : putRegister s r 0 = s := by rw [← count, putRegister_read]
    rw [same]
    exact .leftExit dec (.decZero r s count) rfl
  | succ n =>
    let reduced := putRegister s r n
    have clean := clearRun reduced
    rw [putRegister_overwrite] at clean
    have clearAndSkip : Executes (.branch cleanup) reduced (.break 0) (putRegister s r 0) :=
      .rightExit clearEdge skip clean (.break 0 _) rfl
    exact .rightExit dec body (.decPositive r s n count) clearAndSkip rfl

end I0451.Runtime
