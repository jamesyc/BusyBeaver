module
public import I0451.CounterLoops
public import I0451.Logic.Formula

/-! Counter-level Cantor pairing. One pass moves the second operand to
the first and accumulates it. A successful decrement then increases the
result and moves the remaining first operand back before the next pass. -/

@[expose] public section
namespace I0451.Runtime

open M6.Source.Cantor

def fillPair (a b out : Fin 9) (s : Registers) : Registers :=
  putRegister (addAt (fun j => j == a || j == out) (s b) s) b 0

def rotatePair (a b out : Fin 9) (s : Registers) : Registers :=
  let next := putRegister s out (s out + 1)
  putRegister (addAt (· == b) (next a) next) a 0

def pairedRegisters (a b out : Fin 9) (s : Registers) : Registers :=
  putRegister (putRegister (putRegister s a 0) b 0) out
    (s out + pair (s a) (s b))

/-- The concrete pairing-loop shape. The two supplied move contracts
are proved on the literal counter graph for each call. -/
theorem executes_pair {root test cycle : Cursor} {fill move : Edge} {a b out : Fin 9}
    (ab : a ≠ b) (ao : a ≠ out) (bo : b ≠ out)
    (left : outgoing root false = some fill)
    (right : outgoing root true = some (.branch test))
    (decEdge : outgoing test false = some (.instruction (.dec a)))
    (cycleEdge : outgoing test true = some (.branch cycle))
    (moveEdge : outgoing cycle false = some move)
    (repeatEdge : outgoing cycle true = some (.instruction (.restart 2)))
    (moveIn : ∀ s, Executes fill s .normal (fillPair a b out s))
    (moveBack : ∀ s, Executes move s .normal (rotatePair a b out s))
    (s : Registers) :
    Executes (.branch root) s .normal (pairedRegisters a b out s) := by
  generalize count : s a + s b = n
  induction n using Nat.strongRecOn generalizing s with
  | ind n ih =>
    let filled := fillPair a b out s
    have atA : filled a = n := by simpa [filled, fillPair, putRegister, addAt, ab] using count
    have atB : filled b = 0 := putRegister_at _ _ _
    have atOut : filled out = s out + s b := by simp [filled, fillPair, putRegister, addAt, Ne.symm bo]
    cases n with
    | zero =>
      have stopped : Executes (.branch test) filled .normal filled :=
        .leftExit decEdge (.decZero a filled atA) rfl
      have same : filled = pairedRegisters a b out s := by
        have zeroA : s a = 0 := by omega
        have zeroB : s b = 0 := by omega
        funext j
        by_cases oa : j = out
        · subst j
          simp [atOut, pairedRegisters, zeroA, zeroB, pair, triangle]
        · by_cases aa : j = a
          · subst j
            simp [atA, pairedRegisters, putRegister, ab, ao]
          · by_cases bb : j = b
            · subst j
              simp [atB, pairedRegisters, putRegister, bo]
            · simp [filled, fillPair, pairedRegisters, addAt, putRegister, aa, bb, oa, zeroB]
      rw [← same]
      exact executes_sequence left right (moveIn s) stopped
    | succ n =>
      let reduced := putRegister filled a n
      let rotated := rotatePair a b out reduced
      have newA : rotated a = 0 := putRegister_at _ _ _
      have newB : rotated b = n := by
        simp [rotated, rotatePair, putRegister, addAt, Ne.symm ab, ao, bo, reduced, atB]
      have newOut : rotated out = s out + s b + 1 := by
        simp [rotated, rotatePair, putRegister, addAt, Ne.symm ao, Ne.symm bo, reduced, atOut]
      have sum : rotated a + rotated b = n := by rw [newA, newB, Nat.zero_add]
      have again := ih n (by omega) rotated sum
      have same : pairedRegisters a b out rotated = pairedRegisters a b out s := by
        funext j
        by_cases atO : j = out
        · subst j
          simp only [pairedRegisters, putRegister_at, newOut, newA, newB, pair, Nat.zero_add, count,
            triangle]
          omega
        · by_cases atA' : j = a
          · subst j
            simp [pairedRegisters, putRegister, ab, ao]
          · by_cases atB' : j = b
            · subst j
              simp [pairedRegisters, putRegister, bo]
            · simp [pairedRegisters, putRegister, atO, atA', atB', rotated, rotatePair,
                reduced, addAt, filled, fillPair]
      rw [same] at again
      have spin : Executes (.branch cycle) reduced (.restart 1) rotated :=
        .rightExit moveEdge repeatEdge (moveBack reduced) (.restart 2 rotated) rfl
      have back : Executes (.branch test) filled (.restart 0) rotated :=
        .rightExit decEdge cycleEdge (.decPositive a filled n atA) spin rfl
      exact .repeat left right (moveIn s) back again

end I0451.Runtime
