module
public import I3_380.Search.Compiler.Commands
public import I3_380.Search.Cantor
@[expose] public section

namespace PalomarI3380.Compiler.Source


theorem run_increments (r : Register) (n : Nat) (s : Store) :
    LineRuns (List.replicate n (inc r)) s (s.set r (s r + n)) := by
  induction n generalizing s with
  | zero =>
    simp only [List.replicate_zero, Nat.add_zero, Store.set_same]
    exact .nil
  | succ n ih =>
    have rest := ih (s.set r (s r + 1))
    rw [Store.get_set, Store.set_set, Nat.add_right_comm] at rest
    exact .cons (run_inc r s) rest

/-- Transfer a unary counter, preserving the previous destination value. -/
theorem run_move {a b : Register} (different : a ≠ b) (s : Store) :
    Executes (move a b) s .normal ((s.set a 0).set b (s b + s a)) := by
  generalize eq : s a = n
  induction n generalizing s with
  | zero =>
    simp only [Nat.add_zero]
    rw [← eq, Store.set_same, Store.set_same]
    exact whilePositive_zero eq
  | succ n ih =>
    let next := (s.set a (s a - 1)).set b (s b + 1)
    have hNext : next a = n := by simp [next, Store.set, different, eq]
    have first : Executes (inc b) (s.set a (s a - 1)) .normal next := by
      simpa [next, Store.set, Ne.symm different] using run_inc b (s.set a (s a - 1))
    have rest := ih next hNext
    have normalized : (next.set a 0).set b (next b + n) = (s.set a 0).set b (s b + (n + 1)) := by
      funext i
      by_cases ha : i = a <;> by_cases hb : i = b <;>
        simp [next, Store.set, ha, hb, different] <;> omega
    rw [normalized] at rest
    exact whilePositive_pos (by omega) first rest

theorem run_copy {a b : Register} (ab : a ≠ b) (au : a ≠ u) (bu : b ≠ u)
    (s : Store) (hu : s u = 0) :
    Executes (copy a b) s .normal (s.set b (s b + s a)) := by
  have loop (s : Store) : Executes (whilePositive a (.seq (inc b) (inc u))) s .normal
      (((s.set a 0).set b (s b + s a)).set u (s u + s a)) := by
    generalize eq : s a = n
    induction n generalizing s with
    | zero =>
      simp only [Nat.add_zero]
      rw [← eq, Store.set_same, Store.set_same, Store.set_same]
      exact whilePositive_zero eq
    | succ n ih =>
      let decState := s.set a (s a - 1)
      let next := (decState.set b (s b + 1)).set u (s u + 1)
      have hNext : next a = n := by simp [next, decState, Store.set, ab, au, eq]
      have first : Executes (.seq (inc b) (inc u)) decState .normal next := by
        have hb : decState b = s b := Store.get_set_other _ _ _ _ (Ne.symm ab)
        have hc : (decState.set b (s b + 1)) u = s u := by
          simp [decState, Store.set, Ne.symm bu, Ne.symm au]
        have runB := run_inc b decState
        have runU := run_inc u (decState.set b (s b + 1))
        rw [hb] at runB
        rw [hc] at runU
        exact then_normal runB runU
      have rest := ih next hNext
      have normalized : ((next.set a 0).set b (next b + n)).set u (next u + n) =
          ((s.set a 0).set b (s b + (n + 1))).set u (s u + (n + 1)) := by
        funext i
        by_cases ha : i = a <;> by_cases hb : i = b <;> by_cases hc : i = u <;>
          simp [next, decState, Store.set, ha, hb, hc, ab, au, bu] <;> omega
      rw [normalized] at rest
      exact whilePositive_pos (by omega) first rest
  let mid := ((s.set a 0).set b (s b + s a)).set u (s u + s a)
  have finish := run_move (Ne.symm au) mid
  have normalized : (mid.set u 0).set a (mid a + mid u) = s.set b (s b + s a) := by
    funext i
    by_cases ha : i = a <;> by_cases hb : i = b <;> by_cases hc : i = u <;>
      simp [mid, Store.set, ha, hb, hc, ab, au, bu, Ne.symm ab, Ne.symm au, Ne.symm bu, hu]
  rw [normalized] at finish
  exact then_normal (loop s) finish

/-- The branch after incrementing the second coordinate traverses one
diagonal cell of the Cantor enumeration. -/
theorem run_advance {a b : Register} (ab : a ≠ b) (s : Store) :
    Executes (.seq (inc b) (ifZero a (move b a))) s .normal
      ((s.set a (Cantor.advance (s a, s b)).1).set b (Cantor.advance (s a, s b)).2) := by
  let next := s.set b (s b + 1)
  have ha : next a = s a := Store.get_set_other _ _ _ _ ab
  by_cases zero : s a = 0
  · have after := run_move (Ne.symm ab) next
    have normalized : (next.set b 0).set a (next a + next b) =
        (s.set a (s b + 1)).set b 0 := by
      simp only [next, ha, zero, Nat.zero_add, Store.get_set, Store.set_set]
      exact Store.set_comm _ (Ne.symm ab) _ _
    rw [normalized] at after
    simpa only [Cantor.advance, zero, ↓reduceIte] using
      then_normal (run_inc b s) (ifZero_zero_normal (ha.trans zero) after)
  · have after := ifZero_pos (body := move b a) (s := next) (r := a) (by rwa [ha])
    simp only [ha] at after
    have normalized : next.set a (s a - 1) = (s.set a (s a - 1)).set b (s b + 1) :=
      Store.set_comm _ (Ne.symm ab) _ _
    rw [normalized] at after
    simpa only [Cantor.advance, zero, ↓reduceIte] using then_normal (run_inc b s) after

theorem run_unpair_from {a b input : Register} (ab : a ≠ b) (ai : a ≠ input) (bi : b ≠ input)
    (s : Store) :
    let output := Cantor.advanceLoop (s input) (s a, s b)
    Executes (unpair a b input) s .normal (((s.set input 0).set a output.1).set b output.2) := by
  generalize eq : s input = n
  induction n generalizing s with
  | zero =>
    simp only [Cantor.advanceLoop]
    rw [← eq, Store.set_same, Store.set_same, Store.set_same]
    exact whilePositive_zero eq
  | succ n ih =>
    let decState := s.set input n
    let cell := Cantor.advance (s a, s b)
    let next := (decState.set a cell.1).set b cell.2
    have hInput : next input = n := by simp [next, decState, Store.set, Ne.symm ai, Ne.symm bi]
    have ha : decState a = s a := Store.get_set_other _ _ _ _ ai
    have hb : decState b = s b := Store.get_set_other _ _ _ _ bi
    have first := run_advance ab decState
    rw [ha, hb] at first
    have startEq : s.set input (s input - 1) = decState := by simp [decState, eq]
    have rest := ih next hInput
    have normalized :
        (((next.set input 0).set a (Cantor.advanceLoop n (next a, next b)).1).set b
          (Cantor.advanceLoop n (next a, next b)).2) =
        (((s.set input 0).set a (Cantor.advanceLoop n cell).1).set b (Cantor.advanceLoop n cell).2) := by
      have hPair : (next a, next b) = cell := by simp [next, Store.set, ab]
      rw [hPair]
      funext i
      by_cases h₁ : i = a <;> by_cases h₂ : i = b <;> by_cases h₃ : i = input <;>
        simp [next, decState, Store.set, h₁, h₂, h₃]
    dsimp only at rest
    rw [normalized] at rest
    exact whilePositive_pos (by omega) (startEq.symm ▸ first) rest

theorem run_unpair {a b input : Register} (ab : a ≠ b) (ai : a ≠ input) (bi : b ≠ input)
    (s : Store) (ha : s a = 0) (hb : s b = 0) :
    let output := Cantor.unpair (s input)
    Executes (unpair a b input) s .normal (((s.set input 0).set a output.1).set b output.2) := by
  simpa only [ha, hb, Cantor.advanceLoop_unpair] using run_unpair_from ab ai bi s

end PalomarI3380.Compiler.Source
