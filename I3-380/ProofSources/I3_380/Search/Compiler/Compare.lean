module
public import I3_380.Search.Compiler.Fields
@[expose] public section

namespace PalomarI3380.Compiler.Source

private theorem exp_ne_tok : exp ≠ tok := by decide
private theorem exp_ne_gues : exp ≠ gues := by decide
private theorem tok_ne_gues : tok ≠ gues := by decide

private theorem compareHeads_runs (s : Store) :
    Executes compareHeads s .normal
      (((s.set exp 0).set tok (s tok - s exp)).set gues (if s tok < s exp then 0 else s gues)) := by
  generalize h : s exp = n
  induction n generalizing s with
  | zero =>
    simp only [Nat.sub_zero, Nat.not_lt_zero, ↓reduceIte]
    rw [← h, Store.set_same, Store.set_same, Store.set_same]
    exact whilePositive_zero h
  | succ n ih =>
    let mid := s.set exp n
    have dec : s.set exp (s exp - 1) = mid := by simp [mid, h]
    have token : mid tok = s tok := Store.get_set_other _ _ _ _ exp_ne_tok.symm
    by_cases hTok : s tok = 0
    · let out := (mid.set gues 0).set exp 0
      have hFirst := then_normal (run_clear gues mid) (run_clear exp (mid.set gues 0))
      have zero : mid tok = 0 := token.trans hTok
      have stop : out exp = 0 := Store.get_set _ _ _
      have hLoop : Executes compareHeads s .normal out := by
        apply whilePositive_pos (by omega : s exp ≠ 0)
        · rw [dec]
          exact ifZero_zero_normal zero hFirst
        · exact whilePositive_zero stop
      have norm : (((s.set exp 0).set tok (s tok - (n + 1))).set gues
          (if s tok < n + 1 then 0 else s gues)) = out := by
        simp only [hTok, Nat.zero_sub, Nat.zero_lt_succ, ↓reduceIte]
        funext i
        by_cases a : i = exp <;> by_cases b : i = tok <;> by_cases c : i = gues <;>
          simp [out, mid, Store.set, a, b, c, hTok, exp_ne_tok.symm]
      exact norm.symm ▸ hLoop
    · let next := mid.set tok (s tok - 1)
      have first : Executes (ifZero tok mismatch) (s.set exp (s exp - 1)) .normal next := by
        rw [dec]
        have hPos := ifZero_pos (body := mismatch) (s := mid) (r := tok) (by rwa [token])
        simpa only [next, token] using hPos
      have nextExp : next exp = n := by simp [next, mid, Store.set, exp_ne_tok]
      have nextTok : next tok = s tok - 1 := Store.get_set _ _ _
      have nextG : next gues = s gues := by
        simp [next, mid, Store.set, tok_ne_gues.symm, exp_ne_gues.symm]
      have rest := ih next nextExp
      simp only [nextG, nextTok, show s tok - 1 - n = s tok - (n + 1) by omega,
        show s tok - 1 < n ↔ s tok < n + 1 by omega] at rest
      have norm : ((next.set exp 0).set tok (s tok - (n + 1))).set gues
          (if s tok < n + 1 then 0 else s gues) =
          ((s.set exp 0).set tok (s tok - (n + 1))).set gues
          (if s tok < n + 1 then 0 else s gues) := by
        funext i
        by_cases a : i = exp <;> by_cases b : i = tok <;> by_cases c : i = gues <;>
          simp [next, mid, Store.set, a, b, c]
      rw [norm] at rest
      exact whilePositive_pos (by omega) first rest

private theorem compareTail_runs (s : Store) :
    Executes (whilePositive tok (clear gues)) s .normal
      ((s.set tok 0).set gues (if s tok = 0 then s gues else 0)) := by
  generalize h : s tok = n
  induction n generalizing s with
  | zero =>
    simp only [↓reduceIte]
    rw [← h, Store.set_same, Store.set_same]
    exact whilePositive_zero h
  | succ n ih =>
    let mid := s.set tok n
    let next := mid.set gues 0
    have dec : s.set tok (s tok - 1) = mid := by simp [mid, h]
    have first : Executes (clear gues) (s.set tok (s tok - 1)) .normal next := by
      rw [dec]
      exact run_clear gues mid
    have token : next tok = n := by simp [mid, next, Store.set, tok_ne_gues]
    have tail := ih next token
    rw [show next gues = 0 from Store.get_set _ _ _, ite_self] at tail
    have norm : (next.set tok 0).set gues 0 = (s.set tok 0).set gues 0 := by
      funext i
      by_cases a : i = tok <;> by_cases b : i = gues <;> simp [next, mid, Store.set, a, b]
    rw [norm] at tail
    simpa only [Nat.succ_ne_zero, ↓reduceIte] using
      whilePositive_pos (by omega : s tok ≠ 0) first tail

/-- Compare two unary fields, clearing both. Any mismatch clears the
candidate marker, which the remaining verifier commands preserve. -/
theorem run_compare (s : Store) :
    Executes compare s .normal
      (((s.set exp 0).set tok 0).set gues (if s exp = s tok then s gues else 0)) := by
  let marker := if s tok < s exp then 0 else s gues
  let mid := ((s.set exp 0).set tok (s tok - s exp)).set gues marker
  have first : Executes compareHeads s .normal mid := compareHeads_runs s
  have second := compareTail_runs mid
  have hTok : mid tok = s tok - s exp := by simp [mid, Store.set, tok_ne_gues]
  have hMarker : mid gues = marker := Store.get_set _ _ _
  have mark : (if mid tok = 0 then mid gues else 0) = if s exp = s tok then s gues else 0 := by
    rw [hTok, hMarker]
    unfold marker
    split <;> split <;> (first | split <;> omega | omega)
  rw [mark] at second
  have normalize : (mid.set tok 0).set gues (if s exp = s tok then s gues else 0) =
      ((s.set exp 0).set tok 0).set gues (if s exp = s tok then s gues else 0) := by
    funext i
    by_cases ht : i = tok <;> by_cases hg : i = gues <;> simp [mid, Store.set, ht, hg]
  rw [normalize] at second
  exact then_normal first second

end PalomarI3380.Compiler.Source
