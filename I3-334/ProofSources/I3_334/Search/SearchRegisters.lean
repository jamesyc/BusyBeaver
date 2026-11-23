module
public import I3_334.Search.SearchProgram
public import I3_334Support.Search.Compiler.RegisterArithmetic
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (inc dec break_ continue_ halt block ifPositive ifZero
  whilePositive clear move unpair LineRuns then_normal run_clear run_move run_inc
  whilePositive_zero whilePositive_pos ifZero_pos ifZero_zero_normal
  ifPositive_zero ifPositive_pos_normal run_unpair run_copy_with)

theorem run_copy {a b : Register} (different : a ≠ b) (source : a ≠ u) (target : b ≠ u)
    (s : Store) (free : s u = 0) :
    Executes (copy a b) s .normal (s.set b (s b + s a)) :=
  run_copy_with different source target s free

theorem run_pop {source target : Register} (different : source ≠ target)
    (sourceAux : source ≠ u) (targetAux : target ≠ u)
    (s : Store) (clearTarget : s target = 0) (clearAux : s u = 0) :
    Executes (pop source target) s .normal
      ((s.set source (Cantor.unpair (s source)).2).set target (Cantor.unpair (s source)).1) := by
  let fields := Cantor.unpair (s source)
  let split := (((s.set source 0).set target fields.1).set u fields.2)
  have first : Executes (unpair target u source) s .normal split :=
    run_unpair targetAux different.symm sourceAux.symm s clearTarget clearAux
  have move := run_move sourceAux.symm split
  have destination : (split.set u 0).set source (split source + split u) =
      (s.set source fields.2).set target fields.1 := by
    funext i
    by_cases a : i = source <;> by_cases b : i = target <;> by_cases x : i = u <;>
      simp [split, Store.set, a, b, x, different, different.symm, sourceAux, sourceAux.symm,
        targetAux, targetAux.symm, clearAux]
  rw [destination] at move
  exact then_normal first move

/-- Consume the unary token and the common portion of the expected
field. Only a shortage can clear the candidate marker in this loop. -/
theorem run_compare_prefix (s : Store) :
    Executes (whilePositive tok (ifZero expected (clear gues))) s .normal
      (((s.set tok 0).set expected (s expected - s tok)).set gues
        (if s expected < s tok then 0 else s gues)) := by
  generalize code : s tok = n
  induction n generalizing s with
  | zero =>
    simp only [Nat.sub_zero, Nat.not_lt_zero, ↓reduceIte]
    rw [← code, Store.set_same, Store.set_same, Store.set_same]
    exact whilePositive_zero code
  | succ n ih =>
    let decTok := s.set tok n
    have decrease : s.set tok (s tok-1) = decTok := by simp [decTok,code]
    have sameExpected : decTok expected = s expected := by simp [decTok,Store.set,tok,expected]
    have sameGues : decTok gues = s gues := by simp [decTok,Store.set,tok,gues]
    by_cases empty : s expected = 0
    · let mid := decTok.set gues 0
      have first : Executes (ifZero expected (clear gues)) (s.set tok (s tok-1)) .normal mid := by
        rw [decrease]
        exact ifZero_zero_normal (sameExpected.trans empty) (run_clear gues decTok)
      have remains : mid tok = n := by simp [mid,decTok,Store.set,tok,gues]
      have rest := ih mid remains
      have norm :
          (((mid.set tok 0).set expected (mid expected - n)).set gues
            (if mid expected < n then 0 else mid gues)) =
          (((s.set tok 0).set expected (s expected - (n+1))).set gues
            (if s expected < n+1 then 0 else s gues)) := by
        funext i
        by_cases a : i = tok <;> by_cases b : i = expected <;> by_cases c : i = gues <;>
          simp [mid,decTok,Store.set,a,b,c,tok,expected,gues,empty]
      rw [norm] at rest
      exact whilePositive_pos (by omega) first rest
    · let mid := decTok.set expected (s expected - 1)
      have first : Executes (ifZero expected (clear gues)) (s.set tok (s tok-1)) .normal mid := by
        rw [decrease]
        simpa only [mid,sameExpected] using
          ifZero_pos (body := clear gues) (s := decTok) (r := expected) (by rwa [sameExpected])
      have remains : mid tok = n := by simp [mid,decTok,Store.set,tok,expected]
      have rest := ih mid remains
      have value : mid expected = s expected - 1 := Store.get_set _ _ _
      have marker : mid gues = s gues := by simp [mid,Store.set,expected,gues,sameGues]
      have less : s expected - 1 < n ↔ s expected < n + 1 := by omega
      have parts : s expected - 1 - n = s expected - (n+1) := by omega
      simp only [value,marker,less,parts] at rest
      have same :
          (((mid.set tok 0).set expected (s expected-(n+1))).set gues
            (if s expected < n+1 then 0 else s gues)) =
          (((s.set tok 0).set expected (s expected-(n+1))).set gues
            (if s expected < n+1 then 0 else s gues)) := by
        funext i
        by_cases a : i = tok <;> by_cases b : i = expected <;> by_cases c : i = gues <;>
          simp [mid,decTok,Store.set,a,b,c]
      rw [same] at rest
      exact whilePositive_pos (by omega) first rest

theorem run_compare (s : Store) :
    Executes compare s .normal
      (((s.set tok 0).set expected 0).set gues (if s expected = s tok then s gues else 0)) := by
  let mid := (((s.set tok 0).set expected (s expected-s tok)).set gues
    (if s expected < s tok then 0 else s gues))
  have first : Executes _ s .normal mid := run_compare_prefix s
  have expectedValue : mid expected = s expected-s tok := by simp [mid, Store.set, expected, gues]
  by_cases short : s expected ≤ s tok
  · have stop : mid expected = 0 := by rw [expectedValue, Nat.sub_eq_zero_of_le short]
    have last := ifPositive_zero (body := .seq (clear expected) (clear gues)) stop
    have result : mid =
        (((s.set tok 0).set expected 0).set gues (if s expected = s tok then s gues else 0)) := by
      unfold mid
      rw [Nat.sub_eq_zero_of_le short]
      by_cases eq : s expected = s tok
      · simp [eq]
      · simp [eq, show s expected < s tok by omega]
    rw [result] at last first
    exact then_normal first last
  · have nonzero : mid expected ≠ 0 := by rw [expectedValue]; omega
    let shifted := mid.set expected (mid expected - 1)
    have clears := then_normal (run_clear expected shifted) (run_clear gues (shifted.set expected 0))
    have last := ifPositive_pos_normal nonzero clears
    have result : ((shifted.set expected 0).set gues 0) =
        (((s.set tok 0).set expected 0).set gues (if s expected = s tok then s gues else 0)) := by
      have different : s expected ≠ s tok := by omega
      simp only [shifted, mid, Store.set_set, different, ↓reduceIte]
      funext i
      by_cases a : i = tok <;> by_cases b : i = expected <;> by_cases c : i = gues <;>
        simp [Store.set,a,b,c,tok,expected,gues]
    rw [result] at last
    exact then_normal first last

/-- Read one outer proof field, preserving the unused suffix and
clearing the temporary token after transfer. -/
theorem run_read {target : Register} (diffPl : target ≠ pl) (diffTok : target ≠ tok)
    (s : Store) (freeTok : s tok = 0) (freeAux : s u = 0) :
    Executes (read target) s .normal
      ((s.set pl (Cantor.unpair (s pl)).2).set target (s target + (Cantor.unpair (s pl)).1)) := by
  let fields := Cantor.unpair (s pl)
  let mid := (s.set pl fields.2).set tok fields.1
  have first : Executes (pop pl tok) s .normal mid :=
    run_pop (by decide) (by decide) (by decide) s freeTok freeAux
  have last := run_move diffTok.symm mid
  have result : (mid.set tok 0).set target (mid target + mid tok) =
      (s.set pl fields.2).set target (s target + fields.1) := by
    funext r
    by_cases ht : r = target <;> by_cases hl : r = pl <;> by_cases ht' : r = tok <;>
      simp [mid,Store.set,ht,hl,ht',diffPl,diffTok,freeTok,pl,tok]
  rw [result] at last
  exact then_normal first last

theorem run_eat (s : Store) (freeTok : s tok = 0) (freeAux : s u = 0) :
    Executes eat s .normal
      (((s.set fr (Cantor.unpair (s fr)).2).set expected 0).set gues
        (if s expected = (Cantor.unpair (s fr)).1 then s gues else 0)) := by
  let fields := Cantor.unpair (s fr)
  let mid := (s.set fr fields.2).set tok fields.1
  have first : Executes (pop fr tok) s .normal mid :=
    run_pop (by decide) (by decide) (by decide) s freeTok freeAux
  have last := run_compare mid
  have result : (((mid.set tok 0).set expected 0).set gues
        (if mid expected = mid tok then mid gues else 0)) =
      (((s.set fr fields.2).set expected 0).set gues
        (if s expected = fields.1 then s gues else 0)) := by
    funext r
    by_cases a : r = tok <;> by_cases b : r = fr <;>
      by_cases c : r = expected <;> by_cases d : r = gues <;>
      simp [mid,Store.set,a,b,c,d,freeTok,tok,fr,expected,gues]
  rw [result] at last
  exact then_normal first last

/-- The auxiliary register returns to zero after the two proof fronts
exchange places. -/
theorem run_exchange (s : Store) (free : s u = 0) :
    Executes exchange s .normal ((s.set fr (s lv)).set lv (s fr)) := by
  let first := (s.set fr 0).set u (s fr)
  let second := (first.set lv 0).set fr (s lv)
  have a : Executes (move fr u) s .normal first := by
    simpa only [free,Nat.zero_add] using run_move (a := fr) (b := u) (by decide) s
  have b : Executes (move lv fr) first .normal second := by
    simpa [first,second,Store.set,fr,lv,u] using run_move (a := lv) (b := fr) (by decide) first
  have c := run_move (a := u) (b := lv) (by decide) second
  have balanced : (second.set u 0).set lv (second lv + second u) =
      (s.set fr (s lv)).set lv (s fr) := by
    funext r
    by_cases hf : r = fr <;> by_cases hl : r = lv <;> by_cases hu : r = u <;>
      simp [second,first,Store.set,hf,hl,hu,free,fr,lv,u]
  rw [balanced] at c
  exact then_normal a (then_normal b c)

theorem run_dictionaryPart (takeLeft : Bool) (s : Store)
    (freeExpected : s expected = 0) (freeAux : s u = 0) :
    Executes (dictionaryPart takeLeft) s .normal
      (s.set tmp (if takeLeft then (Cantor.unpair (s tmp)).1 else (Cantor.unpair (s tmp)).2)) := by
  let fields := Cantor.unpair (s tmp)
  let split := (((s.set tmp 0).set expected fields.1).set u fields.2)
  have first : Executes (unpair expected u tmp) s .normal split :=
    run_unpair (by decide) (by decide) (by decide) s freeExpected freeAux
  cases takeLeft
  · let mid := (split.set u 0).set tmp (split tmp + split u)
    have shifted : Executes (move u tmp) split .normal mid := run_move (by decide) split
    have cleaned := run_clear expected mid
    have restored : mid.set expected 0 = s.set tmp fields.2 := by
      funext r
      by_cases a : r = tmp <;> by_cases b : r = expected <;> by_cases c : r = u <;>
        simp [split,mid,Store.set,a,b,c,freeExpected,freeAux,tmp,expected,u]
    rw [restored] at cleaned
    exact then_normal first (then_normal shifted cleaned)
  · let mid := (split.set expected 0).set tmp (split tmp + split expected)
    have shifted : Executes (move expected tmp) split .normal mid := run_move (by decide) split
    have cleaned := run_clear u mid
    have restored : mid.set u 0 = s.set tmp fields.1 := by
      funext r
      by_cases a : r = tmp <;> by_cases b : r = expected <;> by_cases c : r = u <;>
        simp [split,mid,Store.set,a,b,c,freeExpected,freeAux,tmp,expected,u]
    rw [restored] at cleaned
    exact then_normal first (then_normal shifted cleaned)

end PalomarI3334.SearchProgram
