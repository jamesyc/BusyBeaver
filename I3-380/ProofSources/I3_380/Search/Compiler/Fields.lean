module
public import I3_380.Search.Compiler.RegisterArithmetic
@[expose] public section

namespace PalomarI3380.Compiler.Source

theorem run_read {dst : Register} (notPL : dst ≠ pl) (notToken : dst ≠ tok)
    (s : Store) (tokenZero : s tok = 0) (auxZero : s u = 0) :
    let field := Cantor.unpair (s pl)
    Executes (read dst) s .normal ((s.set pl field.2).set dst (s dst + field.1)) := by
  dsimp only
  let field := Cantor.unpair (s pl)
  let first := ((s.set pl 0).set tok field.1).set u field.2
  let second := ((s.set pl field.2).set tok field.1)
  have step₁ := run_unpair (a := tok) (b := u) (input := pl)
    (by decide) (by decide) (by decide) s tokenZero auxZero
  change Executes (unpair tok u pl) s .normal first at step₁
  have step₂ := run_move (a := u) (b := pl) (by decide) first
  have normalize₂ : (first.set u 0).set pl (first pl + first u) = second := by
    funext i
    by_cases a : i = pl <;> by_cases b : i = tok <;> by_cases c : i = u <;>
      simp [first, second, Store.set, a, b, c, auxZero,
        show pl ≠ u by decide, show pl ≠ tok by decide, show tok ≠ pl by decide,
        show tok ≠ u by decide, show u ≠ pl by decide, show u ≠ tok by decide]
  rw [normalize₂] at step₂
  have step₃ := run_move (Ne.symm notToken) second
  have normalize₃ : (second.set tok 0).set dst (second dst + second tok) =
      (s.set pl field.2).set dst (s dst + field.1) := by
    have dest : second dst = s dst := by simp [second, Store.set, notPL, notToken]
    have token : second tok = field.1 := by simp [second]
    rw [dest, token]
    change (((s.set pl field.2).set tok field.1).set tok 0).set dst (s dst + field.1) = _
    rw [Store.set_set]
    have drop : (s.set pl field.2).set tok 0 = s.set pl field.2 := by
      rw [Store.set_comm _ (by decide : pl ≠ tok), ← tokenZero, Store.set_same]
    rw [drop]
  rw [normalize₃] at step₃
  exact then_normal step₁ (then_normal step₂ step₃)

theorem run_pop {src dst : Register} (different : dst ≠ src) (notSrc : u ≠ src) (notDst : dst ≠ u)
    (s : Store) (destZero : s dst = 0) (auxZero : s u = 0) :
    let field := Cantor.unpair (s src)
    Executes (pop src dst) s .normal ((s.set src field.2).set dst field.1) := by
  dsimp only
  let field := Cantor.unpair (s src)
  let mid := ((s.set src 0).set dst field.1).set u field.2
  have first := run_unpair notDst different notSrc s destZero auxZero
  change Executes (unpair dst u src) s .normal mid at first
  have second := run_move notSrc mid
  have normalize : (mid.set u 0).set src (mid src + mid u) = (s.set src field.2).set dst field.1 := by
    have source : mid src = 0 := by simp [mid, Store.set, Ne.symm notSrc, Ne.symm different]
    have aux : mid u = field.2 := Store.get_set _ _ _
    rw [source, aux, Nat.zero_add]
    funext i
    by_cases a : i = src <;> by_cases b : i = dst <;> by_cases c : i = u <;>
      simp [mid, Store.set, a, b, c, auxZero, different, notSrc, notDst,
        Ne.symm different, Ne.symm notDst]
  rw [normalize] at second
  exact then_normal first second

theorem read_pair {dst : Register} (notPL : dst ≠ pl) (notToken : dst ≠ tok)
    (s : Store) (tokenZero : s tok = 0) (auxZero : s u = 0)
    (head tail : Nat) (code : s pl = Cantor.pair head tail) :
    Executes (read dst) s .normal ((s.set pl tail).set dst (s dst + head)) := by
  simpa only [code, Cantor.unpair_pair] using run_read notPL notToken s tokenZero auxZero

end PalomarI3380.Compiler.Source
