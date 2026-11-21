module
public import I3_380.Search.Compiler.Compare
public import I3_380.Search.WordCompare
@[expose] public section

namespace PalomarI3380.Compiler.Source

/-- Consume one numeric field, retaining the marker only on equality. -/
theorem run_eat (s : Store) (tokenZero : s tok = 0) (auxZero : s u = 0) :
    let c := Cantor.unpair (s fr)
    Executes eat s .normal (((s.set fr c.2).set exp 0).set gues
      (if s exp = c.1 then s gues else 0)) := by
  dsimp only
  let c := Cantor.unpair (s fr)
  let mid := (s.set fr c.2).set tok c.1
  have popRun : Executes (pop fr tok) s .normal mid :=
    run_pop (by decide) (by decide) (by decide) s tokenZero auxZero
  have compared := run_compare mid
  have expected : mid exp = s exp := by simp [mid, Store.set, fr, tok, exp]
  have actual : mid tok = c.1 := Store.get_set _ _ _
  have mark : mid gues = s gues := by simp [mid, Store.set, gues, tok, fr]
  rw [expected, actual, mark] at compared
  have normalized :
      ((mid.set exp 0).set tok 0).set gues (if s exp = c.1 then s gues else 0) =
        ((s.set fr c.2).set exp 0).set gues (if s exp = c.1 then s gues else 0) := by
    have swapTokens := Store.set_comm (s.set fr c.2) (by decide : tok ≠ exp) c.1 0
    simp only [mid, swapTokens, Store.set_set]
    have token : (s.set fr c.2).set exp 0 tok = 0 := by
      rw [Store.get_set_other _ _ _ _ (by decide : tok ≠ exp),
        Store.get_set_other _ _ _ _ (by decide : tok ≠ fr), tokenZero]
    exact congrArg (fun store : Store => store.set gues (if s exp = c.1 then s gues else 0))
      (by simpa only [token] using Store.set_same ((s.set fr c.2).set exp 0) tok)
  rw [normalized] at compared
  exact then_normal popRun compared

/-- Compare an explicit two-field token, preserving the untouched
suffix regardless of whether an equality check fails. -/
theorem eatLiteral_effect (code : Nat) (token : Token) :
    (rawFields code).arityField = token.arity + 1 ∧ (rawFields code).tag = token.tag ↔
      readToken code = some (token, (rawFields code).rest) := by
  simp only [rawFields, readToken]
  split
  · rename_i h
    rw [h]
    simp
  · rename_i h
    constructor
    · rintro ⟨arity, tag⟩
      obtain ⟨a, t⟩ := token
      simp only at arity tag
      simp only [arity, tag, Nat.add_sub_cancel_right]
    · intro equal
      have head := congrArg (fun o : Option (Token × Nat) => o.map Prod.fst) equal
      simp only [Option.map_some, Option.some.injEq] at head
      have arity := congrArg Token.arity head
      change (Cantor.unpair code).1 - 1 = token.arity at arity
      exact ⟨by omega, congrArg Token.tag head⟩

theorem run_side (s : Store) (clear : s tmp = 0) :
    Executes side s .normal ((s.set fr (s lv)).set lv (s fr)) := by
  let x := (s.set fr 0).set tmp (s tmp + s fr)
  let y := (x.set lv 0).set fr (x fr + x lv)
  have h₁ : Executes (move fr tmp) s .normal x := run_move (by decide) s
  have h₂ : Executes (move lv fr) x .normal y := run_move (by decide) x
  have h₃ := run_move (a := tmp) (b := lv) (by decide) y
  have normalize : (y.set tmp 0).set lv (y lv + y tmp) = (s.set fr (s lv)).set lv (s fr) := by
    funext i
    by_cases a : i = fr <;> by_cases b : i = lv <;> by_cases c : i = tmp <;>
      simp_all [y, x, Store.set, fr, tmp, lv]
  rw [normalize] at h₃
  exact then_normal h₁ (then_normal h₂ h₃)

end PalomarI3380.Compiler.Source
