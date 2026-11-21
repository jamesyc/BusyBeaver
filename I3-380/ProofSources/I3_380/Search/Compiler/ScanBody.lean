module
public import I3_380.Search.Compiler.ScanLoop
@[expose] public section

namespace PalomarI3380.Compiler.Source

def arityEffect (s : Store) : Store :=
  (((s.set goal (s goal + (s exp - 1))).set exp (s exp - 1 + 1)).set gues
    (mark s (s exp ≠ 0)))

theorem run_arity (s : Store) (aux : s u = 0) : Executes arity s .normal (arityEffect s) := by
  let n := s exp - 1
  let marker := mark s (s exp ≠ 0)
  let next := (s.set exp n).set gues marker
  have branch : Executes (ifZero exp (clear gues)) s .normal next := by
    by_cases h : s exp = 0
    · have update : s.set exp n = s := by
        have same : n = s exp := by simp [n, h]
        rw [same, Store.set_same]
      have marked : marker = 0 := by simp [marker, mark, h]
      have state : next = s.set gues 0 := by simp only [next, update, marked]
      rw [state]
      exact ifZero_zero_normal h (run_clear gues s)
    · have marked : marker = s gues := by simp [marker, mark, h]
      have state : next = s.set exp n := by
        simp only [next, marked]
        have keep : (s.set exp n) gues = s gues :=
          Store.get_set_other _ _ _ _ (by decide : gues ≠ exp)
        simpa only [keep] using Store.set_same (s.set exp n) gues
      rw [state]
      exact ifZero_pos h
  have hAux : next u = 0 := by simpa [next, Store.set, u, exp, gues] using aux
  have hGoal : next goal = s goal := by simp [next, Store.set, goal, exp, gues]
  have hExp : next exp = n := by simp [next, Store.set, exp, gues]
  have copying := run_copy (a := exp) (b := goal) (by decide) (by decide) (by decide) next hAux
  rw [hGoal, hExp] at copying
  let mid := next.set goal (s goal + n)
  have bias : mid exp = n :=
    (Store.get_set_other _ _ _ _ (by decide : exp ≠ goal)).trans hExp
  have final := run_inc exp mid
  rw [bias] at final
  have outcome : mid.set exp (n + 1) = arityEffect s := by
    funext i
    have e : marker = mark s (s exp ≠ 0) := rfl
    by_cases h₁ : i = (3 : Register) <;> by_cases h₂ : i = (11 : Register) <;> by_cases h₃ : i = (5 : Register) <;>
      simp [mid, next, arityEffect, Store.set, goal, exp, gues, h₁, h₂, h₃, e, n]
  rw [outcome] at final
  exact then_normal branch (then_normal copying final)

def scanBodyEffect (s : Store) : Store :=
  let d := rawFields (s tmp)
  let f := rawFields (s fr)
  let ok := d.arityField ≠ 0 ∧ d.arityField = f.arityField ∧ d.tag = f.tag
  ((((s.set tmp d.rest).set fr f.rest).set goal (s goal + (d.arityField - 1))).set gues (mark s ok))

set_option maxHeartbeats 6000000 in
theorem run_scanBody (s : Store) (zeroExp : s exp = 0) (zeroTok : s tok = 0) (zeroAux : s u = 0) :
    Executes scanBody s .normal (scanBodyEffect s) := by
  let d₁ := Cantor.unpair (s tmp)
  let d₂ := Cantor.unpair d₁.2
  let f₁ := Cantor.unpair (s fr)
  let f₂ := Cantor.unpair f₁.2
  let afterPop := (s.set tmp d₁.2).set exp d₁.1
  have pop₁ : Executes (pop tmp exp) s .normal afterPop :=
    run_pop (by decide) (by decide) (by decide) s zeroExp zeroAux
  have afterPopAux : afterPop u = 0 := by simpa [afterPop, Store.set, exp, tmp, u] using zeroAux
  let afterBias := arityEffect afterPop
  have bias := run_arity afterPop afterPopAux
  have hTok : afterBias tok = 0 :=
    by simpa [afterBias, arityEffect, afterPop, Store.set, tok, tmp, exp, goal, gues] using zeroTok
  have hAux : afterBias u = 0 :=
    by simpa [afterBias, arityEffect, afterPop, Store.set, u, tmp, exp, goal, gues] using zeroAux
  let afterHead := (((afterBias.set fr f₁.2).set exp 0).set gues (mark afterBias (d₁.1 - 1 + 1 = f₁.1)))
  have head : Executes eat afterBias .normal afterHead := by
    have h := run_eat afterBias hTok hAux
    have hExp : afterBias exp = d₁.1 - 1 + 1 := by simp [afterBias, arityEffect, afterPop, Store.set, gues, exp]
    have front : afterBias fr = s fr := by
      simp [afterBias, arityEffect, afterPop, Store.set, fr, tmp, exp, goal, gues]
    simpa only [afterHead, hExp, front, mark, f₁] using h
  have hz : afterHead exp = 0 := by simp [afterHead, Store.set, exp, gues]
  have ha : afterHead u = 0 := by simpa [afterHead, Store.set, u, fr, exp, gues] using hAux
  have ht : afterHead tmp = d₁.2 := by
    simp [afterHead, afterBias, arityEffect, afterPop, Store.set, tmp, fr, exp, goal, gues]
  let afterTag := (afterHead.set tmp d₂.2).set exp d₂.1
  have pop₂ : Executes (pop tmp exp) afterHead .normal afterTag := by
    simpa only [afterTag, ht, d₂] using run_pop (src := tmp) (dst := exp)
      (by decide) (by decide) (by decide) afterHead hz ha
  have tokTag : afterTag tok = 0 := by
    simpa [afterTag, afterHead, Store.set, tok, tmp, fr, exp, gues] using hTok
  have auxTag : afterTag u = 0 := by simpa [afterTag, Store.set, u, tmp, exp] using ha
  have tail := run_eat afterTag tokTag auxTag
  have vHeadGuess : afterHead gues = mark afterBias (d₁.1 - 1 + 1 = f₁.1) := Store.get_set _ _ _
  have vBiasGuess : afterBias gues = mark s (d₁.1 ≠ 0) := by
    simp [afterBias, arityEffect, afterPop, Store.set, exp, gues, tmp, mark]
  have vTagGuess : afterTag gues = afterHead gues := by simp [afterTag, Store.set, gues, tmp, exp]
  have vTagExp : afterTag exp = d₂.1 := Store.get_set _ _ _
  have vTagFr : afterTag fr = f₁.2 := by
    simp [afterTag, afterHead, Store.set, tmp, fr, exp, gues]
  have guess :
      (if d₂.1 = f₂.1 then afterTag gues else 0) =
        mark s (d₁.1 ≠ 0 ∧ d₁.1 = f₁.1 ∧ d₂.1 = f₂.1) := by
    rw [vTagGuess, vHeadGuess]
    simp only [mark, vBiasGuess]
    by_cases h : d₁.1 = 0
    · simp [h]
    · have next : d₁.1 - 1 + 1 = d₁.1 := by omega
      simp only [next]
      by_cases same : d₁.1 = f₁.1 <;> by_cases sameTag : d₂.1 = f₂.1 <;> simp [same, sameTag]
  dsimp only at tail
  rw [vTagExp, vTagFr] at tail
  change Executes eat afterTag .normal (((afterTag.set fr f₂.2).set exp 0).set gues
    (if d₂.1 = f₂.1 then afterTag gues else 0)) at tail
  rw [guess] at tail
  have final : (((afterTag.set fr f₂.2).set exp 0).set gues
      (mark s (d₁.1 ≠ 0 ∧ d₁.1 = f₁.1 ∧ d₂.1 = f₂.1))) = scanBodyEffect s := by
    funext i
    by_cases q₁ : i = (9 : Register) <;> by_cases q₂ : i = (4 : Register) <;>
      by_cases q₃ : i = (11 : Register) <;> by_cases q₄ : i = (3 : Register) <;>
      by_cases q₅ : i = (5 : Register) <;>
      simp [scanBodyEffect, afterTag, afterHead, afterBias, afterPop, arityEffect,
        Store.set, tmp, fr, exp, goal, gues, d₁, d₂, f₁, f₂, rawFields,
        q₁, q₂, q₃, q₄, q₅, show s 11 = 0 from zeroExp] <;> rfl
  rw [final] at tail
  exact then_normal pop₁ (then_normal bias (then_normal head (then_normal pop₂ tail)))

end PalomarI3380.Compiler.Source
