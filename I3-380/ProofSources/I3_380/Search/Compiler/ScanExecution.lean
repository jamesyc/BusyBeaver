module
public import I3_380.Search.Compiler.ScanBody
@[expose] public section

namespace PalomarI3380.Compiler.Source

def scanEffect (s : Store) (result : ScanResult) : Store :=
  ((((s.set goal 0).set tmp result.dictionaryRest).set fr result.frontRest).set gues
    (mark s (result.valid = true)))

set_option maxHeartbeats 4000000 in
theorem run_scanLoop (s : Store) (e : s exp = 0) (t : s tok = 0) (a : s u = 0) :
    Executes (whilePositive goal scanBody) s .normal
      (scanEffect s (scanLoop (s goal) (s tmp) (s fr))) := by
  induction measureEq : s goal + s tmp using Nat.strongRecOn generalizing s with
  | ind measure ih =>
    cases hGoal : s goal with
    | zero =>
      simp only [scanLoop_zero, scanEffect, mark, ↓reduceIte]
      rw [← hGoal, Store.set_same, Store.set_same, Store.set_same, Store.set_same]
      exact whilePositive_zero hGoal
    | succ n =>
      let start := s.set goal n
      let d := rawFields (s tmp)
      let f := rawFields (s fr)
      let ok := d.arityField ≠ 0 ∧ d.arityField = f.arityField ∧ d.tag = f.tag
      let next := scanBodyEffect start
      have eStart : start exp = 0 := by simpa [start, Store.set, goal, exp] using e
      have tStart : start tok = 0 := by simpa [start, Store.set, goal, tok] using t
      have aStart : start u = 0 := by simpa [start, Store.set, goal, u] using a
      have fresh : s.set goal (s goal - 1) = start := by simp [start, hGoal]
      have first := run_scanBody start eStart tStart aStart
      have vTmp : start tmp = s tmp := by simp [start, Store.set, tmp, goal]
      have vFr : start fr = s fr := by simp [start, Store.set, fr, goal]
      have vMark : start gues = s gues := by simp [start, Store.set, gues, goal]
      have hNext : next =
          (((((s.set goal n).set tmp d.rest).set fr f.rest).set goal (n + (d.arityField - 1))).set gues
            (mark s ok)) := by
        simp only [next, scanBodyEffect, vTmp, vFr, mark, vMark, start, Store.get_set, d, f, ok]
      have outE : next exp = 0 := by simpa [hNext, Store.set, goal, tmp, fr, gues, exp] using e
      have outT : next tok = 0 := by simpa [hNext, Store.set, goal, tmp, fr, gues, tok] using t
      have outA : next u = 0 := by simpa [hNext, Store.set, goal, tmp, fr, gues, u] using a
      have outGoal : next goal = n + (d.arityField - 1) := by simp [hNext, Store.set, goal, gues]
      have outTmp : next tmp = d.rest := by simp [hNext, Store.set, goal, tmp, fr, gues]
      have outFr : next fr = f.rest := by simp [hNext, Store.set, goal, fr, gues]
      have outGuess : next gues = mark s ok := by rw [hNext, Store.get_set]
      have smaller : next goal + next tmp < measure := by
        rw [outGoal, outTmp]
        have bounds := rawFields_progress (s tmp)
        simp only [d]
        omega
      have tail := ih _ smaller next outE outT outA rfl
      rw [outGoal, outTmp, outFr] at tail
      let result := scanLoop (n + (d.arityField - 1)) d.rest f.rest
      have control : (scanLoop (s goal) (s tmp) (s fr)).valid = true ↔ ok ∧ result.valid = true := by
        rw [hGoal, scanLoop]
        simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, result, ok, d, f]
        exact ⟨fun ⟨⟨⟨a, b⟩, c⟩, d⟩ => ⟨⟨a, b, c⟩, d⟩, fun ⟨⟨a, b, c⟩, d⟩ => ⟨⟨⟨a, b⟩, c⟩, d⟩⟩
      have marker : mark next (result.valid = true) =
          mark s ((scanLoop (s goal) (s tmp) (s fr)).valid = true) := by
        simp only [mark, outGuess, control]
        exact mark_compose s ok (result.valid = true)
      have finish : scanEffect next result = scanEffect s (scanLoop (s goal) (s tmp) (s fr)) := by
        have dict : (scanLoop (s goal) (s tmp) (s fr)).dictionaryRest = result.dictionaryRest := by
          rw [hGoal, scanLoop]
        have front : (scanLoop (s goal) (s tmp) (s fr)).frontRest = result.frontRest := by
          rw [hGoal, scanLoop]
        simp only [scanEffect, dict, front, marker]
        have startEq :
            (((next.set goal 0).set tmp result.dictionaryRest).set fr result.frontRest) =
              (((s.set goal 0).set tmp result.dictionaryRest).set fr result.frontRest).set gues
                (next gues) := by
          rw [outGuess, hNext]
          funext i
          by_cases h₁ : i = (3 : Register) <;> by_cases h₂ : i = (9 : Register) <;>
            by_cases h₃ : i = (4 : Register) <;> by_cases h₄ : i = (5 : Register) <;>
            simp [Store.set, goal, tmp, fr, gues, h₁, h₂, h₃, h₄]
        rw [startEq, Store.set_set]
      change Executes (whilePositive goal scanBody) next .normal (scanEffect next result) at tail
      rw [finish] at tail
      simpa only [hGoal] using whilePositive_pos (by omega : s goal ≠ 0) (fresh.symm ▸ first) tail

end PalomarI3380.Compiler.Source
