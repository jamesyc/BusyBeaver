module
public import I3_380.Search.Compiler.TokenComparison
@[expose] public section

namespace PalomarI3380.Compiler.Source

/-- The loop consumes exactly the requested number of field pairs. It
continues to consume both streams after a mismatch. -/
def prefixSummary : Nat → Nat → Nat → Bool × (Nat × Nat)
  | 0, front, back => (true, front, back)
  | n + 1, front, back =>
    let a := rawFields front
    let b := rawFields back
    let remaining := prefixSummary n a.rest b.rest
    ((a.arityField == b.arityField) && (a.tag == b.tag) && remaining.1, remaining.2)

theorem prefixSummary_correct (n front back : Nat) :
    comparePrefix n front back =
      let result := prefixSummary n front back
      if result.1 then some result.2 else none := by
  induction n generalizing front back with
  | zero => rfl
  | succ n ih =>
    simp only [comparePrefix, prefixSummary, Bool.and_eq_true, beq_iff_eq]
    by_cases same : (rawFields front).arityField = (rawFields back).arityField ∧
        (rawFields front).tag = (rawFields back).tag
    · simp only [same, true_and, ↓reduceIte]
      exact ih _ _
    · simp only [same, false_and, ↓reduceIte]

private theorem two_fields (s : Store) (e : s exp = 0) (t : s tok = 0) (a : s u = 0) :
    let x := rawFields (s fr)
    let y := rawFields (s lv)
    Executes (.seq contextField contextField) s .normal
      (((s.set fr x.rest).set lv y.rest).set gues
        (mark s (x.arityField = y.arityField ∧ x.tag = y.tag))) := by
  dsimp only
  let front := Cantor.unpair (s fr)
  let back := Cantor.unpair (s lv)
  let mid := contextFieldEffect s
  have h₁ : Executes contextField s .normal mid := run_contextField s e t a
  have midE : mid exp = 0 := by simpa [mid, contextFieldEffect, Store.set, exp, lv, fr, gues] using e
  have midT : mid tok = 0 := by simpa [mid, contextFieldEffect, Store.set, tok, lv, fr, gues] using t
  have midA : mid u = 0 := by simpa [mid, contextFieldEffect, Store.set, u, lv, fr, gues] using a
  have h₂ := run_contextField mid midE midT midA
  have vFr : mid fr = front.2 := by simp [mid, contextFieldEffect, Store.set, front, fr, lv, gues]
  have vLv : mid lv = back.2 := by simp [mid, contextFieldEffect, Store.set, back, fr, lv, gues]
  have vGuess : mid gues = mark s (back.1 = front.1) := Store.get_set _ _ _
  have out : contextFieldEffect mid =
      (((s.set fr (rawFields (s fr)).rest).set lv (rawFields (s lv)).rest).set gues
        (mark s ((rawFields (s fr)).arityField = (rawFields (s lv)).arityField ∧
          (rawFields (s fr)).tag = (rawFields (s lv)).tag))) := by
    change ((mid.set lv (Cantor.unpair (mid lv)).2).set fr (Cantor.unpair (mid fr)).2).set gues
      (mark mid ((Cantor.unpair (mid lv)).1 = (Cantor.unpair (mid fr)).1)) = _
    rw [vFr, vLv]
    have guess : mark mid ((Cantor.unpair back.2).1 = (Cantor.unpair front.2).1) =
        mark s (front.1 = back.1 ∧ (Cantor.unpair front.2).1 = (Cantor.unpair back.2).1) := by
      simp only [mark, vGuess]
      by_cases head : front.1 = back.1 <;> by_cases tail : (Cantor.unpair front.2).1 = (Cantor.unpair back.2).1 <;>
        simp [head, tail, eq_comm]
    rw [guess]
    funext i
    by_cases hf : i = fr <;> by_cases hl : i = lv <;> by_cases hg : i = gues <;>
      simp_all [mid, contextFieldEffect, Store.set, rawFields, front, back, fr, lv, gues] <;> rfl
  rw [out] at h₂
  exact then_normal h₁ h₂

def prefixEffect (s : Store) (result : Bool × (Nat × Nat)) : Store :=
  (((s.set sel 0).set fr result.2.1).set lv result.2.2).set gues (mark s (result.1 = true))

theorem run_contextScan (s : Store) (e : s exp = 0) (t : s tok = 0) (a : s u = 0) :
    Executes contextScan s .normal (prefixEffect s (prefixSummary (s sel) (s fr) (s lv))) := by
  generalize count : s sel = n
  induction n generalizing s with
  | zero =>
    have state : prefixEffect s (prefixSummary 0 (s fr) (s lv)) = s := by
      simp only [prefixEffect, prefixSummary, mark, ↓reduceIte]
      rw [← count, Store.set_same, Store.set_same, Store.set_same, Store.set_same]
    rw [state]
    exact whilePositive_zero count
  | succ n ih =>
    let start := s.set sel n
    let x := rawFields (s fr)
    let y := rawFields (s lv)
    let condition := x.arityField = y.arityField ∧ x.tag = y.tag
    let next := ((start.set fr x.rest).set lv y.rest).set gues
      (if condition then s gues else 0)
    have hStart : s.set sel (s sel - 1) = start := by simp [start, count]
    have eStart : start exp = 0 := by simpa [start, Store.set, exp, sel] using e
    have tStart : start tok = 0 := by simpa [start, Store.set, tok, sel] using t
    have aStart : start u = 0 := by simpa [start, Store.set, u, sel] using a
    have first := two_fields start eStart tStart aStart
    dsimp only at first
    have front : start fr = s fr := by simp [start, Store.set, fr, sel]
    have back : start lv = s lv := by simp [start, Store.set, lv, sel]
    have candidate : start gues = s gues := by simp [start, Store.set, gues, sel]
    simp only [front, back, mark, candidate] at first
    have hFirst : Executes (.seq contextField contextField) (s.set sel (s sel - 1)) .normal next := by
      rw [hStart]
      exact first
    have eNext : next exp = 0 :=
      by simpa [next, start, Store.set, exp, fr, lv, gues, sel] using e
    have tNext : next tok = 0 :=
      by simpa [next, start, Store.set, tok, fr, lv, gues, sel] using t
    have aNext : next u = 0 :=
      by simpa [next, start, Store.set, u, fr, lv, gues, sel] using a
    have nNext : next sel = n := by simp [next, start, Store.set, sel, fr, lv, gues]
    have tail := ih next eNext tNext aNext nNext
    have frNext : next fr = x.rest := by simp [next, Store.set, fr, lv, gues]
    have lvNext : next lv = y.rest := by simp [next, Store.set, lv, gues]
    rw [frNext, lvNext] at tail
    let remaining := prefixSummary n x.rest y.rest
    have result : prefixEffect next remaining = prefixEffect s (prefixSummary (n + 1) (s fr) (s lv)) := by
      have guessing : next gues = mark s condition := Store.get_set _ _ _
      have matchFlag :
          (prefixSummary (n + 1) (s fr) (s lv)).1 = true ↔ condition ∧ remaining.1 = true := by
        simp only [prefixSummary, Bool.and_eq_true, beq_iff_eq, condition, remaining, x, y]
      have marker :
          mark next (remaining.1 = true) =
            mark s ((prefixSummary (n + 1) (s fr) (s lv)).1 = true) := by
        simp only [mark, guessing, matchFlag]
        exact mark_compose s condition (remaining.1 = true)
      change (((next.set sel 0).set fr remaining.2.1).set lv remaining.2.2).set gues
        (mark next (remaining.1 = true)) = _
      rw [marker]
      change (((next.set sel 0).set fr remaining.2.1).set lv remaining.2.2).set gues _ =
        (((s.set sel 0).set fr remaining.2.1).set lv remaining.2.2).set gues _
      funext i
      by_cases h₁ : i = sel <;> by_cases h₂ : i = fr <;> by_cases h₃ : i = lv <;>
        by_cases h₄ : i = gues <;> simp_all [next, start, Store.set, sel, fr, lv, gues]
    rw [result] at tail
    exact whilePositive_pos (by omega) hFirst tail

end PalomarI3380.Compiler.Source
