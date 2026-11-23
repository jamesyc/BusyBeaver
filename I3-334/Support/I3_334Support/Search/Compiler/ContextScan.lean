module
public import I3_334Support.Search.WordCompare
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

end PalomarI3380.Compiler.Source
