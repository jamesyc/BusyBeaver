module
public import Std

namespace M192.FiniteChecks
open Lean

@[expose] public def block (predicate : Nat → Bool) (base count : Nat) : Bool :=
  (List.range' base count).all predicate

public theorem append_checks {predicate : Nat → Bool} {base left right : Nat}
    (first : block predicate base left = true)
    (second : block predicate (base + left) right = true) :
    block predicate base (left + right) = true := by
  simp only [block] at first second ⊢
  rw [← List.range'_append_1, List.all_append, first, second]
  rfl

public theorem of_block {predicate : Nat → Bool} {base count : Nat}
    (checked : block predicate base count = true) {i : Nat} (hi : i < count) :
    predicate (base + i) = true :=
  List.all_eq_true.mp checked _ (List.mem_range'.mpr ⟨i, hi, by simp⟩)


-- Supplying numeric bounds keeps elaboration from unfolding a checked block
-- to infer the length and starting index of a composition.
private meta def joinProofs (pred : Ident) (base left right : Nat) (first second : TSyntax `term) :
    MacroM (TSyntax `term) := do
  let start := Syntax.mkNumLit (toString base)
  let firstSize := Syntax.mkNumLit (toString left)
  let secondSize := Syntax.mkNumLit (toString right)
  `(term| append_checks (predicate := $pred) (base := $start) (left := $firstSize) (right := $secondSize) $first $second)

/-- Split a range into small kernel evaluations and join adjacent ranges.
The bound on each evaluation keeps the kernel stack and memory use predictable. -/
scoped macro "check_block" pred:ident base:num count:num : term => do
  let rec prove (base count : Nat) : MacroM (TSyntax `term) := do
    if count ≤ 32 then
      let start := Syntax.mkNumLit (toString base)
      let length := Syntax.mkNumLit (toString count)
      `(term| (by decide +kernel : block $pred $start $length = true))
    else
      let left := count / 2
      let first ← prove base left
      let second ← prove (base + left) (count - left)
      joinProofs pred base left (count - left) first second
  termination_by count
  decreasing_by all_goals omega
  prove base.getNat count.getNat

/-- Compose adjacent checked blocks while keeping the proof tree balanced. The numeric
arguments specify the regular block width and total size. -/
scoped macro "join_blocks" pred:ident width:num total:num "[" checks:term,+ "]" : term => do
  let checks := checks.getElems
  let width := width.getNat
  let total := total.getNat
  let rec join (offset count : Nat) : MacroM (TSyntax `term) := do
    if count ≤ 1 then
      return checks[offset]!
    else
      let left := count / 2
      let first ← join offset left
      let second ← join (offset + left) (count - left)
      let base := offset * width
      let remaining := min (count * width) (total - base)
      joinProofs pred base (left * width) (remaining - left * width) first second
  termination_by count
  decreasing_by all_goals omega
  join 0 checks.size

end M192.FiniteChecks
