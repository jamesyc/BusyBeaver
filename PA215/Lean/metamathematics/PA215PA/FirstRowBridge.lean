import PA215PA.TraceCoding
import PA215PA.NatTape

/-! Links the first object-arithmetic transition formula to the exact machine.
This is a one-row bridge, not the full arithmetized trace theorem. -/
namespace PA215.PA

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

/-- Every stack instance of the arithmetic first-row relation is an actual
transition of the exact table. The starting control is the blank-start state,
but the stack codes are arbitrary. -/
theorem firstRow_step {left right left' right' : Nat}
    (h : firstRow 0 left right 1 left' right') :
    NatTape.step ⟨start, left, right⟩ =
      some ⟨target 1, left', right'⟩ := by
  rcases h with ⟨_, tail, hr, _, hl, ht⟩
  subst right
  subst left'
  subst right'
  have hrow : row ⟨0, by decide⟩ false = ⟨true, true, target 1⟩ := by decide
  have heven : ((1 + 1) * tail).testBit 0 = false := by
    simp [Nat.testBit_zero, Nat.mul_comm]
  have hstart : start = some ⟨0, by decide⟩ := rfl
  simp only [NatTape.step, hstart, heven, Option.map_some, hrow]
  simp [NatTape.advance, NatTape.push, Nat.mul_comm]

/-- Standard-model satisfaction of the six-place PA formula entails the exact
machine transition, not just an unrelated arithmetic calculation. -/
theorem firstRowFormula_step {left right left' right' : Nat}
    (h : Nat ⊧/![0, left, right, 1, left', right'] firstRowFormula) :
    NatTape.step ⟨start, left, right⟩ =
      some ⟨target 1, left', right'⟩ :=
  firstRow_step ((firstRowFormula_correct _ _ _ _ _ _).mp h)

#print axioms firstRow_step
#print axioms firstRowFormula_step
end PA215.PA
