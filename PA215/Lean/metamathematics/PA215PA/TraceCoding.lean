import PA215PA.Theory

/-! Arithmetic coding of the first machine transition.

Two natural-number stacks encode the tape relative to the head. The low bit
of the left stack is the nearest cell to the left. The low bit of the right
stack is the current cell. On row (0, 0) the machine writes one, moves right,
and enters state one. StepSemantics interprets the full transition relation,
and TraceAdequacy relates finite arithmetic traces to machine runs. -/

namespace PA215.PA

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

/-- Arithmetic meaning of the exact first row, on natural-number codes. -/
def firstRow (q left right q' left' right' : Nat) : Prop :=
  q = 0 ∧ ∃ tail, right = (1 + 1) * tail ∧ q' = 1 ∧
    left' = (1 + 1) * left + 1 ∧ right' = tail

theorem firstRow_blank : firstRow 0 0 0 1 1 0 := by
  exact ⟨rfl, 0, rfl, rfl, rfl, rfl⟩

/-- The same six-argument relation in the object language of PA. -/
def firstRowFormula : ArithmeticSemisentence 6 :=
  “a b c d e f. a = 0 ∧ ∃ t, c = (1 + 1) * t ∧ d = 1 ∧
    e = (1 + 1) * b + 1 ∧ f = t”

/-- The syntactic formula really represents the stated arithmetic relation. -/
theorem firstRowFormula_correct (q left right q' left' right' : Nat) :
    (Nat ⊧/![q, left, right, q', left', right'] firstRowFormula) ↔
      firstRow q left right q' left' right' := by
  simp [firstRowFormula, firstRow]

/-- The actual blank-start transition, expressed as a closed PA sentence. -/
def firstRowBlankSentence : ArithmeticSentence :=
  “!firstRowFormula 0 0 0 1 1 0”

/-- The right-move calculation uniformly quantified over arbitrary stack
codes, including nonstandard codes in an arbitrary PA model. -/
def firstRowTotalSentence : ArithmeticSentence :=
  “∀ b t, !firstRowFormula 0 b ((1 + 1) * t) 1 ((1 + 1) * b + 1) t”

theorem pa_proves_firstRow_total : theory ⊢ firstRowTotalSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [firstRowTotalSentence, firstRowFormula, models_iff]
  intro left tail
  exact ⟨rfl, tail, rfl, rfl, rfl, rfl⟩

/-- PA proves this transition. Completeness is applied to **every PA model**,
not merely to the standard natural-number model. -/
theorem pa_proves_firstRow_blank : theory ⊢ firstRowBlankSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [firstRowBlankSentence, models_iff, Semiformula.eval_substs]
  simp [firstRowFormula]

#print axioms firstRow_blank
#print axioms firstRowFormula_correct
#print axioms pa_proves_firstRow_blank
#print axioms pa_proves_firstRow_total

end PA215.PA
