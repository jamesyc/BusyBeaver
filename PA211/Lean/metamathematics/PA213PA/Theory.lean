import Foundation.FirstOrder.Arithmetic.Schemata

/-! The fixed first-order Peano arithmetic presentation. This small interface
does not import arithmetization or incompleteness, so elementary internal PA
proofs can be checked independently of that heavier dependency. -/

namespace PA213.PA

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

/-- Full induction over the language zero, one, addition, multiplication,
equality and order, with Foundation's ordered-semiring base axioms. -/
abbrev theory : ArithmeticTheory := Peano

/-- External syntactic consistency; no project axiom is introduced. -/
abbrev Consistent : Prop := FFL.Entailment.Consistent theory

end PA213.PA

