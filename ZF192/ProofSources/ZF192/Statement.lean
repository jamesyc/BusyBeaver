module
public import ZF192Support.Machine.BinaryTape
public import ZF192Support.Palomar.Definitions.Statement
public import ZF192.Palomar.HistoryDefinition
@[expose] public section

namespace PalomarZF192
open PalomarZF192Theory

/-- The standalone transition table, read as a two-sided binary machine. -/
def machine : BinaryTape.TMN := fun q read =>
  let rows := PalomarZF192History.literalRows.getD q (none, none)
  if read then rows.2 else rows.1

/-- The sentence means blank-tape halting of the exact table in every ZF model. -/
def Represents192 (H : Formula) : Prop :=
  Closed H ∧ ∀ (V : Type) (E : V → V → Prop), Nonempty V → Model E →
  ∀ s : Nat → V, eval E H s ↔ PalomarZF192History.InternalLinkedHalts E

/-- Conditional independence of the exact machine's blank-tape halting. -/
def Exact192Claim : Prop := ∃ H : Formula, Represents192 H ∧
  (Consistent → ¬ Provable (Neg H)) ∧
  (ArithmeticSigma1Sound → (¬ Provable H) ∧ (¬ Provable (Neg H)))

end PalomarZF192
