module
public import I3_334.Literal
public import I3_334Support.Logic.Target
public import I3_334Support.Machine.Simulation
@[expose] public section

namespace PalomarI3334

open PalomarI3380 (HaltsFrom blank)
open PalomarI3380.Logic

namespace Internal

open PalomarI3380.Logic.Internal

variable {V : Type} (E : V → V → Prop)

def LiteralStep (s t : Configuration V) : Prop :=
  ∃ q : Fin 334, Numeral E q.val s.state ∧ ∃ read : Bool,
    let row := literal[2 * q.val + (if read then 1 else 0)]?.getD 0
    Move E read (row / 2 % 2 == 1) (row % 2 == 1) (row / 4) s t

/-- An internal finite history of the exact 334-state machine. Its length
and entries may be nonstandard in a model of ZFC + I3. -/
def Halts : Prop :=
  ∃ n domain history zero start finish,
    NatObject E n ∧ Succ E n domain ∧ FunctionOn E history domain ∧ Empty E zero ∧
      ConfigurationCode E ⟨zero, zero, zero⟩ start ∧ At E history zero start ∧
      At E history n finish ∧
      (∃ final, ConfigurationCode E final finish ∧ Numeral E 334 final.state) ∧
      ∀ i, E i n → ∃ next s t before after, Succ E i next ∧
        At E history i before ∧ At E history next after ∧
        ConfigurationCode E s before ∧ ConfigurationCode E t after ∧ LiteralStep E s t

end Internal

/-- A closed set-theoretic sentence for halting of the 334-state machine. -/
def RepresentsHalting (H : Formula) : Prop :=
  Closed H ∧ ∀ (V : Type) (E : V → V → Prop), Nonempty V → ZFCI3Model E →
    ∀ env : Nat → V, eval E H env ↔ Internal.Halts E

/-- Conditional independence for the literal 334-state machine on a blank tape. -/
def ExactClaim : Prop :=
  ∃ H : Formula, RepresentsHalting H ∧
    (ZFCI3Consistent → ¬ HaltsFrom machine blank ∧ ¬ ZFCI3Provable (Neg H)) ∧
    (ArithmeticSigma1Sound → ¬ ZFCI3Provable H ∧ ¬ ZFCI3Provable (Neg H))

end PalomarI3334
