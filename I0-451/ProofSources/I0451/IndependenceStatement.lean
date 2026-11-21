module
public import I0451.Logic.EffectiveTheories
public import I0451.Sentence

/-! The statement of the conditional independence result and its fixed
arithmetical consistency premise. -/
@[expose] public section
namespace I0451

open FFL FFL.Entailment FFL.FirstOrder FFL.FirstOrder.SetTheory FFL.FirstOrder.Arithmetic
open I0451.Logic I0451.Omega ZF207.OmegaInterpretation
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

/-- The target's fixed arithmetic proof presentation. -/
noncomputable def i0ArithmeticTheory : ArithmeticTheory :=
  (arithmeticConsequences zfcI0).craig

noncomputable instance : i0ArithmeticTheory.Δ₁ := inferInstanceAs ((arithmeticConsequences zfcI0).craig.Δ₁)

/-- The formal negation of provability of false in the target
presentation. The consistency transfer and Gödel II use this same sentence. -/
noncomputable def i0Consistency : ArithmeticSentence := i0ArithmeticTheory.standardProvability.con

/-- A B-proof of consistency for this exact Craig presentation.
The transport from the usual statement attributed to Woodin is an
additional obligation for deriving this premise. -/
def WoodinConsistency : Prop :=
  berkeleyTheory ⊢ arithmeticTranslation.translate i0Consistency

/-- Independence of the blank-tape halting assertion for the literal
451-state machine, in ZFC + I₀ and its choiceless subtheory. -/
def Independence451 : Prop :=
  Entailment.Consistent berkeleyTheory → ArithmeticSigmaOneSound zfcI0 → WoodinConsistency →
    ¬ Halts literal (blank 0) ∧
      ((zfcI0 ⊬ setHalting) ∧ (zfcI0 ⊬ ∼setHalting)) ∧
      ((zfI0 ⊬ setHalting) ∧ (zfI0 ⊬ ∼setHalting))

end I0451
