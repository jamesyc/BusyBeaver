module
public import I0451.Standalone.ModelBridge
public import I0451.Standalone.SigmaBridge
public import I0451.IndependenceStatement

/-! The stand-alone result uses ordinary membership models and the
model-theoretic presentation of first-order provability. -/
@[expose] public section
namespace I0451.Standalone

open I0451.Logic (NamedFormula)

/-- The first-order Berkeley cardinal axiom, with set-coded elementarity. -/
def berkeleyAxiom : NamedFormula :=
  ofFoundationSentence I0451.Logic.SetAssignments.berkeleySetAxiom

/-- I₀ expressed using the proper ultrapower of L(V_{λ+1}).
Its elementary map has critical point below λ and its restriction
to V_λ belongs to L(V_{λ+1}). Both target theories use this sentence. -/
def i0Axiom : NamedFormula :=
  ofFoundationSentence I0451.Logic.i0SetAxiom

/-- Consistency of the specified Craig presentation of the arithmetic
consequences of ZFC + I₀, read in the membership model's natural numbers. -/
noncomputable def targetConsistency : NamedFormula :=
  ofFoundationSentence (ZF207.OmegaInterpretation.arithmeticTranslation.translate I0451.i0Consistency)

/-- The Σ₁ assertion that there is a finite blank-tape run of the literal
machine stopping at a configuration with no outgoing transition. -/
def haltingArithmetic : SigmaFormula :=
  SigmaBridge.formula I0451.arithmeticHalting.val

inductive Theory where
  | berkeley
  | zfcI0
  | zfI0

/-- A membership model satisfies the corresponding theory's additional axioms. -/
abbrev Models {V : Type} (T : Theory) (E : V → V → Prop) : Prop :=
  Model E ∧ Theory.casesOn T
    (∀ s, eval E s berkeleyAxiom)
    (Choice E ∧ ∀ s, eval E s i0Axiom)
    (∀ s, eval E s i0Axiom)

/-- Validity in all membership models. For these theories this is equivalent
to first-order provability, by completeness with the equality axioms. -/
abbrev Provable (T : Theory) (p : NamedFormula) : Prop :=
  ∀ (V : Type) (E : V → V → Prop), Nonempty V → Models T E → ∀ s, eval E s p

/-- Correct interpretation of a closed arithmetic assertion in every
ZF model, including models whose natural numbers are nonstandard. -/
def RepresentsArithmetic (p : SigmaFormula) (φ : NamedFormula) : Prop :=
  p.bound 0 ∧ φ.freeLabels = [] ∧
    ∀ (V : Type) (E : V → V → Prop), Nonempty V → Model E →
      ∀ s env : Nat → V, (∀ i, NatObject E (env i)) →
        (eval E s φ ↔ p.internalEval E env)

/-- Every provable Σ₁ arithmetic sentence is true in the standard naturals. -/
abbrev SigmaOneSound (T : Theory) : Prop :=
  ∀ (p : SigmaFormula) (φ : NamedFormula), RepresentsArithmetic p φ →
    Provable T φ → ∀ s : Nat → Nat, p.natEval s

/-- Conditional independence for the exact literal transition table.
The relative consistency premise is a Berkeley-theory proof for the
particular presentation used by `targetConsistency`. -/
abbrev Claim451 : Prop :=
  (∀ s : Nat → Nat, haltingArithmetic.natEval s ↔ I0451.Halts I0451.literal (I0451.blank 0)) ∧
    ∃ h : NamedFormula, RepresentsArithmetic haltingArithmetic h ∧
      ((¬ Provable .berkeley .falsity) → SigmaOneSound .zfcI0 → Provable .berkeley targetConsistency →
        (¬ I0451.Halts I0451.literal (I0451.blank 0)) ∧
          ((¬ Provable .zfcI0 h) ∧ (¬ Provable .zfcI0 (.imp h .falsity))) ∧
          ((¬ Provable .zfI0 h) ∧ (¬ Provable .zfI0 (.imp h .falsity))))

end I0451.Standalone
