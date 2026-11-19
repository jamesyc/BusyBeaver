module
public import Foundation.FirstOrder.Incompleteness.StandardProvability
public import ConcreteArithmeticTranslation
@[expose] public section
/-! # Second incompleteness for ZF through a calibrated arithmetic theory

Foundation proves Gödel's second incompleteness theorem for arithmetic theories.
ZF's language has no numeral terms, so the argument for ZF goes through an
arithmetic theory `T`:

* `T` extends `𝗜𝚺₁` and has a Δ₁ axiom set;
* `T` is consistent if ZF is;
* ZF proves that `¬φ` implies `T`'s consistency read in ω (equivalently, a
  `T`-refutation read in ω implies `φ`);
* every arithmetic sentence that ZF proves in ω is a theorem of `T`.

Then a consistent ZF does not refute `φ`: otherwise ZF proves `T`'s consistency in
ω, and `T` proves its own consistency. -/
namespace ZF207.Independence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.SetTheory FFL.Entailment
open ZF207.OmegaInterpretation

/-- The calibration premises for an arithmetic theory `T` and a sentence `φ`. -/
structure Calibration (T : ArithmeticTheory) [T.Δ₁] (φ : SetTheorySentence) : Prop where
  base : 𝗜𝚺₁ ⪯ T
  consistent : Consistent (𝗭𝗙 : SetTheory) → Consistent T
  internal : (𝗭𝗙 : SetTheory) ⊢ ∼φ 🡒 arithmeticTranslation.translate T.standardProvability.con
  absorb : ∀ ψ : ArithmeticSentence,
    (𝗭𝗙 : SetTheory) ⊢ arithmeticTranslation.translate ψ → T ⊢ ψ

/-- A consistent ZF does not refute a calibrated sentence. -/
theorem neg_unprovable_of_calibration {T : ArithmeticTheory} [T.Δ₁] {φ : SetTheorySentence}
    (hT : Calibration T φ) [hZF : Consistent (𝗭𝗙 : SetTheory)] :
    ¬ (𝗭𝗙 : SetTheory) ⊢ ∼φ := by
  intro h
  have : 𝗜𝚺₁ ⪯ T := hT.base
  have : Consistent T := hT.consistent hZF
  exact ProvabilityAbstraction.con_unprovable (𝔅 := T.standardProvability)
    (hT.absorb _ (hT.internal ⨀ h))

end ZF207.Independence
