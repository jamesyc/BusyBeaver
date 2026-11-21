module
public import I0451.Arithmetization
public import I0451.Tables
public import I0451.Omega.ConcreteArithmeticProofTransport

/-! The arithmetic halting sentence and its interpretation in the
natural numbers of an arbitrary set-theory model. -/
@[expose] public section
namespace I0451

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.SetTheory
open scoped FFL.FirstOrder.Arithmetic
open ZF207.OmegaInterpretation

abbrev arithmeticHalting := Arithmetization.haltsDef literal

def setHalting : SetTheorySentence := arithmeticTranslation.translate arithmeticHalting.val

theorem arithmetic_halts_exact :
    ℕ↓[ℒₒᵣ] ⊧ arithmeticHalting.val ↔ Halts literal (blank 0) :=
  Arithmetization.haltsDef_nat literal

theorem set_halts_exact {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] :
    V↓[ℒₛₑₜ] ⊧ setHalting ↔
      (arithmeticTranslation.Model V)↓[ℒₒᵣ] ⊧ arithmeticHalting.val := by
  unfold setHalting
  have interpretation := DirectTranslation.Model.translate_iff (π := arithmeticTranslation)
    (M := V) (σ := arithmeticHalting.val)
  rw [interpreted_structure_eq_standard (V := V)] at interpretation
  exact interpretation

/-- For every arithmetical Σ₁ sentence, a proof of its omega-translation
in the theory implies truth in the standard natural numbers. -/
def ArithmeticSigmaOneSound (T : SetTheory) : Prop :=
  ∀ σ : 𝚺ᴬ₁.Sentence, T ⊢ arithmeticTranslation.translate σ.val → ℕ↓[ℒₒᵣ] ⊧ σ.val

theorem halting_unprovable {T : SetTheory} (sound : ArithmeticSigmaOneSound T)
    (nonhalting : ¬ Halts literal (blank 0)) : T ⊬ setHalting := by
  intro proof
  exact nonhalting (arithmetic_halts_exact.mp (sound arithmeticHalting proof))

end I0451
