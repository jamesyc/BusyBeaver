module
public import ConcreteArithmeticTranslation
public import ExplicitZfrProvabilityFormula
@[expose] public section
namespace ZF207.OmegaInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open scoped FFL.FirstOrder.Arithmetic
/-- Translating the closed refutation sentence preserves its exact syntax. -/
def sourceRefutationInZF : SetTheorySentence :=
 arithmeticTranslation.translate
   (ZFR.ArithmeticRepresentation.explicitZfrProvabilityFormula.val/[‘0’])
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
theorem sourceRefutation_translation_exact :
 V↓[ℒₛₑₜ] ⊧ sourceRefutationInZF ↔
 (arithmeticTranslation.Model V)↓[ℒₒᵣ] ⊧
   (ZFR.ArithmeticRepresentation.explicitZfrProvabilityFormula.val/[‘0’]) :=
 DirectTranslation.Model.translate_iff (π := arithmeticTranslation)
end ZF207.OmegaInterpretation
