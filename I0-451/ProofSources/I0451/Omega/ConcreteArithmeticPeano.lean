module
public import I0451.Omega.ConcreteArithmeticPeanoMinus
public import I0451.Omega.ConcreteArithmeticInduction
@[expose] public section
namespace ZF207.OmegaInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "A" => arithmeticTranslation.Model V
instance omega_models_peano : A↓[ℒₒᵣ] ⊧* 𝗣𝗔 := by
 apply models_theory_iff.mpr
 intro φ hφ
 rcases hφ with h|h
 · exact models_theory_iff.mp (omega_models_peanoMinus (V := V)) φ h
 · exact models_theory_iff.mp (models_arithmetic_induction (V := V)) φ h
end ZF207.OmegaInterpretation
