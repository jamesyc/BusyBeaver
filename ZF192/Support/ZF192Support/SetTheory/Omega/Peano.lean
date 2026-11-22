module
public import ZF192Support.SetTheory.Omega.PeanoMinus
public import ZF192Support.SetTheory.Omega.Induction
@[expose] public section
namespace ZF192Support.OmegaInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "A" => arithmeticTranslation.Model V
instance omega_models_peano : A↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
 Semantics.ModelsSet.union_iff.mpr
   ⟨omega_models_peanoMinus (V := V), models_arithmetic_induction (V := V)⟩
end ZF192Support.OmegaInterpretation
