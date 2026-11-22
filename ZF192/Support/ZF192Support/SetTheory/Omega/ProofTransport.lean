module
public import ZF192Support.SetTheory.Omega.Peano
@[expose] public section
namespace ZF192Support.OmegaInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open scoped FFL.FirstOrder.Arithmetic
/-- Genuine theorem transport into actual Foundation ZF, using a completely
specified interpretation. This is not an arithmetic-internal proof-code map. -/
theorem pa_proof_to_zf {σ : ArithmeticSentence} (h : 𝗣𝗔 ⊢ σ) :
 (𝗭𝗙 : SetTheory) ⊢ arithmeticTranslation.translate σ := by
 apply SetTheory.complete.{0}
 intro V _ _ _
 have ht := DirectTranslation.Model.translate_iff (π := arithmeticTranslation) (M := V) (σ := σ)
 rw [interpreted_structure_eq_standard (V := V)] at ht
 apply ht.mpr
 exact models_of_provable (omega_models_peano (V := V)) h
end ZF192Support.OmegaInterpretation
