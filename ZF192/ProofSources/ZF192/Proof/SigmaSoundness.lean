module
public import ZF192Support.SetTheory.Omega.Peano
public import ZF192.Proof.Nonhalting
public import ZF192.Tape.Halting.Sigma
public import ZF192.Tape.Halting.SetTheorySentence

@[expose] public section
namespace ZF192
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.SetTheory
open ZF192Support.OmegaInterpretation
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

/-- Explicit arithmetic Σ1-soundness of actual Foundation ZF through its
fixed natural-number interpretation. This is stronger than mere consistency. -/
def ArithmeticSigma1SoundZF : Prop :=
 ∀σ:𝚺ᴬ₁.Semisentence 0,
 (𝗭𝗙 : SetTheory) ⊢ arithmeticTranslation.translate σ.val → σ.val.Evalb (![]:Fin 0→Nat)
theorem ArithmeticSigma1SoundZF.consistent (hs:ArithmeticSigma1SoundZF) :
 FFL.Entailment.Consistent (𝗭𝗙 : SetTheory) := by
 let bot:𝚺ᴬ₁.Semisentence 0:=.mkSigma ⊥
 apply FFL.Entailment.consistent_iff_exists_unprovable.mpr
 refine ⟨arithmeticTranslation.translate bot.val,?_⟩
 intro hp
 have hf:=hs bot hp
 simpa [bot] using hf
def literal192SigmaSentence : SetTheorySentence :=
 arithmeticTranslation.translate BinaryTape.physicalHaltSigma.val
/-- The halting-unprovability direction for the original table. Soundness is
explicit, and this does not claim the nonhalting-unprovability direction. -/
theorem literal192_sigma_unprovable
 (hs:ArithmeticSigma1SoundZF) :
 ¬ (𝗭𝗙 : SetTheory) ⊢ literal192SigmaSentence := by
 let :=hs.consistent
 intro hp
 have ht:=hs BinaryTape.physicalHaltSigma hp
 have hh:=BinaryTape.physicalHaltSigma_eval.mp ht
 exact literal192_nonhalting_of_foundation_consistent (BinaryTape.physicalHalts_nat_iff.mp hh)
theorem literal192_physical_to_sigma :
 (𝗭𝗙 : SetTheory) ⊢ literal192PhysicalSentence 🡒 literal192SigmaSentence := by
 apply SetTheory.complete.{0}
 intro V _ _ _
 simp only [models_iff,LogicalConnective.HomClass.map_imply]
 change (V↓[Language.set] ⊧ literal192PhysicalSentence) →
  (V↓[Language.set] ⊧ literal192SigmaSentence)
 intro hh
 have h1:=DirectTranslation.Model.translate_iff (π:=arithmeticTranslation) (M:=V)
  (σ:=BinaryTape.physicalHaltSentence)
 have h2:=DirectTranslation.Model.translate_iff (π:=arithmeticTranslation) (M:=V)
  (σ:=BinaryTape.physicalHaltSigma.val)
 rw [interpreted_structure_eq_standard (V:=V)] at h1 h2
 apply h2.mpr
 have he:=h1.mp hh
 rw [models_iff] at he ⊢
 exact BinaryTape.physicalHaltSigma_eval.mpr (BinaryTape.physicalHaltSentence_eval.mp he)
theorem literal192_physical_unprovable (hs:ArithmeticSigma1SoundZF) :
 ¬ (𝗭𝗙 : SetTheory) ⊢ literal192PhysicalSentence := by
 intro hp
 exact literal192_sigma_unprovable hs (literal192_physical_to_sigma ⨀ hp)
end ZF192
