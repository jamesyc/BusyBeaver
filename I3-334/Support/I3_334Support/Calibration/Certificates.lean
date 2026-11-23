module
public import I3_334Support.Calibration.GraphTranslation
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.D1
@[expose] public section

namespace PalomarI3380.Calibration

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ArithmeticInterpretation

/-- A certificate is a graph-theory proof of the translated sentence.
Craig padding keeps this witness bounded by the coded arithmetic axiom. -/
noncomputable def graphCertificateFormula : 𝚫ᴬ₁.Semisentence 2 :=
  .mkDelta
    (.mkSigma “source evidence. ∃ target, !translationGraph target source ∧
      !(proof graphTheory).sigma evidence target”)
    (.mkPi “source evidence. ∀ target, !translationGraph target source →
      !(proof graphTheory).pi evidence target”)

theorem graphCertificate_defined {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    𝚫ᴬ₁-Relation (fun source evidence : M => Proof graphTheory evidence (kax filterInterpretation source))
      via graphCertificateFormula := .mk <| by
  have check (out source : M) :
      translationGraph.val.Evalb ![out,source] ↔ out = kax filterInterpretation source :=
    (translation_defined (M := M)).iff
  have same (w t : M) : (proof graphTheory).pi.val.Evalb ![w,t] ↔ Proof graphTheory w t :=
    (Proof.defined (T := graphTheory) (V := M)).proper.iff' _ |>.trans Proof.defined.iff
  constructor <;> intro v <;> simp [graphCertificateFormula,check,same]

noncomputable def graphCertificates : Craig.CertificateCheck :=
  ⟨graphCertificateFormula,fun M _ _ => (graphCertificate_defined (M := M)).proper⟩

noncomputable def arithmeticTheory : ArithmeticTheory := Craig.paddedTheory graphCertificates

noncomputable instance : arithmeticTheory.Δ₁ := Craig.paddedTheory_delta1 graphCertificates

theorem admitted_certificate (φ : ArithmeticSentence) (evidence : Nat)
    (checked : Proof graphTheory evidence (⌜translatedSentence φ⌝ : Nat)) :
    arithmeticTheory ⊢ φ := by
  apply Craig.proves_of_certificate graphCertificates φ evidence
  change graphCertificateFormula.val.Evalb ![(⌜φ⌝ : Nat),evidence]
  apply (graphCertificate_defined (M := Nat)).df ![(⌜φ⌝ : Nat),evidence] |>.mpr
  simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,translatedSentence_quote] using checked

theorem arithmeticTheory_admits {φ : ArithmeticSentence} (translated : graphTheory ⊢ translatedSentence φ) :
    arithmeticTheory ⊢ φ := by
  obtain ⟨evidence,checked⟩ := provable_iff_provable.mpr translated
  exact admitted_certificate φ evidence checked

end PalomarI3380.Calibration
