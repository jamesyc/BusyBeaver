module
public import Independence.Godel
public import ConcreteChallengeFoundation
public import ConcreteChallengePhysical
public import Literal209SigmaSoundness
public import ConcreteChallengeSentenceTransport
public import Independence.SigmaBridge
@[expose] public section
/-! # The compared claim from a calibrated arithmetic theory

The halting sentence and its meaning in every ZF model are unchanged. The
nonhalting direction comes from `neg_unprovable_of_calibration`. The halting
direction uses Σ1 soundness, converted from the Challenge's form by
`SigmaBridge.standalone_sound_implies_production`. -/
namespace ZF209.Independence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.SetTheory FFL.Entailment
open ZF209.OmegaInterpretation

/-- The closed source sentence for blank-tape halting of the literal machine. -/
def haltSentence : PalomarZF209.Formula := PalomarZF209.ofFoundationSentence literal209PhysicalSentence

/-- Its meaning in every ZF model is the model-internal halting history. -/
theorem haltSentence_represents : PalomarZF209.Represents209 haltSentence := by
  refine ⟨PalomarZF209.ofFoundationSentence_closed _, ?_⟩
  intro V E hn hm s
  let _ : Nonempty V := hn
  let _ : SetStructure V := ⟨fun y x => E x y⟩
  let _ : V↓[Language.set] ⊧* 𝗭𝗙 := PalomarZF209.challenge_model_to_foundation hm
  let A := arithmeticTranslation.Model V
  have ht := DirectTranslation.Model.translate_iff (π := arithmeticTranslation) (M := V)
    (σ := ZF209.BinaryTape.physicalHaltSentence)
  rw [interpreted_structure_eq_standard (V := V)] at ht
  have hphys : (A↓[ℒₒᵣ] ⊧ ZF209.BinaryTape.physicalHaltSentence) ↔
      ZF209.BinaryTape.physicalHalts (M := A) := by
    simpa only [models_iff] using (ZF209.BinaryTape.physicalHaltSentence_eval (M := A))
  exact (PalomarZF209.ofFoundationSentence_eval literal209PhysicalSentence s).trans
    (ht.trans (hphys.trans (PalomarZF209History.internalLinkedHalts_iff (V := V)).symm))

/-- The compared claim, given a calibrated arithmetic theory. -/
theorem exact209Claim_of_calibration {T : ArithmeticTheory} [T.Δ₁]
    (hT : Calibration T literal209PhysicalSentence) : PalomarZF209.Exact209Claim := by
  have sigma : PalomarZF209.ArithmeticSigma1Sound → ArithmeticSigma1SoundZF :=
    SigmaBridge.standalone_sound_implies_production
  refine ⟨haltSentence, haltSentence_represents, fun hc hp => ?_, fun hs => ⟨fun hp => ?_, fun hp => ?_⟩⟩
  · have := PalomarZF209.consistent_iff_foundation.mp hc
    exact neg_unprovable_of_calibration hT
      ((PalomarZF209.provable_neg_ofFoundationSentence_iff literal209PhysicalSentence).mp hp)
  · exact literal209_physical_unprovable (sigma hs)
      ((PalomarZF209.provable_ofFoundationSentence_iff literal209PhysicalSentence).mp hp)
  · have := (sigma hs).consistent
    exact neg_unprovable_of_calibration hT
      ((PalomarZF209.provable_neg_ofFoundationSentence_iff literal209PhysicalSentence).mp hp)

end ZF209.Independence
