module
public import Independence.Godel
public import ConcreteChallengeFoundation
public import ConcreteChallengePhysical
public import Literal207SigmaSoundness
public import ConcreteChallengeSentenceTransport
public import Independence.SigmaBridge
@[expose] public section
/-! # The compared claim from a calibrated arithmetic theory

The halting sentence and its meaning in every ZF model are unchanged. The
nonhalting direction comes from `neg_unprovable_of_calibration`. The halting
direction uses Σ1 soundness, converted from the Challenge's form by
`SigmaBridge.standalone_sound_implies_production`. -/
namespace ZF207.Independence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.SetTheory FFL.Entailment
open ZF207.OmegaInterpretation

/-- The closed source sentence for blank-tape halting of the literal machine. -/
def haltSentence : PalomarZF207.Formula := PalomarZF207.ofFoundationSentence literal207PhysicalSentence

/-- Its meaning in every ZF model is the model-internal halting history. -/
theorem haltSentence_represents : PalomarZF207.Represents207 haltSentence := by
  refine ⟨PalomarZF207.ofFoundationSentence_closed _, ?_⟩
  intro V E hn hm s
  let _ : Nonempty V := hn
  let _ : SetStructure V := ⟨fun y x => E x y⟩
  let _ : V↓[Language.set] ⊧* 𝗭𝗙 := PalomarZF207.challenge_model_to_foundation hm
  let A := arithmeticTranslation.Model V
  have ht := DirectTranslation.Model.translate_iff (π := arithmeticTranslation) (M := V)
    (σ := ZF207.BinaryTape.physicalHaltSentence)
  rw [interpreted_structure_eq_standard (V := V)] at ht
  have hphys : (A↓[ℒₒᵣ] ⊧ ZF207.BinaryTape.physicalHaltSentence) ↔
      ZF207.BinaryTape.physicalHalts (M := A) := by
    simpa only [models_iff] using (ZF207.BinaryTape.physicalHaltSentence_eval (M := A))
  exact (PalomarZF207.ofFoundationSentence_eval literal207PhysicalSentence s).trans
    (ht.trans (hphys.trans (PalomarZF207History.internalLinkedHalts_iff (V := V)).symm))

/-- The compared claim, given a calibrated arithmetic theory. -/
theorem exact207Claim_of_calibration {T : ArithmeticTheory} [T.Δ₁]
    (hT : Calibration T literal207PhysicalSentence) : PalomarZF207.Exact207Claim := by
  have sigma : PalomarZF207.ArithmeticSigma1Sound → ArithmeticSigma1SoundZF :=
    SigmaBridge.standalone_sound_implies_production
  refine ⟨haltSentence, haltSentence_represents, fun hc hp => ?_, fun hs => ⟨fun hp => ?_, fun hp => ?_⟩⟩
  · have := PalomarZF207.consistent_iff_foundation.mp hc
    exact neg_unprovable_of_calibration hT
      ((PalomarZF207.provable_neg_ofFoundationSentence_iff literal207PhysicalSentence).mp hp)
  · exact literal207_physical_unprovable (sigma hs)
      ((PalomarZF207.provable_ofFoundationSentence_iff literal207PhysicalSentence).mp hp)
  · have := (sigma hs).consistent
    exact neg_unprovable_of_calibration hT
      ((PalomarZF207.provable_neg_ofFoundationSentence_iff literal207PhysicalSentence).mp hp)

end ZF207.Independence
