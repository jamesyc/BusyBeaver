module
public import ZF192.Palomar.Physical
public import ZF192.Tape.Halting.SetTheorySentence
public import ZF192.Statement
public import ZF192Support.SetTheory.Omega.ModelStructure
public import ZF192Support.Palomar.SentenceTransport

@[expose] public section
namespace ZF192
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.SetTheory
open ZF192Support.OmegaInterpretation

/-- The closed source sentence for blank-tape halting of the literal machine. -/
def haltSentence : PalomarZF192Theory.Formula := PalomarZF192Theory.ofFoundationSentence literal192PhysicalSentence

/-- Its meaning in every ZF model is the model-internal halting history. -/
theorem haltSentence_represents : PalomarZF192.Represents192 haltSentence := by
  refine ⟨PalomarZF192Theory.ofFoundationSentence_closed _, ?_⟩
  intro V E hn hm s
  let _ : Nonempty V := hn
  let _ : SetStructure V := ⟨fun y x => E x y⟩
  let _ : V↓[Language.set] ⊧* 𝗭𝗙 := PalomarZF192Theory.challenge_model_to_foundation hm
  let A := arithmeticTranslation.Model V
  have ht := DirectTranslation.Model.translate_iff (π := arithmeticTranslation) (M := V)
    (σ := ZF192.BinaryTape.physicalHaltSentence)
  rw [interpreted_structure_eq_standard (V := V)] at ht
  have hphys : (A↓[ℒₒᵣ] ⊧ ZF192.BinaryTape.physicalHaltSentence) ↔
      ZF192.BinaryTape.physicalHalts (M := A) := by
    simpa only [models_iff] using (ZF192.BinaryTape.physicalHaltSentence_eval (M := A))
  exact (PalomarZF192Theory.ofFoundationSentence_eval literal192PhysicalSentence s).trans
    (ht.trans (hphys.trans (PalomarZF192History.internalLinkedHalts_iff (V := V)).symm))

end ZF192
