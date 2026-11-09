module

/- Exact211: fresh physical interpretation of the unchanged original coded source. -/
public import User211EndpointStartupSourceBinding
public import PA215PA.Theory
public import User211EndpointInternalStartupTrace
public import User211EndpointInternalFixedFile

@[expose] public section
namespace PA211.UserCandidate.PA.InternalTrace.FixedTrace
open PA215 PA215.PA
open PA213.PA.InternalTrace.CodedSource
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open CodedSource

def startupRegisters : List Nat := [0,0,6,0,0,0,0,7,0]
noncomputable def entryState {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory] : V :=
  stateCode 69 (fixedFile startupRegisters)

def startupFrameSentence : ArithmeticSentence :=
  “∃ file regs c, !(fixedFileGraph Startup.startupFile) file ∧
    !(fixedFileGraph startupRegisters) regs ∧ !adjoinDef c 69 regs ∧
    !frameGraph c 0 file 81 1 ↑(Startup.finalConfig.right)”

lemma startupFrame_sigma : ℬ[<,ℒₒᵣ].Hierarchy 𝚺 1 startupFrameSentence := by
  simp [startupFrameSentence]

/-- The full startup file is retained, including nonzero spare11. The logical
state is the actual intermediate AX ordinal68, not the clean seed ordinal25. -/
lemma startup_refines_nat : Refines (entryState (V := Nat)) 0 (fixedFile Startup.startupFile)
    ⟨81,1,Startup.finalConfig.right⟩ := by
  have he := frame_nat Startup.startupPath 0 Startup.startupFile
  change PhysicalFrame.frame Startup.startupPath 0 (fixedFile Startup.startupFile)=
    let c := ZipNatTape.encode Startup.nativeFrame
    ({ q := StepFormula.controlCode c.control, left := c.left, right := c.right } : Symbolic.ModelConf Nat) at he
  rw [Startup.encode_nativeFrame] at he
  change PhysicalFrame.frame Startup.startupPath 0 (fixedFile Startup.startupFile)=
    (⟨81,1,Startup.finalConfig.right⟩ : Symbolic.ModelConf Nat) at he
  refine ⟨?_,?_,?_,?_⟩
  · simp [entryState,ValidStore,fixedFile_length,startupRegisters]
  · rw [fixedFile_length,Startup.full_file_length]
    simp only [natCast_nat]
    exact Or.inr (by decide)
  · funext r
    simp only [entryState,store_state,registers,PhysicalRegisters.readFile]
    have h1 := fixedFile_nth (V := Nat) startupRegisters r.val
    have h2 := fixedFile_nth (V := Nat) Startup.startupFile (Source.physicalRegister r)
    simp only [natCast_nat] at h1 h2
    simp only [natCast_nat]
    rw [h1,h2]
    exact (congrFun Startup.logical_projection r).symm
  · simp only [entryState,control_state]
    change Frames frameEntries 69 0 (fixedFile Startup.startupFile) ⟨81,1,Startup.finalConfig.right⟩
    rw [←he]
    exact frames_at 68 _ Startup.source_site68 0 (fixedFile Startup.startupFile)

lemma startupFrame_nat : Nat↓[ℒₒᵣ] ⊧ startupFrameSentence := by
  simp [startupFrameSentence,models_iff,fixedFile_correct,adjoin_defined.df,frame_correct,
    numeral_eq_natCast,natCast_nat]
  convert startup_refines_nat using 1 <;> simp [entryState,stateCode,natCast_nat]

theorem pa_proves_startup_frame : theory ⊢ startupFrameSentence :=
  Arithmetic.sigma_one_completeness startupFrame_sigma startupFrame_nat

theorem startup_refines_all_models {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory] :
    Refines (entryState (V := V)) 0 (fixedFile Startup.startupFile)
      ⟨81,1,(Startup.finalConfig.right : V)⟩ := by
  have h := consequence_iff.mp (Theory.Proof.sound pa_proves_startup_frame) V inferInstance
  simpa [startupFrameSentence,models_iff,fixedFile_correct,adjoin_defined.df,frame_correct,
    numeral_eq_natCast,Nat.cast_ofNat,entryState,stateCode] using h
#print axioms startup_refines_nat
#print axioms pa_proves_startup_frame
#print axioms startup_refines_all_models
end PA211.UserCandidate.PA.InternalTrace.FixedTrace

