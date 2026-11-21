module
public import I3_380.Engine.Arithmetic.DecoderArms
public import I3_380.Arithmetic.PackedFields
public import I3_380.Engine.Arithmetic.TapeScans
public import I3_380.DecoderRefinement
@[expose] public section

namespace PalomarI3380.ArithmeticMachine

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def mappedState (d : DecoderComparison) (state : M) : M :=
  packedField d.stateMap 9 512 state

noncomputable def mappedCode (d : DecoderComparison) (code : M) : M :=
  encode (mappedState d (π₁ code)) (π₁ (π₂ code)) (π₂ (π₂ code))

noncomputable def entryMask (d : DecoderComparison) (state : M) : M :=
  packedField d.entryMasks 2 4 state

def allowedBit (d : DecoderComparison) (state bit : M) : Prop :=
  entryMask d state = 0 ∨ remIn (divIn (entryMask d state) (Exp.exp bit)) 2 = 1

def validReference (d : DecoderComparison) (code : M) : Prop :=
  π₁ code ≤ (d.reference.workingStates : M) ∧ allowedBit d (π₁ code) (remIn (π₁ (π₂ code)) 2)

theorem mappedState_cast (d : DecoderComparison) (q : Nat) :
    mappedState d (q : M) = (d.state q : M) :=
  packedField_cast d.stateMap 9 512 q

theorem allowedBit_cast (d : DecoderComparison) (q : Nat) (bit : Bool) :
    allowedBit d (q : M) (bit.toNat : M) ↔ d.allowed q bit.toNat = true := by
  let mask : Nat := Nat.mod (d.entryMasks >>> (2*q)) 4
  have maskEq : entryMask d (q : M) = (mask : M) :=
    packedField_cast d.entryMasks 2 4 q
  have bitEq : remIn (divIn (mask : M) (Exp.exp (bit.toNat : M))) 2 =
      (Nat.mod (mask >>> bit.toNat) 2 : M) := by
    have observed := packedField_cast (M := M) mask 1 2 bit.toNat
    simpa only [packedField,Nat.cast_one,one_mul,Nat.cast_ofNat,Nat.one_mul] using observed
  rw [allowedBit,maskEq,bitEq]
  simp only [DecoderComparison.allowed,Bool.or_eq_true,beq_iff_eq,Nat.cast_eq_zero,Nat.cast_eq_one]
  change (mask = 0 ∨ Nat.mod (mask >>> bit.toNat) 2 = 1) ↔ _
  rfl

theorem mappedCode_config (d : DecoderComparison) (q : Nat) (l r : M) :
    mappedCode d (encode (q : M) l r) = encode (d.state q : M) l r := by
  simp only [mappedCode,encode,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair,mappedState_cast]

theorem validReference_config (d : DecoderComparison) (q : Nat) (l r : M) (b : Bool)
    (bit : remIn l 2 = (b.toNat : M)) :
    validReference d (encode (q : M) l r) ↔ q ≤ d.reference.workingStates ∧ d.allowed q b.toNat = true := by
  simp only [validReference,encode,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair,bit,allowedBit_cast,Nat.cast_le]

theorem decoder_simulates_step (d : DecoderComparison) (checked : d.check = true)
    (source : M) (valid : validReference d source) :
    let target := tick d.reference.workingStates d.reference.packedRows source
    validReference d target ∧ Reaches d.physical (mappedCode d source) (mappedCode d target) := by
  change validReference d (tick d.reference.workingStates d.reference.packedRows source) ∧
    Reaches d.physical (mappedCode d source) (mappedCode d (tick d.reference.workingStates d.reference.packedRows source))
  have stateBound := valid.1
  obtain ⟨q,qEq⟩ := eq_nat_of_le_nat stateBound
  let l := π₁ (π₂ source)
  let r := π₂ (π₂ source)
  have encodeSource : source = encode (q : M) l r := by
    rw [← qEq]
    exact (encode_projections source).symm
  by_cases terminal : d.reference.workingStates ≤ q
  · have closed : ¬(q : M) < (d.reference.workingStates : M) := by
      exact_mod_cast (Nat.not_lt.mpr terminal)
    have stays : tick d.reference.workingStates d.reference.packedRows source = source := by
      rw [encodeSource]
      simp [tick,encode,closed]
    rw [stays]
    exact ⟨valid,Reaches.refl _ _⟩
  · have work : q < d.reference.workingStates := by omega
    obtain ⟨prev,lEq⟩ := pushBit_split l
    obtain ⟨read,rEq⟩ := pushBit_split r
    have leftBit : remIn l 2 = (prev.toNat : M) := by rw [← lEq,pushBit_rem]
    have accepted := ((validReference_config d q l r prev leftBit).mp (encodeSource ▸ valid)).2
    obtain ⟨next,l',r',after,range,⟨b,hb,allowed⟩,reach⟩ :=
      decoder_arm_reaches d checked work prev read accepted (divIn l 2) (divIn r 2)
    rw [lEq,rEq,← encodeSource] at after
    rw [lEq,rEq] at reach
    rw [after]
    exact ⟨(validReference_config d next l' r' b hb).mpr ⟨range,allowed⟩,
      by simpa only [encodeSource,mappedCode_config] using reach⟩

@[definability] instance mappedCode_definable (d : DecoderComparison) : 𝚺ᴬ₁-Function₁ (mappedCode (M := M) d) := by
  unfold mappedCode mappedState encode
  definability

@[definability] instance validReference_definable (d : DecoderComparison) :
    𝚺ᴬ₁-Predicate (validReference (M := M) d) := by
  unfold validReference allowedBit entryMask remIn divIn
  definability

@[definability] instance reaches_definable (m : Machine) : 𝚺ᴬ₁-Relation (Reaches (M := M) m) := by
  unfold Reaches
  definability

theorem decoder_simulates_clock (d : DecoderComparison) (checked : d.check = true)
    (start : M) (valid : validReference d start) (n : M) :
    let current := clock d.reference.workingStates d.reference.packedRows n start
    validReference d current ∧ Reaches d.physical (mappedCode d start) (mappedCode d current) := by
  induction n using ISigma1.sigma1_succ_induction with
  | zero =>
    simp only [clock_zero]
    exact ⟨valid,Reaches.refl _ _⟩
  | succ n previous =>
    simp only [clock_succ]
    have advanced := decoder_simulates_step d checked _ previous.1
    exact ⟨advanced.1,previous.2.trans advanced.2⟩
  | hP => definability

theorem literal_halts_of_reference_arithmetic (start : M)
    (valid : validReference decoderComparison start)
    (fromBlank : Reaches machine 0 (mappedCode decoderComparison start))
    (duration : M)
    (terminal : π₁ (clock referenceMachine.workingStates referenceMachine.packedRows duration start) =
        (referenceMachine.workingStates : M)) :
    (haltsDef 380 packedLiteral).val.Evalb (![] : Fin 0 → M) := by
  obtain ⟨_,path⟩ := decoder_simulates_clock decoderComparison decoder_comparison_checked start valid duration
  obtain ⟨time,reach⟩ := fromBlank.trans path
  refine (haltsDef_eval 380 packedLiteral).mpr ⟨time,?_⟩
  rw [show clock 380 packedLiteral time (0 : M) = _ from reach]
  simp only [mappedCode,encode,Arithmetic.pi₁_pair]
  change ¬mappedState decoderComparison
    (π₁ (clock referenceMachine.workingStates referenceMachine.packedRows duration start)) < (380 : M)
  rw [terminal,mappedState_cast]
  have numeric : machine.workingStates ≤ decoderComparison.state referenceMachine.workingStates := by decide +kernel
  have endState : (machine.workingStates : M) ≤ (decoderComparison.state referenceMachine.workingStates : M) := by
    exact_mod_cast numeric
  exact not_lt_of_ge endState

end PalomarI3380.ArithmeticMachine
