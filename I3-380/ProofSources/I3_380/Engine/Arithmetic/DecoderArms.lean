module
public import I3_380.Engine.Arithmetic.WindowReplay
public import I3_380.DecoderComparison
@[expose] public section

namespace PalomarI3380.ArithmeticMachine

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem window_input (q : Nat) (previous read : Bool) (l r : M) :
    windowCode (DecoderComparison.input q previous.toNat read.toNat) l r =
      encode (q : M) (pushBit previous l) (pushBit read r) := by
  simp [windowCode,DecoderComparison.input,pushBit,add_comm]

theorem window_exit_bit (d : DecoderComparison) (next : DecoderWindow) (valid : d.validExit next = true)
    (tail : M) :
    ∃ previous : Bool,
      remIn ((next.config.left : M) + ((2^next.leftLength : Nat) : M)*tail) 2 = (previous.toNat : M) ∧
      d.allowed next.config.state previous.toNat = true := by
  cases length : next.leftLength with
  | zero =>
    have checks : d.allowed next.config.state 0 = true ∧ d.allowed next.config.state 1 = true := by
      simpa only [DecoderComparison.validExit,length,↓reduceIte,Bool.and_eq_true] using valid
    rcases mod_two ((next.config.left : M) + ((2^0 : Nat) : M)*tail) with zero | one
    · exact ⟨false,zero,checks.1⟩
    · exact ⟨true,by simpa only [remIn,Bool.toNat_true,Nat.cast_one] using one,checks.2⟩
  | succ len =>
    have check : d.allowed next.config.state (Nat.mod next.config.left 2) = true := by
      have nonempty : next.leftLength ≠ 0 := by omega
      simp only [DecoderComparison.validExit,nonempty,↓reduceIte] at valid
      exact valid
    rw [tail_remainder]
    have bits : Nat.mod next.config.left 2 = 0 ∨ Nat.mod next.config.left 2 = 1 :=
      Nat.mod_two_eq_zero_or_one _
    rcases bits with zero | one
    · refine ⟨false,by rw [zero]; rfl,?_⟩
      change d.allowed next.config.state 0 = true
      rwa [← zero]
    · refine ⟨true,by rw [one]; rfl,?_⟩
      change d.allowed next.config.state 1 = true
      rwa [← one]

/-- The finite decoder comparison lifts to each arithmetic-model step,
with no restriction on either tail of the two-cell input window. -/
theorem decoder_arm_reaches (d : DecoderComparison) (checked : d.check = true)
    {q : Nat} (active : q < d.reference.workingStates) (previous read : Bool)
    (allowed : d.allowed q previous.toNat = true) (l r : M) :
    ∃ (after : Nat) (left right : M),
      tick d.reference.workingStates d.reference.packedRows
        (encode (q : M) (pushBit previous l) (pushBit read r)) = encode (after : M) left right ∧
      after ≤ d.reference.workingStates ∧
      (∃ b : Bool, remIn left 2 = (b.toNat : M) ∧ d.allowed after b.toNat = true) ∧
      Reaches d.physical
        (encode (d.state q : M) (pushBit previous l) (pushBit read r))
        (encode (d.state after : M) left right) := by
  let input := DecoderComparison.input q previous.toNat read.toNat
  have arm := d.checked_arm checked active previous read
  simp only [DecoderComparison.checkArm,allowed,↓reduceIte] at arm
  change (match DecoderWindow.next d.reference input with
    | none => false
    | some out => _) = true at arm
  cases successor : DecoderWindow.next d.reference input with
  | none => simp [successor] at arm
  | some out =>
    rw [successor] at arm
    simp only [Bool.and_eq_true,decide_eq_true_eq] at arm
    obtain ⟨⟨bound,exit⟩,path⟩ := arm
    have inputName : d.translateWindow (DecoderComparison.input q previous.toNat read.toNat) =
        d.translateWindow input := rfl
    rw [inputName] at path
    generalize replay : DecoderWindow.runToMatch d.physical (d.translateWindow out) 3 (d.translateWindow input) = trace at path
    cases trace with
    | none => cases path
    | some length =>
      let left : M := (out.config.left : M) + ((2^out.leftLength : Nat) : M)*l
      let right : M := (out.config.right : M) + ((2^out.rightLength : Nat) : M)*r
      refine ⟨out.config.state,left,right,?_,bound,window_exit_bit d out exit l,?_⟩
      · change tick d.reference.workingStates d.reference.packedRows
          (encode (q : M) (pushBit previous l) (pushBit read r)) = windowCode out l r
        simpa only [input,window_input] using window_tick successor l r
      · refine ⟨(length : M),?_⟩
        have exactTrace := window_run replay l r
        simpa only [input,DecoderComparison.translateWindow,DecoderComparison.translate,
          windowCode,DecoderComparison.input, Nat.pow_one, Nat.cast_ofNat,
          pushBit,add_comm] using exactTrace

end PalomarI3380.ArithmeticMachine
