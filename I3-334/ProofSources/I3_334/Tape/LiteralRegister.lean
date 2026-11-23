module
public import I3_334.Tape.FrameRegister
public import I3_334.Simulation.LiteralDecoderWalk
@[expose] public section

namespace PalomarI3334.Stock

open PalomarI3380 PalomarI3380.ArithmeticMachine
open PalomarI3380.ArithmeticMachine.Reference (cell registers reverseRegisters registers_append
  registers_with_end)
open Control (breakPort)
open Engine (breakPath breakPadding registerValue zeroDecrement)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

def literalPort (dec : Bool) (rank : Nat) : Nat :=
  LiteralDecoder.image (Decoder.registerPort dec rank)

theorem literalEntries : EntryRows machine literalPort := by
  constructor <;> decide +kernel

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The literal has the same register update and next pointer as the
reference. In INC, the vanished last mark is paid back as a gap zero. -/
theorem literalRegisterCycle {path : List Bool} {subtract : Bool} {r : Fin 11}
    (route : RegisterRoute machine literalPort path subtract r)
    (gap a value : M) (before after : List M) (index : after.length = r.val) :
    Progress machine (frame path (gap+2+((r.val+1 : Nat) : M)) ((a::before)++value::after))
      (frame (breakPath (zeroDecrement subtract value) path.reverse).reverse
        (gap+2+(Engine.bit subtract : M)+((r.val+1 : Nat) : M)+
          (breakPadding (zeroDecrement subtract value) path.reverse : M))
        ((a::before)++registerValue subtract value::after)) := by
  let marks := r.val+1
  let left := packWord path.reverse (1 : M)
  let saved := reverseRegisters after (0 : M)
  let file := registers (a::before)
    (pushBit false (pushBit false (reverseRegisters (value::after) 0)))
  let suffix := repeatBit false (gap+2) file
  have selection := selectFrame Control.literalRows literalEntries literalSelector route gap
    (a::before) after value index
  have decode := route.run (repeatBit true (marks : M) suffix)
  have enter := enterOperation literalEntries subtract r.val r.isLt left suffix
  rw [← Nat.cast_succ] at enter
  have inOperation := selection.trans (decode.reach.trans enter)
  cases subtract with
  | true =>
    have operation := executeMarkedDec literalDecrement value gap a before after
      (repeatBit true (marks : M) left)
    have restore := restoreFromRegister Control.literalRows path route.short
      (zeroDecrement true value) marks (gap+2+1) ((a::before)++registerValue true value::after)
    simpa only [Engine.bit, ↓reduceIte, Nat.cast_one, marks] using inOperation.trans (operation.trans restore)
  | false =>
    have recompose : incrementedFile a before value (pushBit false saved) =
        registers ((a::before) ++ (value+1) :: after) 0 := by
      have fileTail : registers after (0 : M) = pushBit false saved := by
        simpa only [saved,pushBit_false_zero] using registers_with_end after (0 : M)
      rw [registers_append]
      simp only [incrementedFile, registers, fileTail]
      rw [add_assoc, one_add_one_eq_two]
    have operation := literalIncrement (repeatBit true (r.val : M) left) gap a before value (pushBit false saved)
    rw [recompose] at operation
    have restore := restoreFromRegister Control.literalRows path route.short false r.val (gap+3)
      ((a::before) ++ (value+1) :: after)
    have sameGap : gap+3+(r.val : M) = gap+2+(marks : M) := by
      simp only [marks, Nat.cast_succ]
      have three : (3 : M) = 2+1 := by exact_mod_cast (show (3 : Nat) = 2+1 from rfl)
      rw [three]
      simp only [add_assoc, add_comm, add_left_comm]
    rw [sameGap] at restore
    simp only [operationPort, Bool.false_eq_true, ↓reduceIte, Nat.cast_succ, repeatBit_succ,
      suffix, file, reverseRegisters] at inOperation
    have tail := operation.trans restore
    simp only [selectedFile, saved, repeatBit_succ] at tail
    simpa [zeroDecrement, registerValue, Engine.bit, marks] using inOperation.trans tail

end PalomarI3334.Stock
