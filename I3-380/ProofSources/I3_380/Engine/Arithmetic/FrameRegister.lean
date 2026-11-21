module
public import I3_380.Engine.Arithmetic.FrameSelection
public import I3_380.Engine.Arithmetic.ControlReturns
public import I3_380.Engine.Arithmetic.RegisterDecrement
@[expose] public section

namespace PalomarI3380.ArithmeticMachine.Reference

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open Engine (breakPadding breakPath registerValue zeroDecrement)
open Engine.Port

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem restoreFromRegister (path : List Bool) (valid : Engine.shortZeros 0 path.reverse = true)
    (skip : Bool) (marks : Nat) (gap : M) (rs : List M) :
    Reaches referenceMachine
      (fromLeft (breakPort skip) (repeatBit true (marks : M) (packWord path.reverse 1))
        (repeatBit false gap (registers rs 0)))
      (frame (breakPath skip path.reverse).reverse
        (gap + (marks : M) + (breakPadding skip path.reverse : M)) rs) := by
  have markedValid : Engine.shortZeros 0 (Engine.ones marks ++ path.reverse) = true := by
    rwa [Engine.shortZeros_ones]
  have run := breakRun skip (Engine.ones marks ++ path.reverse) markedValid
    (repeatBit false gap (registers rs 0))
  rw [packWord_append,← repeatBit_cast] at run
  cases skip with
  | false =>
    simp only [breakPath,Bool.false_eq_true,↓reduceIte,Engine.increment_after_marks,List.reverse_append,
      Engine.reverse_zeros,Engine.break_padding_after_marks,Nat.add_zero,packWord_append,← repeatBit_cast,
      ← repeatBit_add,frame] at run ⊢
    convert run using 4
    ac_rfl
  | true =>
    simp only [breakPath,↓reduceIte,Engine.strip_after_marks,Engine.break_padding_after_marks,Nat.cast_add,
      ← repeatBit_add,frame] at run ⊢
    convert run using 4
    ac_rfl

/-- Execute the selected operation at the double separator, leaving the
other registers alone. The decrement case adds one zero to the gap. -/
theorem executeMarked (subtract : Bool) (value gap a : M) (before after : List M) (l : M) :
    Reaches referenceMachine
      (cell (registerOp subtract) l (repeatBit false (gap+2)
        (registers (a::before) (pushBit false (pushBit false (reverseRegisters (value::after) 0))))))
      (fromLeft (breakPort (zeroDecrement subtract value)) l
        (repeatBit false (gap+2+(Engine.bit subtract : M))
          (registers ((a::before)++registerValue subtract value::after) 0))) := by
  have split : gap+2 = (gap+1)+1 := by rw [add_assoc,one_add_one_eq_two]
  have endEq : registers after (0 : M) = pushBit false (reverseRegisters after 0) := by
    simpa only [pushBit_false_zero] using registers_with_end after (0 : M)
  cases subtract with
  | false =>
    have run := incrementRegister l gap a before value (pushBit false (reverseRegisters after 0))
    simp only [registerOp,Bool.false_eq_true,↓reduceIte,zeroDecrement,Bool.false_and,
      Engine.bit,Nat.cast_zero,add_zero,registerValue,registers_append,reverseRegisters]
    have two : value+2 = (value+1)+1 := by rw [add_assoc,one_add_one_eq_two]
    simpa only [split,two,repeatBit_succ,registers_append,registers,endEq] using run
  | true =>
    have start : repeatBit false (gap+2)
        (registers (a::before) (pushBit false (pushBit false (reverseRegisters (value::after) 0)))) =
      pushBit false (repeatBit false (gap+1)
        (registers (a::before) (pushBit false (pushBit false (repeatBit true (value+1) (registers after 0)))))) := by
      rw [split,repeatBit_succ]
      simp only [reverseRegisters,endEq]
    rw [start]
    rcases zero_or_succ value with rfl | ⟨v,rfl⟩
    · simpa only [registerOp,↓reduceIte,zeroDecrement,Bool.true_and,decide_true,Engine.bit,Nat.cast_one,
        registerValue,ite_eq_left rfl,zero_add,repeatBit_one,split,repeatBit_succ] using
        decrementZero l (gap+1) a before after
    · have nonzero : v+1 ≠ (0 : M) := (lt_of_le_of_lt (Arithmetic.zero_le v) (lt_add_one v)).ne'
      simpa only [registerOp,↓reduceIte,zeroDecrement,Bool.true_and,nonzero,decide_false,Engine.bit,
        Nat.cast_one,registerValue,ite_eq_right nonzero,add_tsub_cancel_right,split,repeatBit_succ, ← add_assoc, ← one_add_one_eq_two] using
        decrementPositive l (gap+1) a before v after

theorem registerCycle {path : List Bool} {subtract : Bool} {r : Fin 12}
    (route : RegisterRoute (M := M) path subtract r) (gap a value : M) (before after : List M)
    (index : after.length = r.val) :
    Reaches referenceMachine (frame path (gap+2+((r.val+1 : Nat) : M)) ((a::before)++value::after))
      (frame (breakPath (zeroDecrement subtract value) path.reverse).reverse
        (gap+2+(Engine.bit subtract : M)+((r.val+1 : Nat) : M)+
          (breakPadding (zeroDecrement subtract value) path.reverse : M))
        ((a::before)++registerValue subtract value::after)) := by
  let marks := r.val+1
  let l := packWord path.reverse (1 : M)
  let x := repeatBit false (gap+2)
    (registers (a::before) (pushBit false (pushBit false (reverseRegisters (value::after) 0))))
  have select := selectFrame route gap (a::before) after value index
  have decode := route.run (repeatBit true (marks : M) x)
  have enter := enterOperation subtract r.val r.isLt l x
  rw [← Nat.cast_succ] at enter
  have operate := executeMarked subtract value gap a before after (repeatBit true (marks : M) l)
  have restore := restoreFromRegister path route.short (zeroDecrement subtract value) marks
    (gap+2+(Engine.bit subtract : M)) ((a::before)++registerValue subtract value::after)
  exact select.trans (decode.trans (enter.trans (operate.trans restore)))

end PalomarI3380.ArithmeticMachine.Reference
