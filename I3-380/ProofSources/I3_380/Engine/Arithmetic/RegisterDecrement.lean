module
public import I3_380.Engine.Arithmetic.DecrementScan
@[expose] public section

namespace PalomarI3380.ArithmeticMachine.Reference

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open Engine (Row)
open Engine.Port

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem shiftSuffix (values : List M) (l x : M) :
    Reaches referenceMachine
      (cell decSuffix (pushBit true (pushBit false l)) (reverseRegisters values (pushBit false x)))
      (fromLeft (ret false) (pushBit false (reverseRegisters values.reverse l))
        (pushBit false (pushBit false x))) := by
  induction values generalizing l with
  | nil =>
    have first := Reference.left (show Row decSuffix false false false select by decide +kernel)
      (pushBit true (pushBit false l)) x
    rw [fromLeft_pushBit] at first
    have finish := Reference.left (show Row select true false false (ret false) by decide +kernel)
      (pushBit false l) (pushBit false x)
    exact first.trans finish
  | cons v values ih =>
    let tail := reverseRegisters values (pushBit false x)
    let inserted := repeatBit true (v+1) (pushBit false l)
    have first := right (show Row decSuffix true true true decShift by decide +kernel)
      (pushBit true (pushBit false l)) (repeatBit true v (pushBit false tail))
    have step := shiftPositive 2 v v (pushBit false l) tail (add_comm 2 v)
    have start : repeatBit true 2 (pushBit false l) = pushBit true (pushBit true (pushBit false l)) := by
      have two : ((0 : M)+1)+1 = 2 := by rw [zero_add,one_add_one_eq_two]
      rw [← two,repeatBit_succ,repeatBit_succ,repeatBit_zero]
    rw [start] at step
    have move : Reaches referenceMachine
        (cell decSuffix (pushBit true (pushBit false l)) (reverseRegisters (v::values) (pushBit false x)))
        (cell decSuffix (pushBit true (pushBit false inserted)) tail) := by
      simpa only [tail,reverseRegisters,repeatBit_succ,inserted] using first.trans step
    simpa only [tail,inserted,List.reverse_cons,reverseRegisters_append,reverseRegisters] using move.trans (ih inserted)

/-- Positive decrement and the suffix move, for an arbitrary internal
register value and a fixed finite list of registers on either side. -/
theorem decrementPositive (l gap a : M) (before : List M) (v : M) (after : List M) :
    Reaches referenceMachine
      (cell dec l (pushBit false (repeatBit false gap
        (registers (a::before) (pushBit false (pushBit false (repeatBit true (v+2) (registers after 0))))))))
      (fromLeft (breakPort false) l (pushBit false
        (repeatBit false (gap+1) (registers ((a::before)++v::after) 0)))) := by
  let marker := repeatBit false (gap+1) (pushBit true l)
  let left := reverseRegisters (a::before).reverse marker
  let tail := reverseRegisters after (pushBit false 0)
  let suffix := registers after 0
  have suffixEq : registers after 0 = pushBit false tail := by
    simpa only [suffix,tail,pushBit_false_zero] using registers_with_end after (pushBit false 0 : M)
  have start := startDecrement a before gap l (repeatBit true (v+2) suffix)
  simp only [suffix] at start
  rw [suffixEq] at start
  have move := shiftPositive 0 (v+2) v (pushBit false left) tail (zero_add _)
  have rest := shiftSuffix after (repeatBit true (v+1) (pushBit false left)) (0 : M)
  have leftEq : reverseRegisters after.reverse (repeatBit true (v+1) (pushBit false left)) =
      reverseRegisters ((a::before)++v::after).reverse marker := by
    simp only [left,List.reverse_append,List.reverse_cons,reverseRegisters_append,reverseRegisters]
  rw [leftEq,fromLeft_pushBit] at rest
  have finish := scanReturn false ((a::before)++v::after).reverse gap l (pushBit false (pushBit false 0))
  have combined := start.trans (by
    rw [repeatBit_zero] at move
    exact move.trans (rest.trans finish))
  simpa only [pushBit_false_zero,List.reverse_reverse,suffixEq,tail] using combined

/-- A zero register retains its value and returns through the zero port. -/
theorem decrementZero (l gap a : M) (before after : List M) :
    Reaches referenceMachine
      (cell dec l (pushBit false (repeatBit false gap
        (registers (a::before) (pushBit false (pushBit false (pushBit true (registers after 0))))))))
      (fromLeft (breakPort true) l (pushBit false
        (repeatBit false (gap+1) (registers ((a::before)++0::after) 0)))) := by
  let marker := repeatBit false (gap+1) (pushBit true l)
  let left := reverseRegisters (a::before).reverse marker
  let tail := reverseRegisters after (0 : M)
  have ending : registers after 0 = pushBit false tail := by
    simpa only [tail,pushBit_false_zero] using registers_with_end after (0 : M)
  have start := startDecrement a before gap l (pushBit true (pushBit false tail))
  have shift := right (show Row decShift true true true decShift by decide +kernel)
    (pushBit false left) (pushBit false tail)
  have down := Reference.left (show Row decShift false false false dec by decide +kernel)
    (pushBit true (pushBit false left)) tail
  rw [fromLeft_pushBit] at down
  have back := Reference.left (show Row dec true true false decPrevious by decide +kernel)
    (pushBit false left) (pushBit false tail)
  rw [fromLeft_pushBit] at back
  have finish := Reference.left (show Row decPrevious false false false (ret true) by decide +kernel)
    left (pushBit true (pushBit false tail))
  have all := start.trans (shift.trans (down.trans (back.trans finish)))
  have notEmpty : (a::before).reverse ≠ [] := by simp
  obtain ⟨b,bs,front⟩ := List.exists_cons_of_ne_nil notEmpty
  let behind := reverseRegisters bs marker
  have leftEq : left = repeatBit true (b+1) (pushBit false behind) := by
    simp only [left,front,reverseRegisters,behind]
  let right := pushBit false (pushBit true (pushBit false tail))
  have returnScan := scanLeft (Engine.return_ones true) (b+1) (pushBit false behind) right
  rw [fromLeft_pushBit] at returnScan
  have complete := scanReturn true bs gap l (repeatBit true (b+1) right)
  have same : bs.reverse++[b] = a::before := by
    simpa using (congrArg List.reverse front).symm
  have finalTail :
      registers bs.reverse (pushBit false (repeatBit true (b+1) right)) =
        registers ((a::before)++0::after) 0 := by
    rw [← same,List.append_assoc]
    simp only [registers_append,registers,List.singleton_append,right,ending,
      zero_add,repeatBit_succ,repeatBit_zero,repeatBit_one]
  have run := all.trans (by simpa only [leftEq] using returnScan.trans complete)
  simpa only [ending,finalTail] using run

end PalomarI3380.ArithmeticMachine.Reference
