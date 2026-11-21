module
public import I3_380.Engine.Arithmetic.RegisterSelection
@[expose] public section

namespace PalomarI3380.ArithmeticMachine.Reference

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open Engine (Row)
open Engine.Port

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem registers_with_end (values : List M) (tail : M) :
    registers values (pushBit false tail) = pushBit false (reverseRegisters values tail) := by
  induction values with
  | nil => rfl
  | cons v values ih => simp only [registers,reverseRegisters,ih]

private theorem decScanOnes : Row decScan true true true decScan := by decide +kernel
private theorem decScanZero : Row decScan false true true decSeparator := by decide +kernel
private theorem decNext : Row decSeparator true false true decScan := by decide +kernel

theorem scanDecrement (values : List M) (n l x : M) :
    Reaches referenceMachine
      (cell decScan l (repeatBit true n (registers values (pushBit false (pushBit false x)))))
      (cell decShift (pushBit false (reverseRegisters values.reverse (repeatBit true (n+1) l))) x) := by
  induction values generalizing n l with
  | nil =>
    have first := scanRight decScanOnes n l (pushBit false (pushBit false x))
    have middle := right decScanZero (repeatBit true n l) (pushBit false x)
    have finish := right (show Row decSeparator false false true decShift by decide +kernel)
      (pushBit true (repeatBit true n l)) x
    simpa only [registers,reverseRegisters,List.reverse_nil,repeatBit_succ] using
      first.trans (middle.trans finish)
  | cons v values ih =>
    let tail := registers values (pushBit false (pushBit false x))
    have first := scanRight decScanOnes n l (registers (v::values) (pushBit false (pushBit false x)))
    have middle := right decScanZero (repeatBit true n l) (repeatBit true (v+1) tail)
    have finish := right decNext (repeatBit true (n+1) l) (repeatBit true v tail)
    have rest := ih v (pushBit false (repeatBit true (n+1) l))
    have a : Reaches referenceMachine
        (cell decScan (repeatBit true n l) (registers (v::values) (pushBit false (pushBit false x))))
        (cell decSeparator (repeatBit true (n+1) l) (pushBit true (repeatBit true v tail))) := by
      simpa only [registers,repeatBit_succ,tail] using middle
    have pass := first.trans (a.trans (finish.trans rest))
    simpa only [tail,List.reverse_cons,reverseRegisters_append,reverseRegisters] using pass

theorem startDecrement (a : M) (values : List M) (gap l x : M) :
    Reaches referenceMachine
      (cell dec l (pushBit false (repeatBit false gap (registers (a::values) (pushBit false (pushBit false x))))))
      (cell decShift (pushBit false
        (reverseRegisters (a::values).reverse (repeatBit false (gap+1) (pushBit true l)))) x) := by
  let suffix := registers values (pushBit false (pushBit false x))
  let marker := repeatBit false gap (pushBit true l)
  let tape := registers (a::values) (pushBit false (pushBit false x))
  have zero : Row decGap false false true decGap := by decide +kernel
  have first := right (show Row dec false true true decGap by decide +kernel) l (repeatBit false gap tape)
  have across := scanRight zero gap (pushBit true l) tape
  have pad := right zero marker (repeatBit true (a+1) suffix)
  have enter := right (show Row decGap true false true decScan by decide +kernel)
    (pushBit false marker) (repeatBit true a suffix)
  have scan := scanDecrement values a (pushBit false (pushBit false marker)) x
  have ready : Reaches referenceMachine (cell decGap marker tape)
      (cell decScan (pushBit false (pushBit false marker)) (repeatBit true a suffix)) := by
    simpa only [tape,registers,suffix,repeatBit_succ] using
      pad.trans (by simpa only [repeatBit_succ] using enter)
  simpa only [tape,marker,suffix,List.reverse_cons,reverseRegisters_append,reverseRegisters,repeatBit_succ] using
    first.trans (across.trans (ready.trans scan))

theorem shiftPositive (m n value l x : M) (size : m+n = value+2) :
    Reaches referenceMachine
      (cell decShift (repeatBit true m l) (repeatBit true n (pushBit false x)))
      (cell decSuffix (pushBit true (pushBit false (repeatBit true (value+1) l))) x) := by
  have first := scanRight (show Row decShift true true true decShift by decide +kernel)
    n (repeatBit true m l) (pushBit false x)
  rw [← repeatBit_add,size] at first
  let left := repeatBit true value l
  have move := Reference.left (show Row decShift false false false dec by decide +kernel)
    (pushBit true (pushBit true left)) x
  rw [fromLeft_pushBit] at move
  have save := Reference.left (show Row dec true true false decPrevious by decide +kernel)
    (pushBit true left) (pushBit false x)
  rw [fromLeft_pushBit] at save
  have back := right (show Row decPrevious true true true decRewrite by decide +kernel)
    left (pushBit true (pushBit false x))
  have changeBit := right (show Row decRewrite true false true decRewrite by decide +kernel)
    (pushBit true left) (pushBit false x)
  have finish := right (show Row decRewrite false true true decSuffix by decide +kernel)
    (pushBit false (pushBit true left)) x
  have two : repeatBit true (value+2) l = pushBit true (pushBit true left) := by
    rw [← one_add_one_eq_two,← add_assoc,repeatBit_succ,repeatBit_succ]
  rw [two] at first
  simpa only [repeatBit_succ,left] using
    first.trans (move.trans (save.trans (back.trans (changeBit.trans finish))))

end PalomarI3380.ArithmeticMachine.Reference
