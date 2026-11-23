module
public import I3_334.Tape.SelectRegister
@[expose] public section

namespace PalomarI3334.Stock

open PalomarI3380
open PalomarI3380.ArithmeticMachine
open PalomarI3380.ArithmeticMachine.Reference (cell registers reverseRegisters
  registers_append reverseRegisters_append registers_with_end)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

/-- The decrement rows depend on the labels assigned to the three
late scan controls and the two zero-result return controls. -/
structure DecrementRows (m : Machine) (scanSep shift suffix retSep retGap : Nat) : Prop where
  enter : Row m 47 false true true 63
  gap : Row m 63 false false true 63
  firstRegister : Row m 63 true false true 81
  scanOnes : Row m 81 true true true 81
  scanZero : Row m 81 false true true scanSep
  nextRegister : Row m scanSep true false true 81
  shiftStart : Row m scanSep false false true shift
  shiftOnes : Row m shift true true true shift
  shiftFinish : Row m shift false false false 47
  rewind : Row m 47 true true false 64
  positive : Row m 64 true true true 83
  noDecrement : Row m 64 false false false 82
  erase : Row m 83 true false true 83
  append : Row m 83 false true true suffix
  nextSuffix : Row m suffix true true true shift
  suffixEnd : Row m suffix false false false 31
  removeExtra : Row m 31 true false false 46
  nonzeroReturn : ReturnRows m 46 62 80 33
  zeroReturn : ReturnRows m 82 retSep retGap 24

theorem referenceDecrement : DecrementRows decoderReference 97 110 99 98 111 := by
  constructor <;> constructor <;> decide +kernel

theorem literalDecrement : DecrementRows machine 96 109 98 97 110 := by
  constructor <;> constructor <;> decide +kernel

variable {machineTable : Machine} {scanSep shiftPort suffixPort retSep retGap : Nat}
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (rows : DecrementRows machineTable scanSep shiftPort suffixPort retSep retGap)
include rows

theorem scanDecrement (values : List M) (n l x : M) :
    Reaches machineTable
      (cell 81 l (repeatBit true n (registers values (pushBit false (pushBit false x)))))
      (cell shiftPort (pushBit false (reverseRegisters values.reverse (repeatBit true (n+1) l))) x) := by
  induction values generalizing n l with
  | nil =>
    have first := scanRight rows.scanOnes n l (pushBit false (pushBit false x))
    have middle := right rows.scanZero (repeatBit true n l) (pushBit false x)
    have finish := right rows.shiftStart
      (pushBit true (repeatBit true n l)) x
    simpa only [registers,reverseRegisters,List.reverse_nil,repeatBit_succ] using
      first.trans (middle.trans finish)
  | cons v values ih =>
    let tail := registers values (pushBit false (pushBit false x))
    have first := scanRight rows.scanOnes n l (registers (v::values) (pushBit false (pushBit false x)))
    have middle := right rows.scanZero (repeatBit true n l) (repeatBit true (v+1) tail)
    have finish := right rows.nextRegister (repeatBit true (n+1) l) (repeatBit true v tail)
    have rest := ih v (pushBit false (repeatBit true (n+1) l))
    have a : Reaches machineTable
        (cell 81 (repeatBit true n l) (registers (v::values) (pushBit false (pushBit false x))))
        (cell scanSep (repeatBit true (n+1) l) (pushBit true (repeatBit true v tail))) := by
      simpa only [registers,repeatBit_succ,tail] using middle
    have pass := first.trans (a.trans (finish.trans rest))
    simpa only [tail,List.reverse_cons,reverseRegisters_append,reverseRegisters] using pass

theorem startDecrement (a : M) (values : List M) (gap l x : M) :
    Reaches machineTable
      (cell 47 l (pushBit false (repeatBit false gap (registers (a::values) (pushBit false (pushBit false x))))))
      (cell shiftPort (pushBit false
        (reverseRegisters (a::values).reverse (repeatBit false (gap+1) (pushBit true l)))) x) := by
  let suffix := registers values (pushBit false (pushBit false x))
  let marker := repeatBit false gap (pushBit true l)
  let tape := registers (a::values) (pushBit false (pushBit false x))
  have zero := rows.gap
  have first := right rows.enter l (repeatBit false gap tape)
  have across := scanRight zero gap (pushBit true l) tape
  have pad := right zero marker (repeatBit true (a+1) suffix)
  have enter := right rows.firstRegister
    (pushBit false marker) (repeatBit true a suffix)
  have scan := scanDecrement rows values a (pushBit false (pushBit false marker)) x
  have ready : Reaches machineTable (cell 63 marker tape)
      (cell 81 (pushBit false (pushBit false marker)) (repeatBit true a suffix)) := by
    simpa only [tape,registers,suffix,repeatBit_succ] using
      pad.trans (by simpa only [repeatBit_succ] using enter)
  simpa only [tape,marker,suffix,List.reverse_cons,reverseRegisters_append,reverseRegisters,repeatBit_succ] using
    first.trans (across.trans (ready.trans scan))

theorem shiftPositive (m n value l x : M) (size : m+n = value+2) :
    Reaches machineTable
      (cell shiftPort (repeatBit true m l) (repeatBit true n (pushBit false x)))
      (cell suffixPort (pushBit true (pushBit false (repeatBit true (value+1) l))) x) := by
  have first := scanRight rows.shiftOnes
    n (repeatBit true m l) (pushBit false x)
  rw [← repeatBit_add,size] at first
  let leftTape := repeatBit true value l
  have move := left rows.shiftFinish
    (pushBit true (pushBit true leftTape)) x
  rw [fromLeft_pushBit] at move
  have save := left rows.rewind
    (pushBit true leftTape) (pushBit false x)
  rw [fromLeft_pushBit] at save
  have back := right rows.positive
    leftTape (pushBit true (pushBit false x))
  have changeBit := right rows.erase
    (pushBit true leftTape) (pushBit false x)
  have finish := right rows.append
    (pushBit false (pushBit true leftTape)) x
  have two : repeatBit true (value+2) l = pushBit true (pushBit true leftTape) := by
    rw [← one_add_one_eq_two,← add_assoc,repeatBit_succ,repeatBit_succ]
  rw [two] at first
  simpa only [repeatBit_succ,leftTape] using
    first.trans (move.trans (save.trans (back.trans (changeBit.trans finish))))

theorem shiftSuffix (values : List M) (l x : M) :
    Reaches machineTable
      (cell suffixPort (pushBit true (pushBit false l)) (reverseRegisters values (pushBit false x)))
      (fromLeft 46 (pushBit false (reverseRegisters values.reverse l))
        (pushBit false (pushBit false x))) := by
  induction values generalizing l with
  | nil =>
    have first := left rows.suffixEnd
      (pushBit true (pushBit false l)) x
    rw [fromLeft_pushBit] at first
    have finish := left rows.removeExtra
      (pushBit false l) (pushBit false x)
    exact first.trans finish
  | cons v values ih =>
    let tail := reverseRegisters values (pushBit false x)
    let inserted := repeatBit true (v+1) (pushBit false l)
    have first := right rows.nextSuffix
      (pushBit true (pushBit false l)) (repeatBit true v (pushBit false tail))
    have step := shiftPositive rows 2 v v (pushBit false l) tail (add_comm 2 v)
    have start : repeatBit true 2 (pushBit false l) = pushBit true (pushBit true (pushBit false l)) := by
      have two : ((0 : M)+1)+1 = 2 := by rw [zero_add,one_add_one_eq_two]
      rw [← two,repeatBit_succ,repeatBit_succ,repeatBit_zero]
    rw [start] at step
    have move : Reaches machineTable
        (cell suffixPort (pushBit true (pushBit false l)) (reverseRegisters (v::values) (pushBit false x)))
        (cell suffixPort (pushBit true (pushBit false inserted)) tail) := by
      simpa only [tail,reverseRegisters,repeatBit_succ,inserted] using first.trans step
    simpa only [tail,inserted,List.reverse_cons,reverseRegisters_append,reverseRegisters] using move.trans (ih inserted)

/-- Positive decrement and the suffix move, for an arbitrary internal
register value and a fixed finite list of registers on either side. -/
theorem decrementPositive (l gap a : M) (before : List M) (v : M) (after : List M) :
    Reaches machineTable
      (cell 47 l (pushBit false (repeatBit false gap
        (registers (a::before) (pushBit false (pushBit false (repeatBit true (v+2) (registers after 0))))))))
      (fromLeft 33 l (pushBit false
        (repeatBit false (gap+1) (registers ((a::before)++v::after) 0)))) := by
  let marker := repeatBit false (gap+1) (pushBit true l)
  let leftTape := reverseRegisters (a::before).reverse marker
  let tail := reverseRegisters after (pushBit false 0)
  let suffix := registers after 0
  have suffixEq : registers after 0 = pushBit false tail := by
    simpa only [suffix,tail,pushBit_false_zero] using registers_with_end after (pushBit false 0 : M)
  have start := startDecrement rows a before gap l (repeatBit true (v+2) suffix)
  simp only [suffix] at start
  rw [suffixEq] at start
  have move := shiftPositive rows 0 (v+2) v (pushBit false leftTape) tail (zero_add _)
  have rest := shiftSuffix rows after (repeatBit true (v+1) (pushBit false leftTape)) (0 : M)
  have leftEq : reverseRegisters after.reverse (repeatBit true (v+1) (pushBit false leftTape)) =
      reverseRegisters ((a::before)++v::after).reverse marker := by
    simp only [leftTape,List.reverse_append,List.reverse_cons,reverseRegisters_append,reverseRegisters]
  rw [leftEq,fromLeft_pushBit] at rest
  have finish := scanReturn rows.nonzeroReturn ((a::before)++v::after).reverse gap l (pushBit false (pushBit false 0))
  have combined := start.trans (by
    rw [repeatBit_zero] at move
    exact move.trans (rest.trans finish))
  simpa only [pushBit_false_zero,List.reverse_reverse,suffixEq,tail] using combined

/-- A zero register retains its value and returns through the zero port. -/
theorem decrementZero (l gap a : M) (before after : List M) :
    Reaches machineTable
      (cell 47 l (pushBit false (repeatBit false gap
        (registers (a::before) (pushBit false (pushBit false (pushBit true (registers after 0))))))))
      (fromLeft 24 l (pushBit false
        (repeatBit false (gap+1) (registers ((a::before)++0::after) 0)))) := by
  let marker := repeatBit false (gap+1) (pushBit true l)
  let leftTape := reverseRegisters (a::before).reverse marker
  let tail := reverseRegisters after (0 : M)
  have ending : registers after 0 = pushBit false tail := by
    simpa only [tail,pushBit_false_zero] using registers_with_end after (0 : M)
  have start := startDecrement rows a before gap l (pushBit true (pushBit false tail))
  have shift := right rows.shiftOnes
    (pushBit false leftTape) (pushBit false tail)
  have down := left rows.shiftFinish
    (pushBit true (pushBit false leftTape)) tail
  rw [fromLeft_pushBit] at down
  have back := left rows.rewind
    (pushBit false leftTape) (pushBit false tail)
  rw [fromLeft_pushBit] at back
  have finish := left rows.noDecrement
    leftTape (pushBit true (pushBit false tail))
  have all := start.trans (shift.trans (down.trans (back.trans finish)))
  have notEmpty : (a::before).reverse ≠ [] := by simp
  obtain ⟨b,bs,front⟩ := List.exists_cons_of_ne_nil notEmpty
  let behind := reverseRegisters bs marker
  have leftEq : leftTape = repeatBit true (b+1) (pushBit false behind) := by
    simp only [leftTape,front,reverseRegisters,behind]
  let right := pushBit false (pushBit true (pushBit false tail))
  have returnScan := scanLeft rows.zeroReturn.ones (b+1) (pushBit false behind) right
  rw [fromLeft_pushBit] at returnScan
  have complete := scanReturn rows.zeroReturn bs gap l (repeatBit true (b+1) right)
  have same : bs.reverse++[b] = a::before := by
    simpa using (congrArg List.reverse front).symm
  have finalTail :
      registers bs.reverse (pushBit false (repeatBit true (b+1) right)) =
        registers ((a::before)++0::after) 0 := by
    rw [← same,List.append_assoc]
    simp only [registers_append,registers,List.singleton_append,right,ending,
      zero_add,repeatBit_succ,repeatBit_one]
  have run := all.trans (by simpa only [leftEq] using returnScan.trans complete)
  simpa only [ending,finalTail] using run

end PalomarI3334.Stock
