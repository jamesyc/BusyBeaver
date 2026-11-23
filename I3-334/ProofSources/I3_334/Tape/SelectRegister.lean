module
public import I3_334.Tape.ControlWords
@[expose] public section

namespace PalomarI3334.Stock

open PalomarI3380
open PalomarI3380.ArithmeticMachine
open PalomarI3380.ArithmeticMachine.Reference (cell registers reverseRegisters
  registers_append reverseRegisters_append)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

structure SelectorRows (m : Machine) (last back : Nat) : Prop where
  enter : Row m 31 false true true 45
  gap : Row m 45 false false true 45
  firstRegister : Row m 45 true true true 61
  register : Row m 61 true true true 61
  separator : Row m 61 false false true 79
  nextRegister : Row m 79 true true true 61
  mark : Row m 79 false false false last
  insert : Row m last false true false back
  rewind : Row m back true true false back
  replay : Row m back false false true last
  finish : Row m last true false false 46
  returnRows : ReturnRows m 46 62 80 33

theorem referenceSelector : SelectorRows decoderReference 96 109 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    decide +kernel

theorem literalSelector : SelectorRows machine 95 108 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    decide +kernel

variable {m : Machine} {last back : Nat}
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Move the marked boundary past one register, preserving arbitrary
register values and the uninspected right tail in any arithmetic model. -/
theorem selectRegister (rows : SelectorRows m last back) (l gap : M)
    (before : List M) (v rest : M) :
    Reaches m
      (cell 31 l (pushBit false
        (repeatBit false (gap+1) (registers (before++[v]) (pushBit false (pushBit false rest))))))
      (fromLeft 33 l (pushBit false (repeatBit false (gap+1)
        (registers before (pushBit false (pushBit false (repeatBit true (v+1) (pushBit false rest)))))))) := by
  let marker := repeatBit false (gap+1) (pushBit true l)
  let leftTape := reverseRegisters before.reverse marker
  let ones := repeatBit true v
  have seek : Reaches m
      (cell 45 marker (registers (before++[v]) (pushBit false (pushBit false rest))))
      (cell last (repeatBit true (v+1) (pushBit false leftTape)) (pushBit false (pushBit false rest))) := by
    have someHead : ∃ a tail, before++[v] = a::tail := by
      cases before with
      | nil => exact ⟨v,[],rfl⟩
      | cons a tail => exact ⟨a,tail++[v],rfl⟩
    obtain ⟨a,tail,eq⟩ := someHead
    have reach := scanFirstMarked rows.gap rows.firstRegister rows.register rows.separator
      rows.nextRegister rows.mark a tail marker rest
    rw [← eq] at reach
    simpa only [leftTape, List.reverse_append, List.reverse_singleton, reverseRegisters_append,
      reverseRegisters] using reach
  let file := registers (before++[v]) (pushBit false (pushBit false rest))
  have first := right rows.enter l (repeatBit false (gap+1) file)
  have go := scanRight rows.gap (gap+1) (pushBit true l) file
  have erase := left rows.insert (repeatBit true (v+1) (pushBit false leftTape)) (pushBit false rest)
  have scan := scanLeft rows.rewind (v+1) (pushBit false leftTape) (pushBit true (pushBit false rest))
  rw [fromLeft_pushBit] at scan
  have next := right rows.replay leftTape (repeatBit true (v+1) (pushBit true (pushBit false rest)))
  have flip := left rows.finish (pushBit false leftTape) (ones (pushBit true (pushBit false rest)))
  rw [fromLeft_pushBit] at flip
  have finish := scanReturn rows.returnRows before.reverse gap l
    (pushBit false (ones (pushBit true (pushBit false rest))))
  have tailEq : ones (pushBit true (pushBit false rest)) = repeatBit true (v+1) (pushBit false rest) := by
    change repeatBit true v (pushBit true (pushBit false rest)) = _
    rw [repeatBit_push, repeatBit_succ]
  have flipped : Reaches m
      (cell last (pushBit false leftTape) (repeatBit true (v+1) (pushBit true (pushBit false rest))))
      (cell 46 leftTape (pushBit false (pushBit false (ones (pushBit true (pushBit false rest)))))) := by
    simpa only [cell, ones, repeatBit_succ] using flip
  have run := first.trans (go.trans (seek.trans (erase.trans (scan.trans (next.trans (flipped.trans finish))))))
  simpa only [List.reverse_reverse, tailEq] using run

end PalomarI3334.Stock
