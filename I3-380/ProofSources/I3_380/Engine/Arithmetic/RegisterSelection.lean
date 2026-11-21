module
public import I3_380.Engine.Arithmetic.RegisterReturn
@[expose] public section

namespace PalomarI3380.ArithmeticMachine.Reference

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open Engine (Row)
open Engine.Port

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem seekSelect (a : M) (rest : List M) (l r : M) :
    Reaches referenceMachine
      (cell selectGap l (registers (a::rest) (pushBit false (pushBit false r))))
      (cell selectEnd (reverseRegisters (a::rest).reverse l) (pushBit false (pushBit false r))) :=
  scanFirstMarked (lead := selectGap) (q := selectScan) (separator := selectSeparator)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) a rest l r

private theorem seekIncrement (a : M) (rest : List M) (l r : M) :
    Reaches referenceMachine
      (cell incGap l (registers (a::rest) (pushBit false (pushBit false r))))
      (cell (ret false) (reverseRegisters (a::rest).reverse l) (pushBit false (pushBit true r))) :=
  scanFirstMarked (lead := incGap) (q := incScan) (separator := incSeparator)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) a rest l r

/-- Move a pair of separators over one model-valued register. -/
theorem selectRegister (l gap : M) (before : List M) (v rest : M) :
    Reaches referenceMachine
      (cell select l (pushBit false
        (repeatBit false (gap+1) (registers (before++[v]) (pushBit false (pushBit false rest))))))
      (fromLeft (breakPort false) l (pushBit false (repeatBit false (gap+1)
        (registers before (pushBit false (pushBit false (repeatBit true (v+1) (pushBit false rest)))))))) := by
  let markerLeft := repeatBit false (gap+1) (pushBit true l)
  let left := reverseRegisters before.reverse markerLeft
  let ones := repeatBit true v
  have seek : Reaches referenceMachine
      (cell selectGap markerLeft (registers (before++[v]) (pushBit false (pushBit false rest))))
      (cell selectEnd (repeatBit true (v+1) (pushBit false left)) (pushBit false (pushBit false rest))) := by
    have someHead : ∃ a tail, before++[v] = a::tail := by
      cases before with
      | nil => exact ⟨v,[],rfl⟩
      | cons a tail => exact ⟨a,tail++[v],rfl⟩
    obtain ⟨a,tail,eq⟩ := someHead
    have reach := seekSelect a tail markerLeft rest
    rw [← eq] at reach
    simpa only [left,List.reverse_append,List.reverse_singleton,reverseRegisters_append,reverseRegisters] using reach
  have first := right (show Row select false true true selectGap by decide +kernel) l
    (repeatBit false (gap+1) (registers (before++[v]) (pushBit false (pushBit false rest))))
  have go := scanRight (show Row selectGap false false true selectGap by decide +kernel)
    (gap+1) (pushBit true l) (registers (before++[v]) (pushBit false (pushBit false rest)))
  have erase := Reference.left (show Row selectEnd false true false selectBack by decide +kernel)
    (repeatBit true (v+1) (pushBit false left)) (pushBit false rest)
  have scan := scanLeft (show Row selectBack true true false selectBack by decide +kernel)
    (v+1) (pushBit false left) (pushBit true (pushBit false rest))
  rw [fromLeft_pushBit] at scan
  have next := right (show Row selectBack false false true selectEnd by decide +kernel)
    left (repeatBit true (v+1) (pushBit true (pushBit false rest)))
  have flip := Reference.left (show Row selectEnd true false false (ret false) by decide +kernel)
    (pushBit false left) (ones (pushBit true (pushBit false rest)))
  rw [fromLeft_pushBit] at flip
  have finish := scanReturn false before.reverse gap l (pushBit false (ones (pushBit true (pushBit false rest))))
  have tailEq : ones (pushBit true (pushBit false rest)) = repeatBit true (v+1) (pushBit false rest) := by
    change repeatBit true v (pushBit true (pushBit false rest)) = _
    rw [repeatBit_push,repeatBit_succ]
  have flipped : Reaches referenceMachine
      (cell selectEnd (pushBit false left) (repeatBit true (v+1) (pushBit true (pushBit false rest))))
      (cell (ret false) left (pushBit false (pushBit false (ones (pushBit true (pushBit false rest)))))) := by
    simpa only [cell,ones,repeatBit_succ] using flip
  have run := first.trans (go.trans (seek.trans (erase.trans (scan.trans (next.trans (flipped.trans finish))))))
  simpa only [List.reverse_reverse,tailEq] using run

/-- Increment the register marked by two successive separators. -/
theorem incrementRegister (l gap a : M) (before : List M) (v rest : M) :
    Reaches referenceMachine
      (cell inc l (pushBit false (repeatBit false (gap+1)
        (registers (a::before) (pushBit false (pushBit false (repeatBit true (v+1) rest)))))))
      (fromLeft (breakPort false) l (pushBit false (repeatBit false (gap+1)
        (registers (a::before) (pushBit false (repeatBit true (v+2) rest)))))) := by
  have first := right (show Row inc false true true incGap by decide +kernel) l
    (repeatBit false (gap+1)
      (registers (a::before) (pushBit false (pushBit false (repeatBit true (v+1) rest)))))
  have pass := scanRight (show Row incGap false false true incGap by decide +kernel)
    (gap+1) (pushBit true l) (registers (a::before) (pushBit false (pushBit false (repeatBit true (v+1) rest))))
  have selected := seekIncrement a before (repeatBit false (gap+1) (pushBit true l)) (repeatBit true (v+1) rest)
  have finish := scanReturn false (a::before).reverse gap l (pushBit true (repeatBit true (v+1) rest))
  have run := first.trans (pass.trans (selected.trans finish))
  simpa only [List.reverse_reverse,← repeatBit_succ,add_assoc,one_add_one_eq_two] using run

end PalomarI3380.ArithmeticMachine.Reference
