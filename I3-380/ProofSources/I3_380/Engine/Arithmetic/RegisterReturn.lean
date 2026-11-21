module
public import I3_380.Engine.Arithmetic.RegisterWords
@[expose] public section

namespace PalomarI3380.ArithmeticMachine.Reference

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open Engine (Row)
open Engine.Port

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Return passes the registers to the left of the head, then erases the
temporary marker behind the gap. -/
theorem scanReturn (zero : Bool) (values : List M) (gap l y : M) :
    Reaches referenceMachine
      (cell (ret zero) (reverseRegisters values (repeatBit false (gap+1) (pushBit true l))) (pushBit false y))
      (fromLeft (breakPort zero) l
        (pushBit false (repeatBit false (gap+1) (registers values.reverse (pushBit false y))))) := by
  induction values generalizing y with
  | nil =>
    let afterMarker := repeatBit false gap (pushBit true l)
    change Reaches referenceMachine (cell (ret zero) (repeatBit false (gap+1) (pushBit true l)) (pushBit false y)) _
    rw [repeatBit_succ]
    have first := left (Engine.return_first zero) (pushBit false afterMarker) y
    rw [fromLeft_pushBit] at first
    have second := left (Engine.return_enter_gap zero) afterMarker (pushBit false y)
    have scan := scanLeft (Engine.return_zeros zero) gap (pushBit true l) (pushBit false (pushBit false y))
    rw [fromLeft_pushBit] at scan
    have last := left (Engine.return_marker zero) l (repeatBit false gap (pushBit false (pushBit false y)))
    have all := first.trans (second.trans (scan.trans last))
    simpa only [registers,List.reverse_nil,repeatBit_succ,repeatBit_push] using all
  | cons v values ih =>
    let tail := reverseRegisters values (repeatBit false (gap+1) (pushBit true l))
    let cord := repeatBit true v (pushBit false tail)
    let block := repeatBit true (v+1) (pushBit false y)
    have first := left (Engine.return_first zero) (pushBit true cord) y
    rw [fromLeft_pushBit] at first
    have second := left (Engine.return_next zero) cord (pushBit false y)
    have pass := scanLeft (Engine.return_ones zero) v (pushBit false tail) (pushBit true (pushBit false y))
    rw [fromLeft_pushBit,repeatBit_push,← repeatBit_succ] at pass
    have all := first.trans (second.trans (pass.trans (ih block)))
    simpa only [reverseRegisters,List.reverse_cons,registers_append,registers,List.singleton_append,
      tail,cord,block,repeatBit_succ] using all

theorem scanFirstMarked {lead q separator exit : Nat} {newBit : Bool}
    (leadZero : Row lead false false true lead) (leadOne : Row lead true true true q)
    (onesRow : Row q true true true q) (separatorRow : Row q false false true separator)
    (nextReg : Row separator true true true q) (marked : Row separator false newBit false exit)
    (v : M) (values : List M) (l r : M) :
    Reaches referenceMachine (cell lead l (registers (v::values) (pushBit false (pushBit false r))))
      (cell exit (reverseRegisters (v::values).reverse l) (pushBit false (pushBit newBit r))) := by
  let tail := registers values (pushBit false (pushBit false r))
  have first := right leadZero l (repeatBit true (v+1) tail)
  have second := right leadOne (pushBit false l) (repeatBit true v tail)
  have run := first.trans (by simpa only [repeatBit_succ] using second)
  have pass := run.trans (scanRight onesRow v (pushBit true (pushBit false l)) tail)
  rw [repeatBit_push,← repeatBit_succ] at pass
  simpa only [registers,List.reverse_cons,reverseRegisters_append,reverseRegisters,tail] using
    pass.trans (scanMarked onesRow separatorRow nextReg marked values _ r)

end PalomarI3380.ArithmeticMachine.Reference
