module
public import I3_334Support.Engine.Arithmetic.RegisterWords
@[expose] public section

namespace PalomarI3334.Stock

open PalomarI3380 PalomarI3380.ArithmeticMachine
open PalomarI3380.ArithmeticMachine.Reference (cell registers reverseRegisters
  registers_append reverseRegisters_append)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def Row (m : Machine) (q : Nat) (b w right : Bool) (target : Nat) : Prop :=
  q < m.workingStates ∧ m.row q b.toNat = 4 * target + 2 * w.toNat + right.toNat
deriving Decidable

variable {m : Machine}

theorem right {q t : Nat} {b w : Bool} (row : Row m q b w true t) (l r : M) :
    Reaches m (cell q l (pushBit b r)) (cell t (pushBit w l) r) :=
  Reaches.step_right row.1 row.2 l r

theorem left {q t : Nat} {b w : Bool} (row : Row m q b w false t) (l r : M) :
    Reaches m (cell q l (pushBit b r)) (fromLeft t l (pushBit w r)) :=
  Reaches.step_left row.1 (by simpa only [Bool.toNat_false, Nat.add_zero] using row.2) l r

theorem scanRight {q : Nat} {b w : Bool} (row : Row m q b w true q) (n l r : M) :
    Reaches m (cell q l (repeatBit b n r)) (cell q (repeatBit w n l) r) :=
  ⟨n, scan_right row.1 row.2 n l r⟩

theorem scanLeft {q : Nat} {b w : Bool} (row : Row m q b w false q) (n l r : M) :
    Reaches m (fromLeft q (repeatBit b n l) r) (fromLeft q l (repeatBit w n r)) :=
  ⟨n, scan_left row.1 (by simpa only [Bool.toNat_false, Nat.add_zero] using row.2) n l r⟩

theorem scanMarked {q sep exit : Nat} {newBit : Bool}
    (ones : Row m q true true true q) (separator : Row m q false false true sep)
    (nextRegister : Row m sep true true true q) (marked : Row m sep false newBit false exit)
    (values : List M) (l r : M) :
    Reaches m (cell q l (registers values (pushBit false (pushBit false r))))
      (cell exit (reverseRegisters values.reverse l) (pushBit false (pushBit newBit r))) := by
  induction values generalizing l with
  | nil =>
    have first := right separator l (pushBit false r)
    have last := left marked (pushBit false l) r
    simpa only [registers,reverseRegisters,List.reverse_nil,fromLeft_pushBit,cell] using first.trans last
  | cons value values ih =>
    let tail := registers values (pushBit false (pushBit false r))
    change Reaches m (cell q l (pushBit false (repeatBit true (value+1) tail))) _
    have first := right separator l (repeatBit true (value+1) tail)
    have second := right nextRegister (pushBit false l) (repeatBit true value tail)
    have reach := first.trans (by simpa only [repeatBit_succ] using second)
    have path := reach.trans (scanRight ones value (pushBit true (pushBit false l)) tail)
    rw [repeatBit_push,← repeatBit_succ] at path
    simpa only [List.reverse_cons,reverseRegisters_append,reverseRegisters,tail] using path.trans (ih _)

theorem scanFirstMarked {lead q separator exit : Nat} {newBit : Bool}
    (leadZero : Row m lead false false true lead) (leadOne : Row m lead true true true q)
    (onesRow : Row m q true true true q) (separatorRow : Row m q false false true separator)
    (nextReg : Row m separator true true true q) (marked : Row m separator false newBit false exit)
    (v : M) (values : List M) (l r : M) :
    Reaches m (cell lead l (registers (v::values) (pushBit false (pushBit false r))))
      (cell exit (reverseRegisters (v::values).reverse l) (pushBit false (pushBit newBit r))) := by
  let tail := registers values (pushBit false (pushBit false r))
  have first := right leadZero l (repeatBit true (v+1) tail)
  have second := right leadOne (pushBit false l) (repeatBit true v tail)
  have run := first.trans (by simpa only [repeatBit_succ] using second)
  have pass := run.trans (scanRight onesRow v (pushBit true (pushBit false l)) tail)
  rw [repeatBit_push,← repeatBit_succ] at pass
  simpa only [registers,List.reverse_cons,reverseRegisters_append,reverseRegisters,tail] using
    pass.trans (scanMarked onesRow separatorRow nextReg marked values _ r)

/-- The leftward return from an increment, common to the three literal tables. -/
structure ReturnRows (m : Machine) (ret separator gap exit : Nat) : Prop where
  first : Row m ret false false false separator
  enter_gap : Row m separator false false false gap
  zeros : Row m gap false false false gap
  marker : Row m gap true false false exit
  next : Row m separator true true false ret
  ones : Row m ret true true false ret

theorem scanReturn {ret sep gapPort exit : Nat} (rows : ReturnRows m ret sep gapPort exit) (values : List M) (gap l y : M) :
    Reaches m
      (cell ret (reverseRegisters values (repeatBit false (gap+1) (pushBit true l))) (pushBit false y))
      (fromLeft exit l
        (pushBit false (repeatBit false (gap+1) (registers values.reverse (pushBit false y))))) := by
  induction values generalizing y with
  | nil =>
    let afterMarker := repeatBit false gap (pushBit true l)
    change Reaches m (cell ret (repeatBit false (gap+1) (pushBit true l)) (pushBit false y)) _
    rw [repeatBit_succ]
    have first := left rows.first (pushBit false afterMarker) y
    rw [fromLeft_pushBit] at first
    have second := left rows.enter_gap afterMarker (pushBit false y)
    have scan := scanLeft rows.zeros gap (pushBit true l) (pushBit false (pushBit false y))
    rw [fromLeft_pushBit] at scan
    have last := left rows.marker l (repeatBit false gap (pushBit false (pushBit false y)))
    have all := first.trans (second.trans (scan.trans last))
    simpa only [registers,List.reverse_nil,repeatBit_succ,repeatBit_push] using all
  | cons v values ih =>
    let tail := reverseRegisters values (repeatBit false (gap+1) (pushBit true l))
    let cord := repeatBit true v (pushBit false tail)
    let block := repeatBit true (v+1) (pushBit false y)
    have first := left rows.first (pushBit true cord) y
    rw [fromLeft_pushBit] at first
    have second := left rows.next cord (pushBit false y)
    have pass := scanLeft rows.ones v (pushBit false tail) (pushBit true (pushBit false y))
    rw [fromLeft_pushBit,repeatBit_push,← repeatBit_succ] at pass
    have all := first.trans (second.trans (pass.trans (ih block)))
    simpa only [reverseRegisters,List.reverse_cons,registers_append,registers,List.singleton_append,
      tail,cord,block,repeatBit_succ] using all

end PalomarI3334.Stock
