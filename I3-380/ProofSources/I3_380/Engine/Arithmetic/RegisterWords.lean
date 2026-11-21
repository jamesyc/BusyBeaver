module
public import I3_380.Engine.Arithmetic.TapeScans
public import I3_380.Engine.RegisterPorts
@[expose] public section

namespace PalomarI3380.ArithmeticMachine

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem repeatBit_add (b : Bool) (m n tail : M) :
    repeatBit b (m+n) tail = repeatBit b n (repeatBit b m tail) := by
  induction n using ISigma1.sigma1_succ_induction with
  | zero => simp
  | succ n ih => rw [← add_assoc,repeatBit_succ,repeatBit_succ,ih]
  | hP => definability

theorem repeatBit_push (b : Bool) (n tail : M) :
    repeatBit b n (pushBit b tail) = pushBit b (repeatBit b n tail) := by
  rw [← repeatBit_one b tail,← repeatBit_add,add_comm (1 : M) n,repeatBit_succ]

namespace Reference

open Engine (Row)

noncomputable def cell (state : Nat) (left right : M) : M := encode (state : M) left right

noncomputable def registers : List M → M → M
  | [], tail => tail
  | v::vs, tail => pushBit false (repeatBit true (v+1) (registers vs tail))

noncomputable def reverseRegisters : List M → M → M
  | [], tail => tail
  | v::vs, tail => repeatBit true (v+1) (pushBit false (reverseRegisters vs tail))

@[simp] theorem registers_append (a b : List M) (tail : M) :
    registers (a++b) tail = registers a (registers b tail) := by
  induction a with
  | nil => rfl
  | cons x rest ih => simp only [List.cons_append,registers,ih]

@[simp] theorem reverseRegisters_append (a b : List M) (tail : M) :
    reverseRegisters (a++b) tail = reverseRegisters a (reverseRegisters b tail) := by
  induction a with
  | nil => rfl
  | cons x rest ih => simp only [List.cons_append,reverseRegisters,ih]

noncomputable def frame (path : List Bool) (gap : M) (values : List M) : M :=
  cell Engine.Port.root 1 (packWord path (repeatBit false gap (registers values 0)))

theorem row_bytes {q t : Nat} {b w d : Bool} (row : Row q b w d t) :
    referenceMachine.row q b.toNat = 4*t+2*w.toNat+d.toNat := by
  have bytes := row.2
  change referenceMachine.row q (Engine.bit b) = Engine.bit d + 2*Engine.bit w + 4*t at bytes
  cases b <;> cases w <;> cases d <;> simp [Engine.bit] at bytes ⊢ <;> omega

theorem right {q t : Nat} {b w : Bool} (row : Row q b w true t) (l r : M) :
    Reaches referenceMachine (cell q l (pushBit b r)) (cell t (pushBit w l) r) :=
  Reaches.step_right row.1 (row_bytes row) l r

theorem left {q t : Nat} {b w : Bool} (row : Row q b w false t) (l r : M) :
    Reaches referenceMachine (cell q l (pushBit b r)) (fromLeft t l (pushBit w r)) :=
  Reaches.step_left row.1 (by simpa only [Bool.toNat_false,Nat.add_zero] using row_bytes row) l r

theorem scanRight {q : Nat} {b w : Bool} (row : Row q b w true q) (n l r : M) :
    Reaches referenceMachine (cell q l (repeatBit b n r)) (cell q (repeatBit w n l) r) :=
  ⟨n,scan_right row.1 (row_bytes row) n l r⟩

theorem scanLeft {q : Nat} {b w : Bool} (row : Row q b w false q) (n l r : M) :
    Reaches referenceMachine (fromLeft q (repeatBit b n l) r) (fromLeft q l (repeatBit w n r)) :=
  ⟨n,scan_left row.1 (by simpa only [Bool.toNat_false,Nat.add_zero] using row_bytes row) n l r⟩

theorem scanMarked {q sep exit : Nat} {newBit : Bool}
    (ones : Row q true true true q) (separator : Row q false false true sep)
    (nextRegister : Row sep true true true q) (marked : Row sep false newBit false exit)
    (values : List M) (l r : M) :
    Reaches referenceMachine (cell q l (registers values (pushBit false (pushBit false r))))
      (cell exit (reverseRegisters values.reverse l) (pushBit false (pushBit newBit r))) := by
  induction values generalizing l with
  | nil =>
    have first := right separator l (pushBit false r)
    have last := left marked (pushBit false l) r
    simpa only [registers,reverseRegisters,List.reverse_nil,fromLeft_pushBit,cell] using first.trans last
  | cons value values ih =>
    let tail := registers values (pushBit false (pushBit false r))
    change Reaches referenceMachine (cell q l (pushBit false (repeatBit true (value+1) tail))) _
    have first := right separator l (repeatBit true (value+1) tail)
    have second := right nextRegister (pushBit false l) (repeatBit true value tail)
    have reach := first.trans (by simpa only [repeatBit_succ] using second)
    have path := reach.trans (scanRight ones value (pushBit true (pushBit false l)) tail)
    rw [repeatBit_push,← repeatBit_succ] at path
    simpa only [List.reverse_cons,reverseRegisters_append,reverseRegisters,tail] using path.trans (ih _)

end Reference
end PalomarI3380.ArithmeticMachine
