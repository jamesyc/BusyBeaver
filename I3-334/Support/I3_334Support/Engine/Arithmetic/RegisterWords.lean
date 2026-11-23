module
public import I3_334Support.Engine.Arithmetic.TapeScans
public import I3_334Support.Engine.ControlWords
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

theorem registers_with_end (values : List M) (tail : M) :
    registers values (pushBit false tail) = pushBit false (reverseRegisters values tail) := by
  induction values with
  | nil => rfl
  | cons v values ih => simp only [registers,reverseRegisters,ih]

theorem repeatZero_slide (n tail : M) :
    repeatBit false (n+1) tail = repeatBit false n (pushBit false tail) := by
  rw [repeatBit_push,repeatBit_succ]

end Reference
end PalomarI3380.ArithmeticMachine
