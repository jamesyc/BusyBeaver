module
public import ModelPhysicalMarkFirst
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Reverse of carry representation1·0·1^value, appended to the left word. -/
noncomputable def carryBlockLeft (value l:M) : M := bitRun value 1 (2+4*l)
lemma native_carry_block (value l tail:M) :
 Reaches (namedState 0 l (registerBlock value tail))
 (namedState 0 (carryBlockLeft value l) tail) := by
 let rest:=bitRun value (1:M) tail
 have h4:(2:M)*2=4 := by norm_num
 have h₁:Reaches (namedState 0 l (registerBlock value tail))
  (namedState 94 (1+2*l) (1+2*rest)) := by
   simpa only [registerBlock,bitRun_succ,bitValue,Bool.false_eq_true,ite_false,ite_true,zero_add,rest] using
    named_right 0 94 false true l (bitRun (value+1) 1 tail) (by decide +kernel)
 have h₂:Reaches (namedState 94 (1+2*l) (1+2*rest))
  (namedState 0 (2+4*l) rest) := by
   simpa only [bitValue,Bool.false_eq_true,ite_false,ite_true,zero_add,mul_add,mul_one,←mul_assoc,h4] using
    named_right 94 0 true false (1+2*l) rest (by decide +kernel)
 have h₃:Reaches (namedState 0 (2+4*l) rest)
  (namedState 0 (carryBlockLeft value l) tail) := by
   simpa only [bitValue,ite_true,carryBlockLeft,rest] using
    named_scan_right 0 true value (2+4*l) tail (by decide +kernel)
 exact h₁.trans (h₂.trans h₃)
/-- The finite prefix here is at most the fixed nine primary registers in applications.
Each register value itself is an arbitrary PA-model element. -/
lemma native_carry_primary_prefix (values:List M) (l tail:M) :
 Reaches (namedState 0 l (values.foldr registerBlock tail))
 (namedState 0 (values.foldl (fun acc v=>carryBlockLeft v acc) l) tail) := by
 induction values generalizing l with
 | nil => exact Reaches.refl _
 | cons v vs ih =>
   exact (native_carry_block v l (vs.foldr registerBlock tail)).trans (ih (carryBlockLeft v l))
end ZF207.BinaryTape
