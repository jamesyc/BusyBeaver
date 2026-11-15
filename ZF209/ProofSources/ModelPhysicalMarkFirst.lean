module
public import ModelPhysicalOrientation
public import ModelRegisterFileEncoding
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- First register's actual marked representation00·1^value. -/
noncomputable def markedBlock (value tail:M) : M := 4*bitRun value 1 tail
/-- Exact native mark routine for register0. Parameter value may be nonstandard;
the complete untouched right tail and arbitrary earlier rooted history are preserved. -/
lemma native_mark_first (value l tail:M) :
 Reaches (namedState 51 l (registerBlock value tail))
 (namedLeft 1 l (markedBlock value tail)) := by
 let rest:=bitRun value (1:M) tail
 have h4:(2:M)*2=4 := by norm_num
 have h₁:Reaches (namedState 51 l (registerBlock value tail))
  (namedState 16 (2*l) (1+2*rest)) := by
   simpa only [registerBlock,bitRun_succ,bitValue,Bool.false_eq_true,ite_false,zero_add,rest] using
    named_right 51 16 false false l (bitRun (value+1) 1 tail) (by decide +kernel)
 have h₂:Reaches (namedState 16 (2*l) (1+2*rest))
  (namedState 1 l (2*(2*rest))) := by
   have ht:=named_left_any 16 1 true false (2*l) rest (by decide +kernel)
   have hz : (2*l:M)=bitValue false+2*l := by simp [bitValue]
   rw [hz,namedLeft_cons] at ht
   simpa only [bitValue,ite_true,Bool.false_eq_true,ite_false,zero_add] using ht
 have h₃:Reaches (namedState 1 l (2*(2*rest))) (namedLeft 1 l (markedBlock value tail)) := by
   simpa only [bitValue,Bool.false_eq_true,ite_false,zero_add,markedBlock,←mul_assoc,h4,rest] using
    named_left_any 1 1 false false l (2*rest) (by decide +kernel)
 exact h₁.trans (h₂.trans h₃)
end ZF209.BinaryTape
