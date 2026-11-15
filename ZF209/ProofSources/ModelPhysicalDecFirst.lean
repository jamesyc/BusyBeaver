module
public import ModelPhysicalMarkFirst
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Positive decrement of the FIRST marked register, for an arbitrary model value.
The four actual renamed rows are transported to the pinned literal209 table.
No spare is consumed or added and the arbitrary right suffix is untouched. -/
lemma native_decrement_positive_first (value l tail:M) :
 Reaches (namedState 0 l (markedBlock (value+1) tail))
 (namedLeft 40 (1+2*l) (registerBlock value tail)) := by
 let ones:=bitRun (value+1) (1:M) tail
 let rest:=bitRun value (1:M) tail
 have h4:(2:M)*2=4 := by norm_num
 have h₁:Reaches (namedState 0 l (markedBlock (value+1) tail))
  (namedState 94 (1+2*l) (2*ones)) := by
   simpa only [markedBlock,ones,bitValue,Bool.false_eq_true,ite_false,ite_true,
    zero_add,←mul_assoc,h4] using
    named_right 0 94 false true l (2*ones) (by decide +kernel)
 have h₂:Reaches (namedState 94 (1+2*l) (2*ones))
  (namedState 66 (2*(1+2*l)) ones) := by
   simpa only [bitValue,Bool.false_eq_true,ite_false,zero_add] using
    named_right 94 66 false false (1+2*l) ones (by decide +kernel)
 have h₃:Reaches (namedState 66 (2*(1+2*l)) ones)
  (namedState 54 (1+2*l) (2*ones)) := by
   have h:=named_left_any 66 54 true true (2*(1+2*l)) rest (by decide +kernel)
   have hz:(2*(1+2*l):M)=bitValue false+2*(1+2*l) := by simp [bitValue]
   rw [hz,namedLeft_cons] at h
   simpa only [ones,rest,bitRun_succ,bitValue,Bool.false_eq_true,ite_false,ite_true,zero_add] using h
 have h₄:Reaches (namedState 54 (1+2*l) (2*ones))
  (namedLeft 40 (1+2*l) (registerBlock value tail)) := by
   simpa only [registerBlock,ones,bitValue,Bool.false_eq_true,ite_false,zero_add] using
    named_left_any 54 40 false false (1+2*l) ones (by decide +kernel)
 exact h₁.trans (h₂.trans (h₃.trans h₄))
end ZF209.BinaryTape
