module
public import ModelPhysicalDecFirst
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Zero decrement of the first marked register. A following register block is
required, but its value and remaining tail are arbitrary PA-model elements.
The original file and arbitrary left prefix are restored at native control97. -/
lemma native_decrement_zero_first (nextvalue l tail:M) :
 Reaches (namedState 0 l (markedBlock 0 (registerBlock nextvalue tail)))
 (namedLeft 97 l (registerBlock 0 (registerBlock nextvalue tail))) := by
 let ones:=bitRun (nextvalue+1) (1:M) tail
 let rest:=bitRun nextvalue (1:M) tail
 let L1:=1+2*l
 let L2:=2*L1
 let L3:=1+2*L2
 have h4:(2:M)*2=4 := by norm_num
 have h24:(2:M)*4=8 := by norm_num
 have h42:(4:M)*2=8 := by norm_num
 have zeroBlock (x:M) : registerBlock 0 x=2*(1+2*x) := by
  unfold registerBlock
  rw [bitRun_succ,bitRun_zero]
 have h₁:Reaches (namedState 0 l (markedBlock 0 (registerBlock nextvalue tail)))
  (namedState 94 L1 (2*(2*ones))) := by
   simpa only [markedBlock,bitRun_zero,registerBlock,ones,L1,bitValue,Bool.false_eq_true,
    ite_false,ite_true,zero_add,←mul_assoc,h4,h24,h42] using
    named_right 0 94 false true l (2*(2*ones)) (by decide +kernel)
 have h₂:Reaches (namedState 94 L1 (2*(2*ones))) (namedState 66 L2 (2*ones)) := by
   simpa only [L2,bitValue,Bool.false_eq_true,ite_false,zero_add] using
    named_right 94 66 false false L1 (2*ones) (by decide +kernel)
 have h₃:Reaches (namedState 66 L2 (2*ones)) (namedState 198 L3 ones) := by
   simpa only [L3,bitValue,Bool.false_eq_true,ite_false,ite_true,zero_add] using
    named_right 66 198 false true L2 ones (by decide +kernel)
 have h₄:Reaches (namedState 198 L3 ones) (namedState 113 L2 (1+2*ones)) := by
   have h:=named_left_any 198 113 true true L3 rest (by decide +kernel)
   have hL:L3=bitValue true+2*L2 := rfl
   rw [hL,namedLeft_cons] at h
   simpa only [ones,rest,bitRun_succ,bitValue,ite_true] using h
 have h₅:Reaches (namedState 113 L2 (1+2*ones)) (namedState 97 L1 (2*(2*ones))) := by
   have h:=named_left_any 113 97 true false L2 ones (by decide +kernel)
   have hL:L2=bitValue false+2*L1 := by simp [L2,bitValue]
   rw [hL,namedLeft_cons] at h
   simpa only [bitValue,Bool.false_eq_true,ite_false,ite_true,zero_add] using h
 have h₆:Reaches (namedState 97 L1 (2*(2*ones)))
  (namedState 113 l (1+2*(1+2*(2*ones)))) := by
   have h:=named_left_any 97 113 false true L1 (2*ones) (by decide +kernel)
   have hL:L1=bitValue true+2*l := rfl
   rw [hL,namedLeft_cons] at h
   simpa only [bitValue,Bool.false_eq_true,ite_false,ite_true,zero_add] using h
 have h₇:Reaches (namedState 113 l (1+2*(1+2*(2*ones))))
  (namedLeft 97 l (registerBlock 0 (registerBlock nextvalue tail))) := by
   rw [zeroBlock]
   change Reaches (namedState 113 l (1+2*(1+2*(2*ones))))
    (namedLeft 97 l (2*(1+2*(2*ones))))
   simpa only [bitValue,Bool.false_eq_true,ite_false,ite_true,zero_add] using
    named_left_any 113 97 true false l (1+2*(2*ones)) (by decide +kernel)
 exact h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (h₆.trans h₇)))))
end ZF207.BinaryTape
