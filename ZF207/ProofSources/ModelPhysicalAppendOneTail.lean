module
public import ModelPhysicalOrientation
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Exact original209 append-one tail, using its modified row198/false rather
than the old reference-table tail. The appended spare1 block is011, numeral6. -/
lemma native_append_one_tail (l:M) :
 Reaches (namedState 0 l 0) (namedLeft 40 (1+2*l) 6) := by
 let L1:=1+2*l
 let L2:=2*L1
 let L3:=1+2*L2
 have h₁:Reaches (namedState 0 l 0) (namedState 94 L1 0) := by
  simpa only [L1,bitValue,Bool.false_eq_true,ite_false,ite_true,mul_zero,zero_add] using
   named_right 0 94 false true l 0 (by decide +kernel)
 have h₂:Reaches (namedState 94 L1 0) (namedState 66 L2 0) := by
  simpa only [L2,bitValue,Bool.false_eq_true,ite_false,mul_zero,zero_add] using
   named_right 94 66 false false L1 0 (by decide +kernel)
 have h₃:Reaches (namedState 66 L2 0) (namedState 198 L3 0) := by
  simpa only [L3,bitValue,Bool.false_eq_true,ite_false,ite_true,mul_zero,zero_add] using
   named_right 66 198 false true L2 0 (by decide +kernel)
 have h₄:Reaches (namedState 198 L3 0) (namedState 40 L2 3) := by
  have h:=named_left_any 198 40 false true L3 0 M207.native_tail
  have hL:L3=bitValue true+2*L2 := rfl
  rw [hL,namedLeft_cons] at h
  norm_num [bitValue] at h
  exact h
 have h₅:Reaches (namedState 40 L2 3) (namedState 54 L1 6) := by
  have h:=named_left_any 40 54 true true L2 1 (by decide +kernel)
  have hL:L2=bitValue false+2*L1 := by simp [L2,bitValue]
  rw [hL,namedLeft_cons] at h
  norm_num [bitValue] at h
  exact h
 have h₆:Reaches (namedState 54 L1 6) (namedLeft 40 L1 6) := by
  have h:=named_left_any 54 40 false false L1 (3:M) (by decide +kernel)
  norm_num [bitValue] at h
  exact h
 exact h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans h₆))))
end ZF207.BinaryTape
