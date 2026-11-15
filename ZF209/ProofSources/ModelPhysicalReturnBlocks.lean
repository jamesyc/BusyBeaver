module
public import ModelPhysicalCarryBlock
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def registerBlockLeft (value l:M) : M := bitRun (value+1) 1 (2*l)
lemma named_return_block (qa qb q:Nat) (v l r:M)
 (loop:M209.renamed qa true=some (true,false,qa))
 (zero:M209.renamed qa false=some (false,false,qb))
 (enter:M209.renamed q true=some (true,false,qa)) :
 Reaches (namedLeft q (registerBlockLeft v l) r) (namedLeft qb l (registerBlock v r)) := by
 have h₁:Reaches (namedLeft q (registerBlockLeft v l) r)
  (namedLeft qa (bitRun v 1 (2*l)) (1+2*r)) := by
   unfold registerBlockLeft
   rw [bitRun_succ,show (1:M)=bitValue true by rfl,namedLeft_cons]
   simpa only [bitValue,ite_true] using named_left_any q qa true true (bitRun v 1 (2*l)) r enter
 have h₂:Reaches (namedLeft qa (bitRun v 1 (2*l)) (1+2*r))
  (namedLeft qa (2*l) (bitRun (v+1) 1 r)) := by
   simpa only [bitValue,ite_true,bitRun_commute] using named_scan_left_oriented qa true v (2*l) (1+2*r) loop
 have h₃:Reaches (namedLeft qa (2*l) (bitRun (v+1) 1 r))
  (namedLeft qb l (registerBlock v r)) := by
   have hz:(2*l:M)=bitValue false+2*l := by simp [bitValue]
   rw [hz,namedLeft_cons]
   simpa only [bitValue,Bool.false_eq_true,ite_false,zero_add,registerBlock] using
    named_left_any qa qb false false l (bitRun (v+1) 1 r) zero
 exact h₁.trans (h₂.trans h₃)
lemma named_return_primary_prefix (qa qb:Nat) (values:List M) (l r:M)
 (loop:M209.renamed qa true=some (true,false,qa))
 (zero:M209.renamed qa false=some (false,false,qb))
 (enter:M209.renamed qb true=some (true,false,qa)) :
 Reaches (namedLeft qb (values.foldl (fun acc v=>registerBlockLeft v acc) l) r)
 (namedLeft qb l (values.foldr registerBlock r)) := by
 induction values generalizing l with
 | nil => exact Reaches.refl _
 | cons v vs ih =>
   exact (ih (registerBlockLeft v l)).trans (named_return_block qa qb qb v l (vs.foldr registerBlock r) loop zero enter)
lemma native_return_primary_prefix (values:List M) (l r:M) :
 Reaches (namedLeft 40 (values.foldl (fun acc v=>registerBlockLeft v acc) l) r)
 (namedLeft 40 l (values.foldr registerBlock r)) :=
 named_return_primary_prefix 54 40 values l r (by decide +kernel) (by decide +kernel) (by decide +kernel)
lemma carryBlockLeft_restore (v l:M) : 1+2*carryBlockLeft v l=registerBlockLeft v (1+2*l) := by
 unfold carryBlockLeft registerBlockLeft
 rw [bitRun_succ]
 have h4:(2:M)*2=4 := by norm_num
 simp only [mul_add,mul_one,←mul_assoc,h4]
lemma carryPrimary_restore (values:List M) (l:M) :
 1+2*values.foldl (fun acc v=>carryBlockLeft v acc) l=
 values.foldl (fun acc v=>registerBlockLeft v acc) (1+2*l) := by
 induction values generalizing l with
 | nil => rfl
 | cons v vs ih =>
   simp only [List.foldl_cons]
   rw [ih,carryBlockLeft_restore]
lemma native_rollback_block (v l r:M) :
 Reaches (namedLeft 97 (carryBlockLeft v l) r) (namedLeft 97 l (registerBlock v r)) := by
 let rest:=bitRun v (1:M) r
 have h4:(2:M)*2=4 := by norm_num
 have h₁:Reaches (namedLeft 97 (carryBlockLeft v l) r) (namedLeft 97 (2+4*l) rest) := by
   exact named_scan_left_oriented 97 true v (2+4*l) r (by decide +kernel)
 have h₂:Reaches (namedLeft 97 (2+4*l) rest) (namedState 113 l (1+2*(1+2*rest))) := by
   have hz:(2+4*l:M)=bitValue false+2*(1+2*l) := by simp [bitValue,mul_add,←mul_assoc,h4]
   rw [hz,namedLeft_cons]
   have ht:=named_left_any 97 113 false true (1+2*l) rest (by decide +kernel)
   rw [show (1+2*l:M)=bitValue true+2*l by rfl,namedLeft_cons] at ht
   simpa only [bitValue,Bool.false_eq_true,ite_false,ite_true] using ht
 have h₃:Reaches (namedState 113 l (1+2*(1+2*rest))) (namedLeft 97 l (registerBlock v r)) := by
   simpa only [bitValue,ite_true,Bool.false_eq_true,ite_false,zero_add,registerBlock,bitRun_succ,rest] using
    named_left_any 113 97 true false l (1+2*rest) (by decide +kernel)
 exact h₁.trans (h₂.trans h₃)
lemma native_rollback_primary_prefix (values:List M) (l r:M) :
 Reaches (namedLeft 97 (values.foldl (fun acc v=>carryBlockLeft v acc) l) r)
 (namedLeft 97 l (values.foldr registerBlock r)) := by
 induction values generalizing l with
 | nil => exact Reaches.refl _
 | cons v vs ih =>
   exact (ih (carryBlockLeft v l)).trans (native_rollback_block v l (vs.foldr registerBlock r))
end ZF209.BinaryTape
