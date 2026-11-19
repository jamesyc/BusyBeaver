module
public import ModelPhysicalFileScan
public import ModelPhysicalReturnBlocks
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma native_increment_forward_prefix (values:List M) (l tail:M) :
 Reaches (namedState 64 l (values.foldr registerBlock tail))
 (namedState 64 (values.foldl (fun acc v=>registerBlockLeft v acc) l) tail) := by
 induction values generalizing l with
 | nil => exact Reaches.refl _
 | cons v vs ih =>
   exact (native_increment_forward_block v l (vs.foldr registerBlock tail)).trans (ih (registerBlockLeft v l))
noncomputable def incrementSelectedLeft (value l:M) : M := bitRun value 1 (1+2*(2*l))
lemma native_increment_selected (value l tail:M) :
 Reaches (namedState 64 l (markedBlock value tail))
 (namedState 0 (incrementSelectedLeft value l) tail) := by
 have h4:(2:M)*2=4 := by norm_num
 have h₁:Reaches (namedState 64 l (markedBlock value tail))
  (namedState 74 (2*l) (2*bitRun value 1 tail)) := by
   simpa only [markedBlock,bitValue,Bool.false_eq_true,ite_false,zero_add,←mul_assoc,h4] using
    named_right 64 74 false false l (2*bitRun value 1 tail) (by decide +kernel)
 have h₂:Reaches (namedState 74 (2*l) (2*bitRun value 1 tail))
  (namedState 0 (1+2*(2*l)) (bitRun value 1 tail)) := by
   simpa only [bitValue,Bool.false_eq_true,ite_false,ite_true,zero_add] using
    named_right 74 0 false true (2*l) (bitRun value 1 tail) (by decide +kernel)
 have h₃:Reaches (namedState 0 (1+2*(2*l)) (bitRun value 1 tail))
  (namedState 0 (incrementSelectedLeft value l) tail) := by
   simpa only [bitValue,ite_true,incrementSelectedLeft] using
    named_scan_right 0 true value (1+2*(2*l)) tail (by decide +kernel)
 exact h₁.trans (h₂.trans h₃)
lemma incrementSelected_restore (value l:M) :
 1+2*incrementSelectedLeft value l=registerBlockLeft (value+1) l := by
 unfold incrementSelectedLeft registerBlockLeft
 rw [← bitRun_succ,bitRun_commute]
end ZF207.BinaryTape
