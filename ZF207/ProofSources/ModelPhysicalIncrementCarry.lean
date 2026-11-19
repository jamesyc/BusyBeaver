module
public import ModelPhysicalIncrementFront
public import ModelPhysicalSpareCarry
public import ModelPhysicalAppendOneTail
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Exact increment through the append-one endpoint, including an internally
sized spare suffix. No external list induction is used for the spare count. -/
lemma native_increment_to_return (pre post:List M) (value spares l:M) :
 Reaches (namedState 64 l (pre.foldr registerBlock
   (markedBlock value (post.foldr registerBlock (spareRun spares 0)))))
 (namedLeft 40 (1+2*spareCarry spares
   (post.foldl (fun acc v=>carryBlockLeft v acc)
    (incrementSelectedLeft value (pre.foldl (fun acc v=>registerBlockLeft v acc) l)))) 6) := by
 have h₁:=native_increment_forward_prefix pre l
   (markedBlock value (post.foldr registerBlock (spareRun spares 0)))
 have h₂:=native_increment_selected value (pre.foldl (fun acc v=>registerBlockLeft v acc) l)
   (post.foldr registerBlock (spareRun spares 0))
 have h₃:=native_carry_primary_prefix post
   (incrementSelectedLeft value (pre.foldl (fun acc v=>registerBlockLeft v acc) l)) (spareRun spares 0)
 have h₄:Reaches (namedState 0
   (post.foldl (fun acc v=>carryBlockLeft v acc)
    (incrementSelectedLeft value (pre.foldl (fun acc v=>registerBlockLeft v acc) l))) (spareRun spares 0))
   (namedState 0 (spareCarry spares (post.foldl (fun acc v=>carryBlockLeft v acc)
    (incrementSelectedLeft value (pre.foldl (fun acc v=>registerBlockLeft v acc) l)))) 0) :=
   native_carry_spares spares _ 0
 exact h₁.trans (h₂.trans (h₃.trans (h₄.trans (native_append_one_tail _))))
end ZF207.BinaryTape
