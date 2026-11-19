module
public import ModelPhysicalIncrementCarry
public import ModelPhysicalSpareReturn
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Full exact literal207 increment box, including arbitrary model-sized spare
suffix and the modified append-one tail. The spare count increases by one. -/
lemma native_increment_file (pre post:List M) (value spares l:M) :
 Reaches (namedState 64 l (pre.foldr registerBlock
   (markedBlock value (post.foldr registerBlock (spareRun spares 0)))))
 (namedLeft 40 l (pre.foldr registerBlock
   (registerBlock (value+1) (post.foldr registerBlock (spareRun (spares+1) 0))))) := by
 have h₁:=native_increment_to_return pre post value spares l
 rw [spareCarry_restore,carryPrimary_restore,incrementSelected_restore] at h₁
 have h₂:=native_spare_return spares
   (post.foldl (fun acc v=>registerBlockLeft v acc)
    (registerBlockLeft (value+1) (pre.foldl (fun acc v=>registerBlockLeft v acc) l))) 6
 have hs:(spareRun spares (6:M))=spareRun (spares+1) 0 := by
   simpa only [mul_zero,add_zero] using spareRun_commute spares (0:M)
 rw [hs] at h₂
 have h₃:=native_return_primary_prefix post
   (registerBlockLeft (value+1) (pre.foldl (fun acc v=>registerBlockLeft v acc) l)) (spareRun (spares+1) 0)
 have h₄:=named_return_block 54 40 40 (value+1)
   (pre.foldl (fun acc v=>registerBlockLeft v acc) l)
   (post.foldr registerBlock (spareRun (spares+1) 0))
   (by decide +kernel) (by decide +kernel) (by decide +kernel)
 have h₅:=native_return_primary_prefix pre l
   (registerBlock (value+1) (post.foldr registerBlock (spareRun (spares+1) 0)))
 exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))
end ZF207.BinaryTape
