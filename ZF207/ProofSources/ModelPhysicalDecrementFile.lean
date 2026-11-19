module
public import ModelPhysicalDecrement
public import ModelRegisterFileEncoding
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- The exact zero branch on a full file. The spare count is model-sized and
positive; this supplies the next block even at the last primary register. -/
lemma native_decrement_zero_file (pre post:List M) (spares l:M) :
 Reaches (namedState 0 l (pre.foldr registerBlock
   (markedBlock 0 (post.foldr registerBlock (spareRun (spares+1) 0)))))
 (namedLeft 97 l (pre.foldr registerBlock
   (registerBlock 0 (post.foldr registerBlock (spareRun (spares+1) 0))))) := by
 cases post with
 | nil =>
   simp only [List.foldr_nil]
   rw [spareRun_succ,←registerBlock_one]
   exact native_decrement_zero pre 1 l (spareRun spares 0)
 | cons v vs => exact native_decrement_zero pre v l (vs.foldr registerBlock (spareRun (spares+1) 0))
/-- A positive selected value decrements without consuming or resetting any
spare. The additional left bit accounts for the physical gap increase. -/
lemma native_decrement_positive_file (pre post:List M) (value spares l:M) :
 Reaches (namedState 0 l (pre.foldr registerBlock
   (markedBlock (value+1) (post.foldr registerBlock (spareRun spares 0)))))
 (namedLeft 40 (1+2*l) (pre.foldr registerBlock
   (registerBlock value (post.foldr registerBlock (spareRun spares 0))))) :=
 native_decrement_positive pre value l (post.foldr registerBlock (spareRun spares 0))
end ZF207.BinaryTape
