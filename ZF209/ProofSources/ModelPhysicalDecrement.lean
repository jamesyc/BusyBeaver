module
public import ModelPhysicalReturnBlocks
public import ModelPhysicalDecFirst
public import ModelPhysicalDecZeroFirst
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Exact positive decrement after a finite primary-register prefix. Every value
and the entire unmodified suffix are arbitrary model quantities. -/
lemma native_decrement_positive (values:List M) (value l tail:M) :
 Reaches (namedState 0 l (values.foldr registerBlock (markedBlock (value+1) tail)))
 (namedLeft 40 (1+2*l) (values.foldr registerBlock (registerBlock value tail))) := by
 have h₁:=native_carry_primary_prefix values l (markedBlock (value+1) tail)
 have h₂:=native_decrement_positive_first value (values.foldl (fun acc v=>carryBlockLeft v acc) l) tail
 rw [carryPrimary_restore] at h₂
 have h₃:=native_return_primary_prefix values (1+2*l) (registerBlock value tail)
 exact h₁.trans (h₂.trans h₃)
/-- Exact zero branch retains the selected zero and its following block; no
spare is removed or reset. The following value is not assumed standard. -/
lemma native_decrement_zero (values:List M) (nextvalue l tail:M) :
 Reaches (namedState 0 l (values.foldr registerBlock (markedBlock 0 (registerBlock nextvalue tail))))
 (namedLeft 97 l (values.foldr registerBlock (registerBlock 0 (registerBlock nextvalue tail)))) := by
 have h₁:=native_carry_primary_prefix values l (markedBlock 0 (registerBlock nextvalue tail))
 have h₂:=native_decrement_zero_first nextvalue (values.foldl (fun acc v=>carryBlockLeft v acc) l) tail
 have h₃:=native_rollback_primary_prefix values l (registerBlock 0 (registerBlock nextvalue tail))
 exact h₁.trans (h₂.trans h₃)
end ZF209.BinaryTape
