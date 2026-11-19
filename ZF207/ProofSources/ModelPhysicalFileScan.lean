module
public import ModelPhysicalReaches
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.BinaryTape
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
/-- Cross one actual native unary register block0·1^(v+1), with arbitrary model v.
This transports the whole block onto the left side in reverse order. -/
lemma named_forward_block (qa qb:Nat) (v l tail:M)
 (ones:M207.renamed qa true=some (true,true,qa))
 (zero:M207.renamed qa false=some (false,true,qb))
 (back:M207.renamed qb true=some (true,true,qa)) :
 Reaches (namedState qa l (2*bitRun (v+1) 1 tail))
 (namedState qa (bitRun (v+1) 1 (2*l)) tail) := by
 have h₁:Reaches (namedState qa l (2*bitRun (v+1) 1 tail))
  (namedState qb (2*l) (bitRun (v+1) 1 tail)) := by
   simpa only [bitValue,Bool.false_eq_true,ite_false,zero_add] using
    named_right qa qb false false l (bitRun (v+1) 1 tail) zero
 have h₂:Reaches (namedState qb (2*l) (bitRun (v+1) 1 tail))
  (namedState qa (1+2*(2*l)) (bitRun v 1 tail)) := by
   simpa only [bitValue,ite_true,bitRun_succ] using
    named_right qb qa true true (2*l) (bitRun v 1 tail) back
 have h₃:Reaches (namedState qa (1+2*(2*l)) (bitRun v 1 tail))
  (namedState qa (bitRun (v+1) 1 (2*l)) tail) := by
   simpa only [bitValue,ite_true,bitRun_commute] using
    named_scan_right qa true v (1+2*(2*l)) tail ones
 exact h₁.trans (h₂.trans h₃)
/-- Concrete native increment routine's forward scan control64/74, transported
through the proved permutation to literal207 rather than merely a reference table. -/
lemma native_increment_forward_block (v l tail:M) :
 Reaches (namedState 64 l (2*bitRun (v+1) 1 tail))
 (namedState 64 (bitRun (v+1) 1 (2*l)) tail) :=
 named_forward_block 64 74 v l tail (by decide +kernel) (by decide +kernel) (by decide +kernel)
end ZF207.BinaryTape
