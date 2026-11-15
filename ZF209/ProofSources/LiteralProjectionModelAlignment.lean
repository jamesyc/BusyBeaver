module
public import LiteralPairModelAlignment
public import ModelReplay1448
public import ExactUnpairGraph
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma literalFst_modelUnpairLeft (n : M) : t64 n=modelUnpairLeft n := by
 have h := p1277 (modelUnpairLeft n) (modelUnpairRight n)
 change t64 (t63 (modelUnpairLeft n) (modelUnpairRight n))=modelUnpairLeft n at h
 rw [literalPair_modelCantor,modelUnpair_reconstruct] at h
 exact h
lemma literalSnd_modelUnpairRight (n : M) : t65 n=modelUnpairRight n := by
 have h := p1278 (modelUnpairLeft n) (modelUnpairRight n)
 change t65 (t63 (modelUnpairLeft n) (modelUnpairRight n))=modelUnpairRight n at h
 rw [literalPair_modelCantor,modelUnpair_reconstruct] at h
 exact h
end ZF209.MM0ModelReplay
