module
public import ExactMemberCodeGraph
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
omit [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma modelMember_nat (x n : Nat) : modelMember x n ↔ sourceMember x n := by
 induction n using Nat.strong_induction_on with
 | h n ih =>
  by_cases hn : n=0
  · subst n
    simp [modelMember,modelMemberCode_zero,sourceMember,decodeSourceList_zero]
  let a := (C207Soundness.unpair (n-1)).1
  let b := (C207Soundness.unpair (n-1)).2
  have hb : b<n := by have hh:=C207Soundness.unpair_right_le (n-1); dsimp [b]; omega
  have he : n=modelListCons a b := by
   rw [modelListCons,modelCantor_nat]
   dsimp [a,b]
   rw [C207Soundness.unpair_spec]
   omega
  have hm : modelMember x n ↔ a=x ∨ modelMember x b := by
   rw [he,modelMember_cons]
  rw [hm,ih b hb]
  change (a=x ∨ x∈decodeSourceList b) ↔ x∈decodeSourceList n
  have hlist : decodeSourceList n=a::decodeSourceList b := by
   rw [decodeSourceList]
   simp [hn,a,b]
  rw [hlist]
  simp only [List.mem_cons,eq_comm]


end ZFR.ArithmeticRepresentation
