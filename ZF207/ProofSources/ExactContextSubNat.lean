module
public import ExactContextSubPredicate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
omit [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma modelContextSub_nat (n x : Nat) : modelContextSub n x ↔ sourceContextSub n x := by
 induction n using Nat.strong_induction_on with
 | h n ih =>
  by_cases hn : n=0
  · subst n
    simp [modelContextSub,modelContextSubCode_zero,sourceContextSub,sourceMember,decodeSourceList_zero]
  let a := (C207Soundness.unpair (n-1)).1
  let b := (C207Soundness.unpair (n-1)).2
  have hb : b<n := by have hh:=C207Soundness.unpair_right_le (n-1); dsimp [b]; omega
  have he : n=modelListCons a b := by
   rw [modelListCons,modelCantor_nat]
   dsimp [a,b]
   rw [C207Soundness.unpair_spec]
   omega
  rw [he,modelContextSub_cons,modelMember_nat,ih b hb]
  change (sourceMember a x ∧ sourceContextSub b x) ↔ sourceContextSub (modelListCons a b) x
  have hlist : decodeSourceList (modelListCons a b)=a::decodeSourceList b := by
   rw [← he,decodeSourceList]
   simp [hn,a,b]
  simp only [sourceContextSub,sourceMember,hlist,List.mem_cons]
  constructor
  · rintro ⟨ha,hb⟩ c (hc|hc)
    · simpa [hc] using ha
    · exact hb c hc
  · intro hh
    exact ⟨hh a (Or.inl rfl),fun c hc=>hh c (Or.inr hc)⟩
end ZFR.ArithmeticRepresentation
