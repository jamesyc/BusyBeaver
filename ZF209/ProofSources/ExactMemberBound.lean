module
public import ExactMemberDefinability
@[expose] public section
namespace ZFR.ArithmeticRepresentation
lemma modelMember_lt_nat (a n : Nat) (hm : modelMember a n) : a<n := by
 induction n using Nat.strong_induction_on with
 | h n ih =>
  by_cases hn:n=0
  · subst n; simp [modelMember,modelMemberCode_zero] at hm
  let x := (C209Soundness.unpair (n-1)).1
  let t := (C209Soundness.unpair (n-1)).2
  have ht:t<n := by have h:=C209Soundness.unpair_right_le (n-1); dsimp [t]; omega
  have hx:x<n := by have h:=C209Soundness.unpair_left_le (n-1); dsimp [x]; omega
  have he:n=modelListCons x t := by
   rw [modelListCons,modelCantor_nat]
   dsimp [x,t]; rw [C209Soundness.unpair_spec]; omega
  rw [he,modelMember_cons] at hm
  rcases hm with ha|ha
  · omega
  · exact Nat.lt_trans (ih t ht ha) ht
end ZFR.ArithmeticRepresentation
