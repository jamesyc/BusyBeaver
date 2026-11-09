module

public import PA215PA.ActualCommandRealizesFormula
public import PA215PA.ActualRuleExpression
public import PA215PA.ActualCompilerRuleExpression

@[expose] public section
namespace PA215.PA.ActualCompilerLeafSoundness
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal ActualHeadGraphs ActualCommandStepGraph
macro "expose_actual_rule_helpers" : tactic => `(tactic|
  simp only [ActualRuleExpression.Templates.zero, ActualRuleExpression.Templates.one,
    ActualRuleExpression.Templates.accepted, ActualRuleExpression.Templates.r1,
    ActualRuleExpression.Templates.r2, ActualRuleExpression.Templates.r3,
    ActualRuleExpression.Templates.r4, ActualRuleExpression.Templates.a,
    ActualRuleExpression.Templates.b, ActualRuleExpression.Templates.c,
    ActualRuleExpression.Templates.u, ActualRuleExpression.Templates.h,
    ActualRuleExpression.Templates.requireZero, ActualRuleExpression.Templates.minor,
    ActualRuleExpression.Templates.major,
    ActualCompilerRuleExpression.Templates.zero, ActualCompilerRuleExpression.Templates.r1,
    ActualCompilerRuleExpression.Templates.r2, ActualCompilerRuleExpression.Templates.r3,
    ActualCompilerRuleExpression.Templates.r4, ActualCompilerRuleExpression.Templates.a,
    ActualCompilerRuleExpression.Templates.b, ActualCompilerRuleExpression.Templates.c,
    ActualCompilerRuleExpression.Templates.u, ActualCompilerRuleExpression.Templates.requireZero] at *)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem leaf1_sound (previous words tag payload out : V)
    (h : ActualCheckExpression.eval ActualRuleExpression.leaf1 previous tag payload=out+1) :
    Realizes (ActualWordExpression.eval ActualCompilerRuleExpression.leaf1 words tag payload) out := by
  unfold ActualRuleExpression.leaf1 at h
  unfold ActualCompilerRuleExpression.leaf1
  expose_actual_rule_helpers
  simp only [ActualCheckExpression.eval,Nat.cast_zero,Nat.cast_one] at h
  simp only [ActualWordExpression.eval,ActualCheckExpression.eval,Nat.cast_zero]
  by_cases ht : decodeRight (decodeRight payload)=0
  · simp only [ht,ite_true] at h ⊢
    rw [selectedHead_expr]
    have he : ActualArithmeticGraph.eval rho1Expr (decodeLeft payload)
      (decodeLeft (decodeRight payload)) 0 0=out := add_right_cancel h
    rw [← he]
    exact realizes_head1 _ _ _
  · simp only [ht,ite_false] at h
    exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))
theorem leaf2_sound (previous words tag payload out : V)
    (h : ActualCheckExpression.eval ActualRuleExpression.leaf2 previous tag payload=out+1) :
    Realizes (ActualWordExpression.eval ActualCompilerRuleExpression.leaf2 words tag payload) out := by
  unfold ActualRuleExpression.leaf2 at h
  unfold ActualCompilerRuleExpression.leaf2
  expose_actual_rule_helpers
  simp only [ActualCheckExpression.eval,Nat.cast_zero,Nat.cast_one] at h
  simp only [ActualWordExpression.eval,ActualCheckExpression.eval,Nat.cast_zero]
  by_cases ht : decodeRight (decodeRight (decodeRight payload))=0
  · simp only [ht,ite_true] at h ⊢
    rw [selectedHead_expr]
    have he : ActualArithmeticGraph.eval rho2Expr (decodeLeft payload)
      (decodeLeft (decodeRight payload)) (decodeLeft (decodeRight (decodeRight payload))) 0=out := add_right_cancel h
    rw [← he]
    exact realizes_head2 _ _ _
  · simp only [ht,ite_false] at h
    exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))
theorem leaf3_sound (previous words tag payload out : V)
    (h : ActualCheckExpression.eval ActualRuleExpression.leaf3 previous tag payload=out+1) :
    Realizes (ActualWordExpression.eval ActualCompilerRuleExpression.leaf3 words tag payload) out := by
  unfold ActualRuleExpression.leaf3 at h
  unfold ActualCompilerRuleExpression.leaf3
  expose_actual_rule_helpers
  simp only [ActualCheckExpression.eval,Nat.cast_zero,Nat.cast_one] at h
  simp only [ActualWordExpression.eval,ActualCheckExpression.eval,Nat.cast_zero]
  by_cases ht : decodeRight (decodeRight (decodeRight payload))=0
  · simp only [ht,ite_true] at h ⊢
    rw [selectedHead_expr]
    have he : ActualArithmeticGraph.eval rho3Expr (decodeLeft payload)
      (decodeLeft (decodeRight payload)) (decodeLeft (decodeRight (decodeRight payload))) 0=out := add_right_cancel h
    rw [← he]
    exact realizes_head3 _ _ _
  · simp only [ht,ite_false] at h
    exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))
theorem leaf4_sound (previous words tag payload out : V)
    (h : ActualCheckExpression.eval ActualRuleExpression.leaf4 previous tag payload=out+1) :
    Realizes (ActualWordExpression.eval ActualCompilerRuleExpression.leaf4 words tag payload) out := by
  unfold ActualRuleExpression.leaf4 at h
  unfold ActualCompilerRuleExpression.leaf4
  expose_actual_rule_helpers
  simp only [ActualCheckExpression.eval,Nat.cast_zero,Nat.cast_one] at h
  simp only [ActualWordExpression.eval,ActualCheckExpression.eval,Nat.cast_zero]
  by_cases ht : decodeRight (decodeRight (decodeRight payload))=0
  · simp only [ht,ite_true] at h ⊢
    rw [selectedHead_expr]
    have he : ActualArithmeticGraph.eval rho4Expr (decodeLeft payload)
      (decodeLeft (decodeRight payload)) (decodeLeft (decodeRight (decodeRight payload))) 0=out := add_right_cancel h
    rw [← he]
    exact realizes_head4 _ _ _
  · simp only [ht,ite_false] at h
    exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))
theorem leaf5_sound (previous words tag payload out : V)
    (h : ActualCheckExpression.eval ActualRuleExpression.leaf5 previous tag payload=out+1) :
    Realizes (ActualWordExpression.eval ActualCompilerRuleExpression.leaf5 words tag payload) out := by
  unfold ActualRuleExpression.leaf5 at h
  unfold ActualCompilerRuleExpression.leaf5
  expose_actual_rule_helpers
  simp only [ActualCheckExpression.eval,Nat.cast_zero,Nat.cast_one] at h
  simp only [ActualWordExpression.eval,ActualCheckExpression.eval,Nat.cast_zero]
  by_cases ht : decodeRight (decodeRight (decodeRight payload))=0
  · simp only [ht,ite_true] at h ⊢
    rw [selectedHead_expr]
    have he : ActualArithmeticGraph.eval rho5Expr (decodeLeft payload)
      (decodeLeft (decodeRight payload)) (decodeLeft (decodeRight (decodeRight payload))) 0=out := add_right_cancel h
    rw [← he]
    exact realizes_head5 _ _ _
  · simp only [ht,ite_false] at h
    exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))
theorem leaf6_sound (previous words tag payload out : V)
    (h : ActualCheckExpression.eval ActualRuleExpression.leaf6 previous tag payload=out+1) :
    Realizes (ActualWordExpression.eval ActualCompilerRuleExpression.leaf6 words tag payload) out := by
  unfold ActualRuleExpression.leaf6 at h
  unfold ActualCompilerRuleExpression.leaf6
  expose_actual_rule_helpers
  simp only [ActualCheckExpression.eval,Nat.cast_zero,Nat.cast_one] at h
  simp only [ActualWordExpression.eval,ActualCheckExpression.eval,Nat.cast_zero]
  by_cases ht : decodeRight (decodeRight payload)=0
  · simp only [ht,ite_true] at h ⊢
    rw [selectedHead_expr]
    have he : ActualArithmeticGraph.eval rho6Expr (decodeLeft payload)
      0 (decodeLeft (decodeRight payload)) 0=out := add_right_cancel h
    rw [← he]
    exact realizes_head6 _ _ _
  · simp only [ht,ite_false] at h
    exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))
theorem leaf7_sound (previous words tag payload out : V)
    (h : ActualCheckExpression.eval ActualRuleExpression.leaf7 previous tag payload=out+1) :
    Realizes (ActualWordExpression.eval ActualCompilerRuleExpression.leaf7 words tag payload) out := by
  unfold ActualRuleExpression.leaf7 at h
  unfold ActualCompilerRuleExpression.leaf7
  expose_actual_rule_helpers
  simp only [ActualCheckExpression.eval,Nat.cast_zero,Nat.cast_one] at h
  simp only [ActualWordExpression.eval,ActualCheckExpression.eval,Nat.cast_zero]
  by_cases ht : decodeRight (decodeRight (decodeRight payload))=0
  · simp only [ht,ite_true] at h ⊢
    rw [selectedHead_expr]
    have he : ActualArithmeticGraph.eval rho7Expr (decodeLeft payload)
      (decodeLeft (decodeRight payload)) (decodeLeft (decodeRight (decodeRight payload))) 0=out := add_right_cancel h
    rw [← he]
    exact realizes_head7 _ _ _
  · simp only [ht,ite_false] at h
    exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))

theorem leaf8_sound (previous words tag payload out : V)
    (h : ActualCheckExpression.eval ActualRuleExpression.leaf8 previous tag payload=out+1) :
    Realizes (ActualWordExpression.eval ActualCompilerRuleExpression.leaf8 words tag payload) out := by
  unfold ActualRuleExpression.leaf8 at h
  unfold ActualCompilerRuleExpression.leaf8
  expose_actual_rule_helpers
  simp only [ActualCheckExpression.eval,Nat.cast_zero,Nat.cast_one] at h
  simp only [ActualWordExpression.eval,ActualCheckExpression.eval,Nat.cast_zero]
  by_cases ht : decodeRight (decodeRight (decodeRight (decodeRight payload)))=0
  · simp only [ht,ite_true] at h ⊢
    by_cases hu : decodeLeft (decodeRight (decodeRight (decodeRight payload))) ≤ decodeLeft payload
    · simp only [hu,ite_true] at h ⊢
      rw [head8_expr]
      have he := add_right_cancel h
      rw [← he]
      exact realizes_head8 _ _ _ _ hu
    · simp only [hu,ite_false] at h
      exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))
  · simp only [ht,ite_false] at h
    exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))

theorem bundle_sound (previous words tag payload out : V)
    (h : ActualCheckExpression.eval ActualRuleExpression.rawBundle previous tag payload=out+1) :
    Realizes (ActualWordExpression.eval ActualCompilerRuleExpression.rawBundle words tag payload) out := by
  unfold ActualRuleExpression.rawBundle at h
  unfold ActualCompilerRuleExpression.rawBundle
  expose_actual_rule_helpers
  simp only [ActualCheckExpression.eval,Nat.cast_zero,Nat.cast_one] at h
  simp only [ActualWordExpression.eval,ActualCheckExpression.eval,Nat.cast_zero]
  by_cases ht : decodeRight (decodeRight (decodeRight payload))=0
  · simp only [ht,ite_true] at h ⊢
    by_cases ha : decodeLeft (decodeRight (decodeRight payload))=decodeLeft payload
    · simp only [ha,ite_true] at h
      exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))
    · simp only [ha,ite_false] at h ⊢
      by_cases hb : decodeLeft (decodeRight (decodeRight payload))=decodeLeft (decodeRight payload)
      · simp only [hb,ite_true] at h
        exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))
      · simp only [hb,ite_false] at h ⊢
        rw [gate_expr]
        have he := add_right_cancel h
        rw [← he]
        have hg := realizes_gate (decodeLeft payload) (decodeLeft (decodeRight payload))
          (decodeLeft (decodeRight (decodeRight payload)))
        have hz : decodeLeft (0:V)=0 := by simp [decodeLeft]
        simpa only [gateValue,ha,hb,ite_false,ActualCheckExpression.eval,hz] using hg
  · simp only [ht,ite_false] at h
    exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))
#print axioms leaf8_sound
#print axioms bundle_sound
#print axioms leaf1_sound
#print axioms leaf2_sound
#print axioms leaf3_sound
#print axioms leaf4_sound
#print axioms leaf5_sound
#print axioms leaf6_sound
#print axioms leaf7_sound
end PA215.PA.ActualCompilerLeafSoundness
