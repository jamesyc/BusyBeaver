module
public import ExactSourceSubstEquations
public import ExactSourceShiftNat
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
open C209Soundness

lemma substIndexValue_nat (d r i : Nat) :
 graphValue substIndexGraph substIndexGraph_total ![d,r,i]=sourceSubstIndex r d i := by
 apply (substIndexGraph_exact _ _ _ _).mp
 exact (graphValue_spec substIndexGraph substIndexGraph_total _ _).mpr rfl

lemma modelSourceSubst_nat (d r n : Nat) : modelSourceSubst d r n=sourceSubst d r n := by
 induction n using Nat.strong_induction_on generalizing d with
 | h n ih =>
  by_cases hn : n=0
  · subst n
    rw [modelSourceSubst_zero]
    simp [sourceSubst,sourceTransform]
  let t := n%8
  let a := (C209Soundness.unpair (n/8)).1
  let b := (C209Soundness.unpair (n/8)).2
  have ha : a<n := lt_of_le_of_lt (C209Soundness.unpair_left_le (n/8)) (Nat.div_lt_self (by omega) (by omega))
  have hb : b<n := lt_of_le_of_lt (C209Soundness.unpair_right_le (n/8)) (Nat.div_lt_self (by omega) (by omega))
  have he : n=modelSourceNode t a b := by
    rw [modelSourceNode_nat]
    unfold sourceNode
    dsimp [t,a,b]
    rw [C209Soundness.unpair_spec]
    omega
  have htG : radix8ResidueGraph.val.Evalb ![t,n] := (radix8ResidueGraph_nat _ _).mpr rfl
  have haG : sourceLeftGraph.val.Evalb ![a,n] := (sourceLeftGraph_nat _ _).mpr rfl
  have hbG : sourceRightGraph.val.Evalb ![b,n] := (sourceRightGraph_nat _ _).mpr rfl
  change modelSourceSubst d r n=sourceTransform (sourceSubstIndex r) d n
  rw [sourceTransform,dif_neg hn]
  change modelSourceSubst d r n =
   if t=1 then sourceNode 1 (sourceSubstIndex r d a) (sourceSubstIndex r d b)
   else if t=2 then sourceNode 2 (sourceSubstIndex r d a) (sourceSubstIndex r d b)
   else if t=3 then sourceNode 3 (sourceSubst d r a) (sourceSubst d r b)
   else if t=4 then sourceNode 4 (sourceSubst d r a) (sourceSubst d r b)
   else if t=5 then sourceNode 5 (sourceSubst d r a) (sourceSubst d r b)
   else if t=6 ∧ b=0 then sourceNode 6 (sourceSubst (d+1) r a) 0
   else if t=7 ∧ b=0 then sourceNode 7 (sourceSubst (d+1) r a) 0
   else 0
  by_cases h1 : t=1
  · have hm := modelSourceSubst_atomic d r t a b (Or.inl h1)
    rw [←he,modelSourceNode_nat,substIndexValue_nat,substIndexValue_nat] at hm
    simpa [h1] using hm
  by_cases h2 : t=2
  · have hm := modelSourceSubst_atomic d r t a b (Or.inr h2)
    rw [←he,modelSourceNode_nat,substIndexValue_nat,substIndexValue_nat] at hm
    simpa [h1,h2] using hm
  by_cases h3 : t=3
  · have hm := modelSourceSubst_binary d r t a b (Or.inl h3)
    rw [←he,modelSourceNode_nat,ih a ha d,ih b hb d] at hm
    simpa [h1,h2,h3] using hm
  by_cases h4 : t=4
  · have hm := modelSourceSubst_binary d r t a b (Or.inr (Or.inl h4))
    rw [←he,modelSourceNode_nat,ih a ha d,ih b hb d] at hm
    simpa [h1,h2,h3,h4] using hm
  by_cases h5 : t=5
  · have hm := modelSourceSubst_binary d r t a b (Or.inr (Or.inr h5))
    rw [←he,modelSourceNode_nat,ih a ha d,ih b hb d] at hm
    simpa [h1,h2,h3,h4,h5] using hm
  by_cases h6 : t=6 ∧ b=0
  · have he' : n=modelSourceNode t a 0 := by simpa only [h6.2] using he
    have hm := modelSourceSubst_binder d r t a (Or.inl h6.1)
    rw [←he',modelSourceNode_nat,ih a ha (d+1)] at hm
    simpa [h1,h2,h3,h4,h5,h6] using hm
  by_cases h7 : t=7 ∧ b=0
  · have he' : n=modelSourceNode t a 0 := by simpa only [h7.2] using he
    have hm := modelSourceSubst_binder d r t a (Or.inr h7.1)
    rw [←he',modelSourceNode_nat,ih a ha (d+1)] at hm
    simpa [h1,h2,h3,h4,h5,h6,h7] using hm
  · have hbad : ¬(t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ ((t=6 ∨ t=7) ∧ b=0)) := by tauto
    have hm := modelSourceSubst_malformed d r n t a b htG haG hbG hbad
    simpa [h1,h2,h3,h4,h5,h6,h7] using hm

lemma sourceSubstGraph_nat (z d r n : Nat) :
 sourceSubstGraph.val.Evalb ![z,d,r,n] ↔ z=sourceSubst d r n := by
 rw [sourceSubstGraph_eval,modelSourceSubst_nat]

end ZFR.ArithmeticRepresentation
