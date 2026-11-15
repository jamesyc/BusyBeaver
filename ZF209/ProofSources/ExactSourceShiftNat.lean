module
public import ExactSourceShiftEquations
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
open C209Soundness

lemma modelSourceNode_nat (t a b : Nat) : modelSourceNode t a b=sourceNode t a b := by
 simp only [modelSourceNode,modelCantor_nat,sourceNode]
 rfl

lemma shiftIndexValue_nat (d i : Nat) :
 graphValue shiftIndexGraph shiftIndexGraph_total ![d,i]=sourceShiftIndex d i := by
 apply (shiftIndexGraph_exact _ _ _).mp
 exact (graphValue_spec shiftIndexGraph shiftIndexGraph_total _ _).mpr rfl

lemma modelSourceShift_nat (d n : Nat) : modelSourceShift d n=sourceShift d n := by
 induction n using Nat.strong_induction_on generalizing d with
 | h n ih =>
  by_cases hn : n=0
  · subst n
    rw [modelSourceShift_zero]
    simp [sourceShift,sourceTransform]
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
  change modelSourceShift d n=sourceTransform sourceShiftIndex d n
  rw [sourceTransform,dif_neg hn]
  change modelSourceShift d n =
   if t=1 then sourceNode 1 (sourceShiftIndex d a) (sourceShiftIndex d b)
   else if t=2 then sourceNode 2 (sourceShiftIndex d a) (sourceShiftIndex d b)
   else if t=3 then sourceNode 3 (sourceShift d a) (sourceShift d b)
   else if t=4 then sourceNode 4 (sourceShift d a) (sourceShift d b)
   else if t=5 then sourceNode 5 (sourceShift d a) (sourceShift d b)
   else if t=6 ∧ b=0 then sourceNode 6 (sourceShift (d+1) a) 0
   else if t=7 ∧ b=0 then sourceNode 7 (sourceShift (d+1) a) 0
   else 0
  by_cases h1 : t=1
  · have hm := modelSourceShift_atomic d t a b (Or.inl h1)
    rw [←he,modelSourceNode_nat,shiftIndexValue_nat,shiftIndexValue_nat] at hm
    simpa [h1] using hm
  by_cases h2 : t=2
  · have hm := modelSourceShift_atomic d t a b (Or.inr h2)
    rw [←he,modelSourceNode_nat,shiftIndexValue_nat,shiftIndexValue_nat] at hm
    simpa [h1,h2] using hm
  by_cases h3 : t=3
  · have hm := modelSourceShift_binary d t a b (Or.inl h3)
    rw [←he,modelSourceNode_nat,ih a ha d,ih b hb d] at hm
    simpa [h1,h2,h3] using hm
  by_cases h4 : t=4
  · have hm := modelSourceShift_binary d t a b (Or.inr (Or.inl h4))
    rw [←he,modelSourceNode_nat,ih a ha d,ih b hb d] at hm
    simpa [h1,h2,h3,h4] using hm
  by_cases h5 : t=5
  · have hm := modelSourceShift_binary d t a b (Or.inr (Or.inr h5))
    rw [←he,modelSourceNode_nat,ih a ha d,ih b hb d] at hm
    simpa [h1,h2,h3,h4,h5] using hm
  by_cases h6 : t=6 ∧ b=0
  · have he' : n=modelSourceNode t a 0 := by simpa only [h6.2] using he
    have hm := modelSourceShift_binder d t a (Or.inl h6.1)
    rw [←he',modelSourceNode_nat,ih a ha (d+1)] at hm
    simpa [h1,h2,h3,h4,h5,h6] using hm
  by_cases h7 : t=7 ∧ b=0
  · have he' : n=modelSourceNode t a 0 := by simpa only [h7.2] using he
    have hm := modelSourceShift_binder d t a (Or.inr h7.1)
    rw [←he',modelSourceNode_nat,ih a ha (d+1)] at hm
    simpa [h1,h2,h3,h4,h5,h6,h7] using hm
  · have hbad : ¬(t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ ((t=6 ∨ t=7) ∧ b=0)) := by tauto
    have hm := modelSourceShift_malformed d n t a b htG haG hbG hbad
    simpa [h1,h2,h3,h4,h5,h6,h7] using hm

lemma sourceShiftGraph_nat (z d n : Nat) :
 sourceShiftGraph.val.Evalb ![z,d,n] ↔ z=sourceShift d n := by
 rw [sourceShiftGraph_eval,modelSourceShift_nat]

end ZFR.ArithmeticRepresentation
