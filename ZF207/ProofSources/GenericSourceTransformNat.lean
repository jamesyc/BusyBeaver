module
public import GenericSourceTransformEquations
public import ExactSourceShiftNat
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation.GenericTransform
open C207Soundness
lemma modelTransform_nat (idx : 𝚺ᴬ₁.Semisentence 3) (hi : GraphTotalIn (M:=Nat) idx)
 (f : Nat → Nat → Nat) (hIndex : ∀d i, graphValue idx hi ![d,i]=f d i) (d n : Nat) : modelTransform idx hi d n=(sourceTransform f) d n := by
 induction n using Nat.strong_induction_on generalizing d with
 | h n ih =>
  by_cases hn : n=0
  · subst n
    rw [modelTransform_zero idx hi]
    simp [sourceTransform]
  let t := n%8
  let a := (C207Soundness.unpair (n/8)).1
  let b := (C207Soundness.unpair (n/8)).2
  have ha : a<n := lt_of_le_of_lt (C207Soundness.unpair_left_le (n/8)) (Nat.div_lt_self (by omega) (by omega))
  have hb : b<n := lt_of_le_of_lt (C207Soundness.unpair_right_le (n/8)) (Nat.div_lt_self (by omega) (by omega))
  have he : n=modelSourceNode t a b := by
    rw [modelSourceNode_nat]
    unfold sourceNode
    dsimp [t,a,b]
    rw [C207Soundness.unpair_spec]
    omega
  have htG : radix8ResidueGraph.val.Evalb ![t,n] := (radix8ResidueGraph_nat _ _).mpr rfl
  have haG : sourceLeftGraph.val.Evalb ![a,n] := (sourceLeftGraph_nat _ _).mpr rfl
  have hbG : sourceRightGraph.val.Evalb ![b,n] := (sourceRightGraph_nat _ _).mpr rfl
  change modelTransform idx hi d n=sourceTransform f d n
  rw [sourceTransform,dif_neg hn]
  change modelTransform idx hi d n =
   if t=1 then sourceNode 1 (f d a) (f d b)
   else if t=2 then sourceNode 2 (f d a) (f d b)
   else if t=3 then sourceNode 3 ((sourceTransform f) d a) ((sourceTransform f) d b)
   else if t=4 then sourceNode 4 ((sourceTransform f) d a) ((sourceTransform f) d b)
   else if t=5 then sourceNode 5 ((sourceTransform f) d a) ((sourceTransform f) d b)
   else if t=6 ∧ b=0 then sourceNode 6 ((sourceTransform f) (d+1) a) 0
   else if t=7 ∧ b=0 then sourceNode 7 ((sourceTransform f) (d+1) a) 0
   else 0
  by_cases h1 : t=1
  · have hm := modelTransform_atomic idx hi d t a b (Or.inl h1)
    rw [←he,modelSourceNode_nat,hIndex,hIndex] at hm
    simpa [h1] using hm
  by_cases h2 : t=2
  · have hm := modelTransform_atomic idx hi d t a b (Or.inr h2)
    rw [←he,modelSourceNode_nat,hIndex,hIndex] at hm
    simpa [h1,h2] using hm
  by_cases h3 : t=3
  · have hm := modelTransform_binary idx hi d t a b (Or.inl h3)
    rw [←he,modelSourceNode_nat,ih a ha d,ih b hb d] at hm
    simpa [h1,h2,h3] using hm
  by_cases h4 : t=4
  · have hm := modelTransform_binary idx hi d t a b (Or.inr (Or.inl h4))
    rw [←he,modelSourceNode_nat,ih a ha d,ih b hb d] at hm
    simpa [h1,h2,h3,h4] using hm
  by_cases h5 : t=5
  · have hm := modelTransform_binary idx hi d t a b (Or.inr (Or.inr h5))
    rw [←he,modelSourceNode_nat,ih a ha d,ih b hb d] at hm
    simpa [h1,h2,h3,h4,h5] using hm
  by_cases h6 : t=6 ∧ b=0
  · have he' : n=modelSourceNode t a 0 := by simpa only [h6.2] using he
    have hm := modelTransform_binder idx hi d t a (Or.inl h6.1)
    rw [←he',modelSourceNode_nat,ih a ha (d+1)] at hm
    simpa [h1,h2,h3,h4,h5,h6] using hm
  by_cases h7 : t=7 ∧ b=0
  · have he' : n=modelSourceNode t a 0 := by simpa only [h7.2] using he
    have hm := modelTransform_binder idx hi d t a (Or.inr h7.1)
    rw [←he',modelSourceNode_nat,ih a ha (d+1)] at hm
    simpa [h1,h2,h3,h4,h5,h6,h7] using hm
  · have hbad : ¬(t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ ((t=6 ∨ t=7) ∧ b=0)) := by tauto
    have hm := modelTransform_malformed idx hi d n t a b htG haG hbG hbad
    simpa [h1,h2,h3,h4,h5,h6,h7] using hm

end ZFR.ArithmeticRepresentation.GenericTransform
