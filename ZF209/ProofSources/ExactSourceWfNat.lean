module
public import ExactSourceWfEquations
public import ExactSourceShiftNat
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation

lemma modelSourceWf_nat (n : Nat) : modelSourceWf n ↔ sourceWf n := by
 induction n using Nat.strong_induction_on with
 | h n ih =>
   by_cases hn : n=0
   · subst n
     exact iff_of_true modelSourceWf_zero sourceWf_zero
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
   have ht : t<8 := by dsimp [t]; omega
   have hp : 0<modelSourceNode t a b := by rw [←he]; omega
   have hnode := modelSourceWf_node t a b ht hp
   rw [←he,ih a ha,ih b hb] at hnode
   rw [sourceWf,dif_neg hn]
   exact hnode

lemma sourceWfFormula_nat (n : Nat) : sourceWfFormula.val.Evalb ![n] ↔ sourceWf n := by
 rw [sourceWfFormula_eval,modelSourceWf_nat]

end ZFR.ArithmeticRepresentation
