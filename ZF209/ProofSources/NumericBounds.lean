module
public import NumericTransform
public import GeneralizationBridge
@[expose] public section
namespace ZFR
open C209Soundness

def sourceBound (k n : Nat) : Prop :=
 if h : n = 0 then True else
 let t := n % 8
 let p := unpair (n/8)
 ((t=1 ∨ t=2) ∧ p.1 < k ∧ p.2 < k) ∨
 ((t=3 ∨ t=4 ∨ t=5) ∧ sourceBound k p.1 ∧ sourceBound k p.2) ∨
 ((t=6 ∨ t=7) ∧ p.2=0 ∧ sourceBound (k+1) p.1)
termination_by n
decreasing_by
 all_goals
  have hq : n/8 < n := Nat.div_lt_self (by omega) (by omega)
  have := unpair_left_le (n/8)
  have := unpair_right_le (n/8)
  omega

theorem sourceBound_zero (k : Nat) : sourceBound k 0 ↔ True := by
 rw [sourceBound]; simp

theorem sourceBound_node (k t a b : Nat) (ht : t < 8) (hp : 0 < t) :
 sourceBound k (sourceNode t a b) ↔
 ((t=1 ∨ t=2) ∧ a < k ∧ b < k) ∨
 ((t=3 ∨ t=4 ∨ t=5) ∧ sourceBound k a ∧ sourceBound k b) ∨
 ((t=6 ∨ t=7) ∧ b=0 ∧ sourceBound (k+1) a) := by
 rw [sourceBound]
 simp only [sourceNode_ne_zero hp, dite_false, sourceNode_tag ht,
   sourceNode_payload ht, sourceUnpair_pair, Prod.fst, Prod.snd]

theorem sourceBound_encode (p : Formula) (k : Nat) :
 sourceBound k (encodeFormula p) ↔ Bound p k := by
 induction p generalizing k <;> simp only [encodeFormula,Bound]
 · exact sourceBound_zero k
 all_goals rw [sourceBound_node _ _ _ _ (by decide) (by decide)]
 all_goals simp_all

end ZFR
