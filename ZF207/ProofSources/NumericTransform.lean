module
public import NumericSource
@[expose] public section
namespace ZFR
open C207Soundness

/-- Numeric recursion of sfRenameBody/sfShiftBody/sfSubstBody. Invalid tags and
nonzero quantifier right payloads return zero, exactly as in the MM0 bodies. -/
def sourceTransform (f : Nat → Nat → Nat) (d n : Nat) : Nat :=
 if h : n = 0 then 0 else
 let p := unpair (n/8)
 let t := n%8
 if t=1 then sourceNode 1 (f d p.1) (f d p.2)
 else if t=2 then sourceNode 2 (f d p.1) (f d p.2)
 else if t=3 then sourceNode 3 (sourceTransform f d p.1) (sourceTransform f d p.2)
 else if t=4 then sourceNode 4 (sourceTransform f d p.1) (sourceTransform f d p.2)
 else if t=5 then sourceNode 5 (sourceTransform f d p.1) (sourceTransform f d p.2)
 else if t=6 ∧ p.2=0 then sourceNode 6 (sourceTransform f (d+1) p.1) 0
 else if t=7 ∧ p.2=0 then sourceNode 7 (sourceTransform f (d+1) p.1) 0
 else 0
termination_by n
decreasing_by
 all_goals
   have hq : n/8 < n := Nat.div_lt_self (by omega) (by omega)
   have ha := unpair_left_le (n/8)
   have hb := unpair_right_le (n/8)
   omega

theorem sourceTransform_encode (f : Nat → Nat → Nat)
 (hl : ∀ d, f (d+1) = lift (f d)) (d : Nat) (a : Formula) :
 sourceTransform f d (encodeFormula a) = encodeFormula (rename (f d) a) := by
 induction a generalizing d with
 | bot => rw [encodeFormula, sourceTransform]; rfl
 | mem i j =>
   rw [encodeFormula, sourceTransform]
   simp [sourceNode_ne_zero, sourceNode_tag, sourceNode_payload, sourceUnpair_pair, rename, encodeFormula]
 | eq i j =>
   rw [encodeFormula, sourceTransform]
   simp [sourceNode_ne_zero, sourceNode_tag, sourceNode_payload, sourceUnpair_pair, rename, encodeFormula]
 | and a b ia ib =>
   rw [encodeFormula, sourceTransform]
   simp [sourceNode_ne_zero, sourceNode_tag, sourceNode_payload, sourceUnpair_pair, rename, encodeFormula, ia, ib]
 | or a b ia ib =>
   rw [encodeFormula, sourceTransform]
   simp [sourceNode_ne_zero, sourceNode_tag, sourceNode_payload, sourceUnpair_pair, rename, encodeFormula, ia, ib]
 | imp a b ia ib =>
   rw [encodeFormula, sourceTransform]
   simp [sourceNode_ne_zero, sourceNode_tag, sourceNode_payload, sourceUnpair_pair, rename, encodeFormula, ia, ib]
 | all a ia =>
   rw [encodeFormula, sourceTransform]
   simp [sourceNode_ne_zero, sourceNode_tag, sourceNode_payload, sourceUnpair_pair, rename, encodeFormula, ia, hl]
 | ex a ia =>
   rw [encodeFormula, sourceTransform]
   simp [sourceNode_ne_zero, sourceNode_tag, sourceNode_payload, sourceUnpair_pair, rename, encodeFormula, ia, hl]

def sourceRenameIndex (σ : Nat → Nat) (d i : Nat) := if i < d then i else d + σ (i-d)
def sourceShiftIndex (d i : Nat) := if i < d then i else i+1
def sourceSubstIndex (t d i : Nat) := if i < d then i else if i=d then t+d else i-1

theorem sourceRenameIndex_lift (σ : Nat → Nat) (d : Nat) :
 sourceRenameIndex σ (d+1) = lift (sourceRenameIndex σ d) := by
 funext i; cases i with
 | zero => simp [sourceRenameIndex, lift]
 | succ i =>
   simp only [sourceRenameIndex, lift]
   split <;> split <;> rename_i h h' <;> try omega
   have hs : i+1-(d+1) = i-d := by omega
   rw [hs]; omega

theorem sourceShiftIndex_lift (d : Nat) : sourceShiftIndex (d+1) = lift (sourceShiftIndex d) := by
 funext i; cases i <;> simp only [sourceShiftIndex, lift] <;> split <;> simp_all <;> omega

theorem sourceSubstIndex_lift (t d : Nat) : sourceSubstIndex t (d+1) = lift (sourceSubstIndex t d) := by
 funext i; cases i with
 | zero => simp [sourceSubstIndex, lift]
 | succ i =>
   simp only [sourceSubstIndex, lift]
   by_cases h : i < d
   · simp [h, show i+1 < d+1 by omega]
   · by_cases he : i = d
     · subst i; simp [Nat.add_assoc]
     · simp [h, he, show ¬i+1 < d+1 by omega, show i+1 ≠ d+1 by omega]
       omega

def sourceRename (σ : Nat → Nat) := sourceTransform (sourceRenameIndex σ)
def sourceShift := sourceTransform sourceShiftIndex
def sourceSubst (d t n : Nat) := sourceTransform (sourceSubstIndex t) d n

theorem sourceRename_encode (σ : Nat → Nat) (a : Formula) :
 sourceRename σ 0 (encodeFormula a) = encodeFormula (rename σ a) := by
 have h := sourceTransform_encode (sourceRenameIndex σ) (sourceRenameIndex_lift σ) 0 a
 have hi : sourceRenameIndex σ 0 = σ := by funext i; simp [sourceRenameIndex]
 simpa only [sourceRename, hi] using h

theorem sourceShift_encode (a : Formula) :
 sourceShift 0 (encodeFormula a) = encodeFormula (shift a) := by
 have h := sourceTransform_encode sourceShiftIndex sourceShiftIndex_lift 0 a
 have hi : sourceShiftIndex 0 = Nat.succ := by funext i; simp [sourceShiftIndex]
 simpa only [sourceShift, hi, shift] using h

theorem sourceSubst_encode (t : Nat) (a : Formula) :
 sourceSubst 0 t (encodeFormula a) = encodeFormula (subst t a) := by
 have hi : sourceSubstIndex t 0 = substMap t := by
   funext i; cases i <;> simp [sourceSubstIndex, substMap]
 have h := sourceTransform_encode (sourceSubstIndex t) (sourceSubstIndex_lift t) 0 a
 simpa [sourceSubst, subst, hi] using h

end ZFR
