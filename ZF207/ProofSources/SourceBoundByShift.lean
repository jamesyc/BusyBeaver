module
public import SourceFormulaDecode
public import NumericBounds
@[expose] public section
namespace ZFR
open C207Soundness

theorem shiftIndex_fixed_iff (k i : Nat) : sourceShiftIndex k i=i ↔ i<k := by
 unfold sourceShiftIndex
 split <;> omega

theorem rename_shift_fixed_iff (a : Formula) (k : Nat) :
 rename (sourceShiftIndex k) a=a ↔ Bound a k := by
 induction a generalizing k with
 | bot => simp [rename,Bound]
 | mem i j => simp [rename,Bound,shiftIndex_fixed_iff]
 | eq i j => simp [rename,Bound,shiftIndex_fixed_iff]
 | and a b ia ib => simp [rename,Bound,ia,ib]
 | or a b ia ib => simp [rename,Bound,ia,ib]
 | imp a b ia ib => simp [rename,Bound,ia,ib]
 | all a ia => simp [rename,Bound,← sourceShiftIndex_lift,ia]
 | ex a ia => simp [rename,Bound,← sourceShiftIndex_lift,ia]

theorem bound_implies_wf (n k : Nat) (h : sourceBound k n) : sourceWf n := by
 induction n using Nat.strongRecOn generalizing k with
 | ind n ih =>
   rw [sourceBound] at h
   rw [sourceWf]
   by_cases hn : n=0
   · simp [hn]
   · simp only [hn,dite_false] at h ⊢
     have hq : n/8<n := Nat.div_lt_self (by omega) (by decide)
     have hl := unpair_left_le (n/8)
     have hr := unpair_right_le (n/8)
     rcases h with ⟨ht,_,_⟩ | ⟨ht,ha,hb⟩ | ⟨ht,hz,ha⟩
     · exact Or.inl ht
     · exact Or.inr (Or.inl ⟨ht,ih _ (by omega) k ha,ih _ (by omega) k hb⟩)
     · exact Or.inr (Or.inr ⟨ht,hz,ih _ (by omega) (k+1) ha⟩)

theorem sourceBound_iff_shift_fixed (k n : Nat) :
 sourceBound k n ↔ sourceWf n ∧ sourceShift k n=n := by
 constructor
 · intro h
   have hw := bound_implies_wf n k h
   refine ⟨hw,?_⟩
   obtain ⟨a,rfl⟩ := sourceWf_exists_formula n hw
   have ha := (sourceBound_encode a k).mp h
   have he := (rename_shift_fixed_iff a k).mpr ha
   exact (sourceTransform_encode sourceShiftIndex sourceShiftIndex_lift k a).trans (congrArg encodeFormula he)
 · rintro ⟨hw,he⟩
   obtain ⟨a,rfl⟩ := sourceWf_exists_formula n hw
   change sourceTransform sourceShiftIndex k (encodeFormula a)=encodeFormula a at he
   rw [sourceTransform_encode sourceShiftIndex sourceShiftIndex_lift] at he
   exact (sourceBound_encode a k).mpr ((rename_shift_fixed_iff a k).mp (encodeFormula_injective he))
end ZFR
