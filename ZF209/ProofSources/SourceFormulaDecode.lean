module
public import SourceVariableBounds
public import NumericTransform
@[expose] public section
namespace ZFR
open C209Soundness

theorem sourceNode_rebuild (n : Nat) :
 sourceNode (n%8) (unpair (n/8)).1 (unpair (n/8)).2 = n := by
 unfold sourceNode
 rw [unpair_spec]
 omega

theorem sourceWf_exists_formula (n : Nat) (h : sourceWf n) :
 ∃ a : Formula, encodeFormula a = n := by
 induction n using Nat.strongRecOn with
 | ind n ih =>
   by_cases hz : n=0
   · subst n; exact ⟨.bot,rfl⟩
   have hq : n/8<n := Nat.div_lt_self (by omega) (by omega)
   have hl := unpair_left_le (n/8)
   have hr := unpair_right_le (n/8)
   have rebuild := sourceNode_rebuild n
   rw [sourceWf] at h
   simp only [hz, dite_false] at h
   rcases h with (ht|ht) | ⟨ht,ha,hb⟩ | ⟨ht,hb,ha⟩
   · exact ⟨.mem (unpair (n/8)).1 (unpair (n/8)).2, by simpa [encodeFormula,ht] using rebuild⟩
   · exact ⟨.eq (unpair (n/8)).1 (unpair (n/8)).2, by simpa [encodeFormula,ht] using rebuild⟩
   · obtain ⟨a,ea⟩ := ih _ (by omega) ha
     obtain ⟨b,eb⟩ := ih _ (by omega) hb
     rcases ht with ht|ht|ht
     · exact ⟨.and a b, by simpa [encodeFormula,ea,eb,ht] using rebuild⟩
     · exact ⟨.or a b, by simpa [encodeFormula,ea,eb,ht] using rebuild⟩
     · exact ⟨.imp a b, by simpa [encodeFormula,ea,eb,ht] using rebuild⟩
   · obtain ⟨a,ea⟩ := ih _ (by omega) ha
     rcases ht with ht|ht
     · exact ⟨.all a, by simpa [encodeFormula,ea,hb,ht] using rebuild⟩
     · exact ⟨.ex a, by simpa [encodeFormula,ea,hb,ht] using rebuild⟩

end ZFR
