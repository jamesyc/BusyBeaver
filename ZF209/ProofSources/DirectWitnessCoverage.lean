module
public import ExecutableZFProof
public import Mathlib.Data.Nat.Init
@[expose] public section
namespace RosserDirect.WitnessCoverage
open ZFR ZFR.ExecutableZF C209Soundness
theorem bounded_code_is_formula (n k : Nat) (hb : sourceBound k n) :
 ∃ p : ZFR.Formula, encodeFormula p = n ∧ Bound p k := by
 induction n using Nat.strong_induction_on generalizing k with
 | h n ih =>
   by_cases hn : n = 0
   · subst n; exact ⟨.bot,rfl,trivial⟩
   have hsmall : n / 8 < n := Nat.div_lt_self (by omega) (by omega)
   have ha : (unpair (n/8)).1 < n := Nat.lt_of_le_of_lt (unpair_left_le _) hsmall
   have hc : (unpair (n/8)).2 < n := Nat.lt_of_le_of_lt (unpair_right_le _) hsmall
   have rebuild : sourceNode (n%8) (unpair (n/8)).1 (unpair (n/8)).2 = n := by
     unfold sourceNode
     rw [unpair_spec]
     omega
   rw [sourceBound] at hb
   simp only [hn,dite_false] at hb
   rcases hb with ⟨htag,hx,hy⟩ | ⟨htag,hx,hy⟩ | ⟨htag,hy,hx⟩
   · rcases htag with ht | ht
     · refine ⟨.mem _ _,?_,hx,hy⟩
       simpa [encodeFormula,ht] using rebuild
     · refine ⟨.eq _ _,?_,hx,hy⟩
       simpa [encodeFormula,ht] using rebuild
   · obtain ⟨a,hea,hba⟩ := ih _ ha k hx
     obtain ⟨b,heb,hbb⟩ := ih _ hc k hy
     rcases htag with ht | ht | ht
     · refine ⟨.and a b,?_,hba,hbb⟩
       simpa [encodeFormula,hea,heb,ht] using rebuild
     · refine ⟨.or a b,?_,hba,hbb⟩
       simpa [encodeFormula,hea,heb,ht] using rebuild
     · refine ⟨.imp a b,?_,hba,hbb⟩
       simpa [encodeFormula,hea,heb,ht] using rebuild
   · obtain ⟨a,hea,hba⟩ := ih _ ha (k+1) hx
     rcases htag with ht | ht
     · refine ⟨.all a,?_,hba⟩
       simpa [encodeFormula,hea,hy,ht] using rebuild
     · refine ⟨.ex a,?_,hba⟩
       simpa [encodeFormula,hea,hy,ht] using rebuild

end RosserDirect.WitnessCoverage
