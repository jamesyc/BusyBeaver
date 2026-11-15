module
public import SourceNumericDecode
@[expose] public section
namespace ZFR.NumericDecode
open C209Soundness
/-- Induction over the ACTUAL numeric Peano trace, not an assumed typed image. -/
theorem numeric_trace_induction (P : Nat → Prop)
 (rules : ∀ r xs, (∀ p, sourceMember p xs → P p) → sourceFullRules r xs → P r)
 (n : Nat) (h : numericTraceValid sourceFullRules n) :
 ∀ r, sourceMember r n → P r := by
 induction n using Nat.strong_induction_on with
 | h n ih =>
   by_cases hn : n=0
   · subst n; intro r hr; simp [sourceMember,decodeSourceList_zero] at hr
   have he : cantor (unpair (n-1)).1 (unpair (n-1)).2 + 1=n := by rw [unpair_spec]; omega
   rw [← he,numericTraceValid_cons] at h
   have ht := ih _ (Nat.lt_of_le_of_lt (unpair_right_le _) (by omega)) h.1
   intro r hr
   rw [← he] at hr
   simp only [sourceMember,decodeSourceList_cons,List.mem_cons] at hr
   rcases hr with hr | hr
   · subst r; exact rules _ _ ht h.2
   · exact ht r hr
end ZFR.NumericDecode
