module
public import ExactTraceFormula
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
lemma tail_zero_nat : modelListTail (0:Nat)=0 := by rw [modelListTail_nat]; rfl
lemma tailIter_zero_nat (k : Nat) : modelTailIter k (0:Nat)=0 := by
 induction k with
 | zero => exact modelTailIter_zero 0
 | succ k ih => rw [show k+1=k+1 from rfl,modelTailIter_succ,ih,tail_zero_nat]
lemma tailIter_commute_nat (k n : Nat) : modelTailIter k (modelListTail n)=modelTailIter (k+1) n := by
 induction k with
 | zero => rw [modelTailIter_zero,modelTailIter_succ,modelTailIter_zero]
 | succ k ih => rw [modelTailIter_succ,ih,modelTailIter_succ (k+1)]
lemma tailIter_stops_nat (k n : Nat) (h:n≤k) : modelTailIter k n=0 := by
 induction k generalizing n with
 | zero =>
   have hn:n=0 := by omega
   subst n
   exact modelTailIter_zero 0
 | succ k ih =>
   by_cases hn:n=0
   · subst n; exact tailIter_zero_nat _
   · rw [←tailIter_commute_nat]
     apply ih
     have hh:=modelListTail_lt n (by omega : 0<n)
     omega
lemma trace_valid_tail_nat (R : Nat → Nat → Prop) (n : Nat) (h:numericTraceValid R n) :
 numericTraceValid R (modelListTail n) := by
 by_cases hn:n=0
 · subst n; rw [tail_zero_nat]; exact h
 · rw [numericTraceValid] at h
   simp only [hn,↓reduceDIte] at h
   simpa only [modelListTail_nat] using h.1
lemma trace_valid_step_nat (R : Nat → Nat → Prop) (n : Nat) (h:numericTraceValid R n) (hn:n≠0) :
 R (modelListHead n) (modelListTail n) := by
 rw [numericTraceValid] at h
 simp only [hn,↓reduceDIte] at h
 simpa only [modelListHead_nat,modelListTail_nat] using h.2
lemma trace_valid_iter_nat (R : Nat → Nat → Prop) (n : Nat) (h:numericTraceValid R n) (k : Nat) :
 numericTraceValid R (modelTailIter k n) := by
 induction k with
 | zero => simpa only [modelTailIter_zero] using h
 | succ k ih => rw [modelTailIter_succ]; exact trace_valid_tail_nat R _ ih
lemma modelTrace_nat (R : Nat → Nat → Prop) (n : Nat) : modelTrace R n ↔ numericTraceValid R n := by
 constructor
 · intro h
   induction n using Nat.strong_induction_on with
   | h n ih =>
     by_cases hn:n=0
     · subst n; exact numericTraceValid_zero R
     · have hnpos:0<n := by omega
       have htail:modelListTail n<n := modelListTail_lt n hnpos
       have hr := h.2 0 hnpos
       simp only [modelTailIter_zero] at hr
       have hr' := hr.resolve_left hn
       have hv : modelTrace R (modelListTail n) := by
         refine ⟨tailIter_stops_nat _ _ (by rfl),?_⟩
         intro k hk
         have hkn:k+1<n := by omega
         simpa only [tailIter_commute_nat] using h.2 (k+1) hkn
       have hi := ih (modelListTail n) htail hv
       rw [numericTraceValid]
       simp only [hn,↓reduceDIte]
       simpa only [modelListHead_nat,modelListTail_nat] using And.intro hi hr'
 · intro h
   refine ⟨tailIter_stops_nat n n (by rfl),?_⟩
   intro k hk
   by_cases hz:modelTailIter k n=0
   · exact Or.inl hz
   · exact Or.inr (trace_valid_step_nat R _ (trace_valid_iter_nat R n h k) hz)
end ZFR.ArithmeticRepresentation
