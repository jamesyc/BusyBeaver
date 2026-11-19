module
public import ExactContextWfEquations
public import ExactSourceWfNat
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation

lemma contextWf_cons_nat (a b : Nat) : sourceContextWf (C207Soundness.cantor a b+1) ↔
 sourceWf a ∧ sourceContextWf b := by
 simp [sourceContextWf,sourceMember,decodeSourceList_cons]

lemma modelSourceContextWf_nat (n : Nat) : modelSourceContextWf n ↔ sourceContextWf n := by
 induction n using Nat.strong_induction_on with
 | h n ih =>
   by_cases hn : n=0
   · subst n
     have h : sourceContextWf 0 := by simp [sourceContextWf,sourceMember,decodeSourceList_zero]
     exact iff_of_true modelSourceContextWf_zero h
   have hp : 0<n := by omega
   have he := (modelList_reconstruct n hp).symm
   have he' : n=C207Soundness.cantor (modelListHead n) (modelListTail n)+1 := by
     simpa only [modelListCons,modelCantor_nat] using he
   have h := modelSourceContextWf_cons (modelListHead n) (modelListTail n)
   rw [←he,modelSourceWf_nat,ih _ (modelListTail_lt n hp)] at h
   have hcons := contextWf_cons_nat (modelListHead n) (modelListTail n)
   rw [←he'] at hcons
   exact h.trans hcons.symm

end ZFR.ArithmeticRepresentation
