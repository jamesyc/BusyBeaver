module
public import ExactContextShiftEquations
public import ExactSourceShiftNat
public import NumericRules
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation

lemma modelSourceContextShift_nat (n : Nat) : modelSourceContextShift n=sourceContextShift n := by
 induction n using Nat.strong_induction_on with
 | h n ih =>
   by_cases hn : n=0
   · subst n
     rw [modelSourceContextShift_zero,sourceContextShift_zero]
   have hp : 0<n := by omega
   have he := (modelList_reconstruct n hp).symm
   have he' : n=sourceCons (modelListHead n) (modelListTail n) := by
     simpa only [modelListCons,modelCantor_nat,sourceCons] using he
   have h := modelSourceContextShift_cons (modelListHead n) (modelListTail n)
   rw [←he,modelSourceShift_nat,ih _ (modelListTail_lt n hp)] at h
   have hc := sourceContextShift_cons (modelListHead n) (modelListTail n)
   rw [←he'] at hc
   rw [hc]
   simpa only [modelListCons,modelCantor_nat,sourceCons] using h

end ZFR.ArithmeticRepresentation
