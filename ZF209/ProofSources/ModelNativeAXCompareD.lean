module
public import ModelNativeAXCompareDFormula
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativeAXCompareD
open ZF209.NativeSource ZFR.ArithmeticRepresentation ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
theorem clearX_terminates (ρ:Nat→M) : ∀x:M,clearX ρ x := by
 apply (clearX_certificate ρ).induction
 · exact nativeReaches_trans (nativeReaches_step (step4216_zero ρ 0 0)) (nativeReaches_step (step4218 ρ 0 0))
 · intro x ih
   change clearX ρ x at ih
   change clearX ρ (x+1)
   exact nativeReaches_trans (nativeReaches_step (step4216_dec ρ 0 x))
    (nativeReaches_trans (nativeReaches_step (step4217 ρ 0 x))
    (nativeReaches_trans (nativeReaches_step (step4214_zero ρ 0 x)) ih))
theorem clearH_terminates (ρ:Nat→M) : ∀h:M,clearH ρ h := by
 apply (clearH_certificate ρ).induction
 · intro x
   exact nativeReaches_trans (nativeReaches_step (step4214_zero ρ 0 x)) (clearX_terminates ρ x)
 · intro h ih
   change clearH ρ h at ih
   change clearH ρ (h+1)
   intro x
   exact nativeReaches_trans (nativeReaches_step (step4214_dec ρ h x))
    (nativeReaches_trans (nativeReaches_step (step4215 ρ h x)) (ih x))
theorem native_guard (ρ:Nat→M) : ∀h:M,guardResult ρ h := by
 apply (guardResult_certificate ρ).induction
 · change guardResult ρ 0
   intro x
   constructor
   · intro hx; subst x
     exact nativeReaches_trans (nativeReaches_step (step4209_zero ρ 0 0)) (nativeReaches_step (step4213_zero ρ 0 0))
   · intro hx
     have hp:0<x:=pos_iff_ne_zero.mpr (Ne.symm hx)
     have he:modelPredecessor x+1=x:=modelPredecessor_of_pos x hp
     rw [←he]
     exact nativeReaches_trans (nativeReaches_step (step4209_zero ρ 0 _))
      (nativeReaches_trans (nativeReaches_step (step4213_dec ρ 0 _)) (clearH_terminates ρ 0 _))
 · intro h ih
   change guardResult ρ h at ih
   change guardResult ρ (h+1)
   intro x
   by_cases hz:x=0
   · subst x
     constructor
     · intro he; exact False.elim ((by simp : h+1≠(0:M)) he)
     · intro _
       exact nativeReaches_trans (nativeReaches_step (step4209_dec ρ h 0))
        (nativeReaches_trans (nativeReaches_step (step4210_zero ρ h 0))
        (nativeReaches_trans (nativeReaches_step (step4212 ρ h 0)) (clearH_terminates ρ h 0)))
   · have hp:0<x:=pos_iff_ne_zero.mpr hz
     have he:modelPredecessor x+1=x:=modelPredecessor_of_pos x hp
     rw [←he]
     have hprefix:=nativeReaches_trans (nativeReaches_step (step4209_dec ρ h (modelPredecessor x+1)))
      (nativeReaches_trans (nativeReaches_step (step4210_dec ρ h (modelPredecessor x)))
      (nativeReaches_step (step4211 ρ h (modelPredecessor x))))
     constructor
     · intro heq
       exact nativeReaches_trans hprefix ((ih _).1 (add_right_cancel heq))
     · intro hne
       exact nativeReaches_trans hprefix ((ih _).2 (by intro e;exact hne (congrArg (fun z:M=>z+1) e)))
lemma native_guard_equal (ρ:Nat→M) (h x:M) (he:h=x) :
 nativeReaches (guardState ρ 4209 h x) (guardState ρ 4219 0 0) := (native_guard ρ h x).1 he
lemma native_guard_unequal (ρ:Nat→M) (h x:M) (he:h≠x) :
 nativeReaches (guardState ρ 4209 h x) (guardState ρ 4221 0 0) := (native_guard ρ h x).2 he
end ZF209.NativeAXCompareD
