module
public import ModelNativeGuardFormula
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativeGuard
open ZF207.NativeSource ZFR.ArithmeticRepresentation ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
theorem clearX_terminates (ρ:Nat→M) : ∀x:M,clearX ρ x := by
 apply (clearX_certificate ρ).induction
 · exact nativeReaches_trans (nativeReaches_step (step7_zero ρ 0 0)) (nativeReaches_step (step9 ρ 0 0))
 · intro x ih
   change clearX ρ x at ih
   change clearX ρ (x+1)
   exact nativeReaches_trans (nativeReaches_step (step7_dec ρ 0 x))
    (nativeReaches_trans (nativeReaches_step (step8 ρ 0 x))
    (nativeReaches_trans (nativeReaches_step (step5_zero ρ 0 x)) ih))
theorem clearH_terminates (ρ:Nat→M) : ∀h:M,clearH ρ h := by
 apply (clearH_certificate ρ).induction
 · intro x
   exact nativeReaches_trans (nativeReaches_step (step5_zero ρ 0 x)) (clearX_terminates ρ x)
 · intro h ih
   change clearH ρ h at ih
   change clearH ρ (h+1)
   intro x
   exact nativeReaches_trans (nativeReaches_step (step5_dec ρ h x))
    (nativeReaches_trans (nativeReaches_step (step6 ρ h x)) (ih x))
theorem native_guard (ρ:Nat→M) : ∀h:M,guardResult ρ h := by
 apply (guardResult_certificate ρ).induction
 · change guardResult ρ 0
   intro x
   constructor
   · intro hx; subst x
     exact nativeReaches_trans (nativeReaches_step (step0_zero ρ 0 0)) (nativeReaches_step (step4_zero ρ 0 0))
   · intro hx
     have hp:0<x:=pos_iff_ne_zero.mpr (Ne.symm hx)
     have he:modelPredecessor x+1=x:=modelPredecessor_of_pos x hp
     rw [←he]
     exact nativeReaches_trans (nativeReaches_step (step0_zero ρ 0 _))
      (nativeReaches_trans (nativeReaches_step (step4_dec ρ 0 _)) (clearH_terminates ρ 0 _))
 · intro h ih
   change guardResult ρ h at ih
   change guardResult ρ (h+1)
   intro x
   by_cases hz:x=0
   · subst x
     constructor
     · intro he; exact False.elim ((by simp : h+1≠(0:M)) he)
     · intro _
       exact nativeReaches_trans (nativeReaches_step (step0_dec ρ h 0))
        (nativeReaches_trans (nativeReaches_step (step1_zero ρ h 0))
        (nativeReaches_trans (nativeReaches_step (step3 ρ h 0)) (clearH_terminates ρ h 0)))
   · have hp:0<x:=pos_iff_ne_zero.mpr hz
     have he:modelPredecessor x+1=x:=modelPredecessor_of_pos x hp
     rw [←he]
     have hprefix:=nativeReaches_trans (nativeReaches_step (step0_dec ρ h (modelPredecessor x+1)))
      (nativeReaches_trans (nativeReaches_step (step1_dec ρ h (modelPredecessor x)))
      (nativeReaches_step (step2 ρ h (modelPredecessor x))))
     constructor
     · intro heq
       exact nativeReaches_trans hprefix ((ih _).1 (add_right_cancel heq))
     · intro hne
       exact nativeReaches_trans hprefix ((ih _).2 (by intro e;exact hne (congrArg (fun z:M=>z+1) e)))
lemma native_guard_equal (ρ:Nat→M) (h x:M) (he:h=x) :
 nativeReaches (guardState ρ 0 h x) (guardState ρ 10 0 0) := (native_guard ρ h x).1 he
lemma native_guard_unequal (ρ:Nat→M) (h x:M) (he:h≠x) :
 nativeReaches (guardState ρ 0 h x) (guardState ρ 11 0 0) := (native_guard ρ h x).2 he
end ZF207.NativeGuard
