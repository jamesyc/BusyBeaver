module
public import ZF192Support.Execution.Registers.Arithmetic.CompareFormula
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.NativeCompare
open ZF192Support.NativeSource ZFR.ArithmeticRepresentation ZF192Support.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable {base unequal : Nat} (bound : Bound base unequal)
include bound

theorem clearX_terminates (ρ:Nat→M) : ∀x:M,clearX base unequal ρ x := by
 apply (clearX_certificate base unequal ρ).induction
 · exact nativeReaches_trans (nativeReaches_step (step7_zero bound ρ 0 0)) (nativeReaches_step (step9 bound ρ 0 0))
 · intro x ih
   change clearX base unequal ρ x at ih
   change clearX base unequal ρ (x+1)
   exact nativeReaches_trans (nativeReaches_step (step7_dec bound ρ 0 x))
    (nativeReaches_trans (nativeReaches_step (step8 bound ρ 0 x))
    (nativeReaches_trans (nativeReaches_step (step5_zero bound ρ 0 x)) ih))
theorem clearH_terminates (ρ:Nat→M) : ∀h:M,clearH base unequal ρ h := by
 apply (clearH_certificate base unequal ρ).induction
 · intro x
   exact nativeReaches_trans (nativeReaches_step (step5_zero bound ρ 0 x)) (clearX_terminates bound ρ x)
 · intro h ih
   change clearH base unequal ρ h at ih
   change clearH base unequal ρ (h+1)
   intro x
   exact nativeReaches_trans (nativeReaches_step (step5_dec bound ρ h x))
    (nativeReaches_trans (nativeReaches_step (step6 bound ρ h x)) (ih x))
theorem native_guard (ρ:Nat→M) : ∀h:M,guardResult base unequal ρ h := by
 apply (guardResult_certificate base unequal ρ).induction
 · change guardResult base unequal ρ 0
   intro x
   constructor
   · intro hx; subst x
     exact nativeReaches_trans (nativeReaches_step (step0_zero bound ρ 0 0)) (nativeReaches_step (step4_zero bound ρ 0 0))
   · intro hx
     have hp:0<x:=pos_iff_ne_zero.mpr (Ne.symm hx)
     have he:modelPredecessor x+1=x:=modelPredecessor_of_pos x hp
     rw [←he]
     exact nativeReaches_trans (nativeReaches_step (step0_zero bound ρ 0 _))
      (nativeReaches_trans (nativeReaches_step (step4_dec bound ρ 0 _)) (clearH_terminates bound ρ 0 _))
 · intro h ih
   change guardResult base unequal ρ h at ih
   change guardResult base unequal ρ (h+1)
   intro x
   by_cases hz:x=0
   · subst x
     constructor
     · intro he; exact False.elim ((by simp : h+1≠(0:M)) he)
     · intro _
       exact nativeReaches_trans (nativeReaches_step (step0_dec bound ρ h 0))
        (nativeReaches_trans (nativeReaches_step (step1_zero bound ρ h 0))
        (nativeReaches_trans (nativeReaches_step (step3 bound ρ h 0)) (clearH_terminates bound ρ h 0)))
   · have hp:0<x:=pos_iff_ne_zero.mpr hz
     have he:modelPredecessor x+1=x:=modelPredecessor_of_pos x hp
     rw [←he]
     have hprefix:=nativeReaches_trans (nativeReaches_step (step0_dec bound ρ h (modelPredecessor x+1)))
      (nativeReaches_trans (nativeReaches_step (step1_dec bound ρ h (modelPredecessor x)))
      (nativeReaches_step (step2 bound ρ h (modelPredecessor x))))
     constructor
     · intro heq
       exact nativeReaches_trans hprefix ((ih _).1 (add_right_cancel heq))
     · intro hne
       exact nativeReaches_trans hprefix ((ih _).2 (by intro e;exact hne (congrArg (fun z:M=>z+1) e)))
lemma native_guard_equal (ρ:Nat→M) (h x:M) (he:h=x) :
 nativeReaches (guardState ρ (base : M) h x) (guardState ρ ((base + 10 : Nat) : M) 0 0) := (native_guard bound ρ h x).1 he
lemma native_guard_unequal (ρ:Nat→M) (h x:M) (he:h≠x) :
 nativeReaches (guardState ρ (base : M) h x) (guardState ρ (unequal : M) 0 0) := (native_guard bound ρ h x).2 he
end ZF192Support.NativeCompare
