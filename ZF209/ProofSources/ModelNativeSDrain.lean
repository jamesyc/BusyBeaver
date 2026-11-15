module
public import ModelNativeSDrainSteps
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativeSDrain
open ZF209.NativeSource ZFR.ArithmeticRepresentation ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def drainTerminates (ρ:Nat→M) (n:M) : Prop := ∀l x:M,
 nativeReaches (drainState ρ 4332 n l x) (drainState ρ 4336 0 (l+n) (x+n))
noncomputable def drainFormula : ArithmeticSemiformula Nat 1 :=
 “n. ∀l, ∀x, ∀initial, ∀hist, ∀head,
 (!nativeRunFormula initial hist ∧ !listHeadGraph head hist ∧
 !stateGraph head 4332 &0 &1 l &3 &4 &5 &6 n x) →
 ∃out, ∃last, !nativeRunFormula initial out ∧ !listHeadGraph last out ∧
 !stateGraph last 4336 &0 &1 (l+n) &3 &4 &5 &6 0 (x+n)”
lemma drainFormula_eval (ρ:Nat→M) (n:M) : drainFormula.Eval ![n] ρ ↔ drainTerminates ρ n := by
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [drainFormula,drainTerminates,nativeReaches,drainState,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,nativeRunFormula_eval,ruleHead_defined.iff,stateGraph_eval,numeral_eq_natCast]
noncomputable def drain_certificate (ρ:Nat→M) : FormulaCertificate ρ 1 (fun v=>drainTerminates ρ (v 0)) := by
 refine ⟨drainFormula,?_⟩
 intro v
 have hv:v=![v 0] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 rw [hv]; exact (drainFormula_eval ρ (v 0)).symm
theorem drain_terminates (ρ:Nat→M) : ∀n:M,drainTerminates ρ n := by
 apply (drain_certificate ρ).induction
 · change drainTerminates ρ 0
   intro l x
   change nativeReaches _ (drainState ρ 4336 0 (l+0) (x+0))
   rw [add_zero,add_zero]
   exact nativeReaches_step (drain_step27_zero ρ 0 l x)
 · intro n ih
   change drainTerminates ρ n at ih
   change drainTerminates ρ (n+1)
   intro l x
   have hr:=nativeReaches_trans (nativeReaches_step (drain_step27_dec ρ n l x))
    (nativeReaches_trans (nativeReaches_step (drain_step28_inc ρ n l x))
    (nativeReaches_trans (nativeReaches_step (drain_step29_inc ρ n (l+1) x))
    (nativeReaches_step (drain_step30_jump ρ n (l+1) (x+1)))))
   have ht:=ih (l+1) (x+1)
   change nativeReaches _ (drainState ρ 4336 0 ((l+1)+n) ((x+1)+n)) at ht
   have hl:(l+1)+n=l+(n+1):=by ac_rfl
   have hx:(x+1)+n=x+(n+1):=by ac_rfl
   rw [hl,hx] at ht
   exact nativeReaches_trans hr ht
end ZF209.NativeSDrain
