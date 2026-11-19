module
public import ModelNativeCopyHSteps
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativeCopyH
open ZF207.NativeSource ZFR.ArithmeticRepresentation ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def drainTerminates (base:Nat) (ρ:Nat→M) (n:M) : Prop := ∀l x:M,
 nativeReaches (drainState base ρ 0 n l x) (drainState base ρ 4 0 (l+n) (x+n))
noncomputable def drainFormula (base:Nat) : ArithmeticSemiformula Nat 1 :=
 “n. ∀l, ∀x, ∀initial, ∀hist, ∀head,
 (!nativeRunFormula initial hist ∧ !listHeadGraph head hist ∧
 !stateGraph head ↑base &0 &1 l &3 &4 &5 &6 n x) →
 ∃out, ∃last, !nativeRunFormula initial out ∧ !listHeadGraph last out ∧
 !stateGraph last ↑(base+4) &0 &1 (l+n) &3 &4 &5 &6 0 (x+n)”
lemma drainFormula_eval (base:Nat) (ρ:Nat→M) (n:M) : (drainFormula base).Eval ![n] ρ ↔ drainTerminates base ρ n := by
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [drainFormula,drainTerminates,nativeReaches,drainState,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,nativeRunFormula_eval,ruleHead_defined.iff,stateGraph_eval,numeral_eq_natCast]
noncomputable def drain_certificate (base:Nat) (ρ:Nat→M) : FormulaCertificate ρ 1 (fun v=>drainTerminates base ρ (v 0)) := by
 refine ⟨drainFormula base,?_⟩
 intro v
 have hv:v=![v 0] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 rw [hv]; exact (drainFormula_eval base ρ (v 0)).symm
theorem drain_terminates {base:Nat} (hb:Bound base) (ρ:Nat→M) : ∀n:M,drainTerminates base ρ n := by
 apply (drain_certificate base ρ).induction
 · change drainTerminates base ρ 0
   intro l x
   change nativeReaches _ (drainState base ρ 4 0 (l+0) (x+0))
   rw [add_zero,add_zero]
   exact nativeReaches_step (drain_step27_zero hb ρ 0 l x)
 · intro n ih
   change drainTerminates base ρ n at ih
   change drainTerminates base ρ (n+1)
   intro l x
   have hr:=nativeReaches_trans (nativeReaches_step (drain_step27_dec hb ρ n l x))
    (nativeReaches_trans (nativeReaches_step (drain_step28_inc hb ρ n l x))
    (nativeReaches_trans (nativeReaches_step (drain_step29_inc hb ρ n (l+1) x))
    (nativeReaches_step (drain_step30_jump hb ρ n (l+1) (x+1)))))
   have ht:=ih (l+1) (x+1)
   change nativeReaches _ (drainState base ρ 4 0 ((l+1)+n) ((x+1)+n)) at ht
   have hl:(l+1)+n=l+(n+1):=by ac_rfl
   have hx:(x+1)+n=x+(n+1):=by ac_rfl
   rw [hl,hx] at ht
   exact nativeReaches_trans hr ht
end ZF207.NativeCopyH
