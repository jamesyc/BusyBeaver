module
public import ModelNativeFetchSteps
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativeFetch
open ZF207.NativeSource ZFR.ArithmeticRepresentation ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def drainTerminates (ρ:Nat→M) (n:M) : Prop := ∀l x:M,
 nativeReaches (fetchState ρ 27 n l x) (fetchState ρ 31 0 (l+n) (x+n))
noncomputable def drainFormula : ArithmeticSemiformula Nat 1 :=
 “n. ∀l, ∀x, ∀initial, ∀hist, ∀head,
 (!nativeRunFormula initial hist ∧ !listHeadGraph head hist ∧
 !stateGraph head 27 &0 l &2 &3 &4 &5 n &7 x) →
 ∃out, ∃last, !nativeRunFormula initial out ∧ !listHeadGraph last out ∧
 !stateGraph last 31 &0 (l+n) &2 &3 &4 &5 0 &7 (x+n)”
lemma drainFormula_eval (ρ:Nat→M) (n:M) : drainFormula.Eval ![n] ρ ↔ drainTerminates ρ n := by
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [drainFormula,drainTerminates,nativeReaches,fetchState,Semiformula.eval_rew,Function.comp_def,
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
   change nativeReaches _ (fetchState ρ 31 0 (l+0) (x+0))
   rw [add_zero,add_zero]
   exact nativeReaches_step (fetch_step27_zero ρ 0 l x)
 · intro n ih
   change drainTerminates ρ n at ih
   change drainTerminates ρ (n+1)
   intro l x
   have hr:=nativeReaches_trans (nativeReaches_step (fetch_step27_dec ρ n l x))
    (nativeReaches_trans (nativeReaches_step (fetch_step28_inc ρ n l x))
    (nativeReaches_trans (nativeReaches_step (fetch_step29_inc ρ n (l+1) x))
    (nativeReaches_step (fetch_step30_jump ρ n (l+1) (x+1)))))
   have ht:=ih (l+1) (x+1)
   change nativeReaches _ (fetchState ρ 31 0 ((l+1)+n) ((x+1)+n)) at ht
   have hl:(l+1)+n=l+(n+1):=by ac_rfl
   have hx:(x+1)+n=x+(n+1):=by ac_rfl
   rw [hl,hx] at ht
   exact nativeReaches_trans hr ht
def restoreTerminates (ρ:Nat→M) (x:M) : Prop := ∀n l:M,
 nativeReaches (fetchState ρ 31 n l x) (fetchState ρ 34 (n+x+1) l 0)
noncomputable def restoreFormula : ArithmeticSemiformula Nat 1 :=
 “x. ∀n, ∀l, ∀initial, ∀hist, ∀head,
 (!nativeRunFormula initial hist ∧ !listHeadGraph head hist ∧
 !stateGraph head 31 &0 l &2 &3 &4 &5 n &7 x) →
 ∃out, ∃last, !nativeRunFormula initial out ∧ !listHeadGraph last out ∧
 !stateGraph last 34 &0 l &2 &3 &4 &5 (n+x+1) &7 0”
lemma restoreFormula_eval (ρ:Nat→M) (x:M) : restoreFormula.Eval ![x] ρ ↔ restoreTerminates ρ x := by
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [restoreFormula,restoreTerminates,nativeReaches,fetchState,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,nativeRunFormula_eval,ruleHead_defined.iff,stateGraph_eval,numeral_eq_natCast]
noncomputable def restore_certificate (ρ:Nat→M) : FormulaCertificate ρ 1 (fun v=>restoreTerminates ρ (v 0)) := by
 refine ⟨restoreFormula,?_⟩
 intro v
 have hv:v=![v 0] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 rw [hv]; exact (restoreFormula_eval ρ (v 0)).symm
theorem restore_terminates (ρ:Nat→M) : ∀x:M,restoreTerminates ρ x := by
 apply (restore_certificate ρ).induction
 · change restoreTerminates ρ 0
   intro n l
   change nativeReaches _ (fetchState ρ 34 (n+0+1) l 0)
   rw [add_zero]
   exact nativeReaches_trans (nativeReaches_step (fetch_step31_inc ρ n l 0))
    (nativeReaches_step (fetch_step32_zero ρ (n+1) l 0))
 · intro x ih
   change restoreTerminates ρ x at ih
   change restoreTerminates ρ (x+1)
   intro n l
   have hr:=nativeReaches_trans (nativeReaches_step (fetch_step31_inc ρ n l (x+1)))
    (nativeReaches_trans (nativeReaches_step (fetch_step32_dec ρ (n+1) l x))
    (nativeReaches_step (fetch_step33_jump ρ (n+1) l x)))
   have ht:=ih (n+1) l
   change nativeReaches _ (fetchState ρ 34 ((n+1)+x+1) l 0) at ht
   have hn:(n+1)+x+1=n+(x+1)+1:=by ac_rfl
   rw [hn] at ht
   exact nativeReaches_trans hr ht
end ZF207.NativeFetch
