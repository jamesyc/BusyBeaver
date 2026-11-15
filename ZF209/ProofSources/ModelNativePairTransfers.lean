module
public import ModelNativePairSteps
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativePair
open ZF209.NativeSource ZFR.ArithmeticRepresentation ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def drainT (offset:Nat) (ρ:Nat→M) (t:M) : Prop := ∀w x y:M,
 nativeReaches (pairState offset ρ 0 t w x y) (pairState offset ρ 4 0 w (x+t) (y+t))
noncomputable def drainTFormula (offset:Nat) : ArithmeticSemiformula Nat 1 :=
 “t. ∀w, ∀x, ∀y, ∀initial, ∀hist, ∀head,
 (!nativeRunFormula initial hist ∧ !listHeadGraph head hist ∧
 !stateGraph head ↑offset w &1 t &3 &4 y &6 &7 x) →
 ∃out, ∃last, !nativeRunFormula initial out ∧ !listHeadGraph last out ∧
 !stateGraph last ↑(offset+4) w &1 0 &3 &4 (y+t) &6 &7 (x+t)”
lemma drainTFormula_eval (offset:Nat) (ρ:Nat→M) (t:M) : (drainTFormula offset).Eval ![t] ρ ↔ drainT offset ρ t := by
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [drainTFormula,drainT,nativeReaches,pairState,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,nativeRunFormula_eval,ruleHead_defined.iff,stateGraph_eval,numeral_eq_natCast]
noncomputable def drainT_certificate (offset:Nat) (ρ:Nat→M) : FormulaCertificate ρ 1 (fun v=>drainT offset ρ (v 0)) := by
 refine ⟨drainTFormula offset,?_⟩
 intro v
 have hv:v=![v 0] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 rw [hv]; exact (drainTFormula_eval offset ρ (v 0)).symm
theorem drainT_terminates {offset:Nat} (hb:Bound offset) (ρ:Nat→M) : ∀t:M,drainT offset ρ t := by
 apply (drainT_certificate offset ρ).induction
 · change drainT offset ρ 0
   intro w x y
   change nativeReaches _ (pairState offset ρ 4 0 w (x+0) (y+0))
   rw [add_zero,add_zero]
   exact nativeReaches_step (pair_step0_zero hb ρ 0 w x y)
 · intro t ih
   change drainT offset ρ t at ih
   change drainT offset ρ (t+1)
   intro w x y
   have hr:=nativeReaches_trans (nativeReaches_step (pair_step0_dec hb ρ t w x y))
    (nativeReaches_trans (nativeReaches_step (pair_step1_inc hb ρ t w x y))
    (nativeReaches_trans (nativeReaches_step (pair_step2_inc hb ρ t w x (y+1)))
    (nativeReaches_step (pair_step3_jump hb ρ t w (x+1) (y+1)))))
   have ht:=ih w (x+1) (y+1)
   change nativeReaches _ (pairState offset ρ 4 0 w ((x+1)+t) ((y+1)+t)) at ht
   have hx:(x+1)+t=x+(t+1):=by ac_rfl
   have hy:(y+1)+t=y+(t+1):=by ac_rfl
   rw [hx,hy] at ht
   exact nativeReaches_trans hr ht
def drainX (offset:Nat) (ρ:Nat→M) (x:M) : Prop := ∀t w y:M,
 nativeReaches (pairState offset ρ 6 t w x y) (pairState offset ρ 9 (t+x) w 0 y)
noncomputable def drainXFormula (offset:Nat) : ArithmeticSemiformula Nat 1 :=
 “x. ∀t, ∀w, ∀y, ∀initial, ∀hist, ∀head,
 (!nativeRunFormula initial hist ∧ !listHeadGraph head hist ∧
 !stateGraph head ↑(offset+6) w &1 t &3 &4 y &6 &7 x) →
 ∃out, ∃last, !nativeRunFormula initial out ∧ !listHeadGraph last out ∧
 !stateGraph last ↑(offset+9) w &1 (t+x) &3 &4 y &6 &7 0”
lemma drainXFormula_eval (offset:Nat) (ρ:Nat→M) (x:M) : (drainXFormula offset).Eval ![x] ρ ↔ drainX offset ρ x := by
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [drainXFormula,drainX,nativeReaches,pairState,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,nativeRunFormula_eval,ruleHead_defined.iff,stateGraph_eval,numeral_eq_natCast]
noncomputable def drainX_certificate (offset:Nat) (ρ:Nat→M) : FormulaCertificate ρ 1 (fun v=>drainX offset ρ (v 0)) := by
 refine ⟨drainXFormula offset,?_⟩
 intro v
 have hv:v=![v 0] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 rw [hv]; exact (drainXFormula_eval offset ρ (v 0)).symm
theorem drainX_terminates {offset:Nat} (hb:Bound offset) (ρ:Nat→M) : ∀x:M,drainX offset ρ x := by
 apply (drainX_certificate offset ρ).induction
 · change drainX offset ρ 0
   intro t w y
   change nativeReaches _ (pairState offset ρ 9 (t+0) w 0 y)
   rw [add_zero]
   exact nativeReaches_step (pair_step6_zero hb ρ t w 0 y)
 · intro x ih
   change drainX offset ρ x at ih
   change drainX offset ρ (x+1)
   intro t w y
   have hr:=nativeReaches_trans (nativeReaches_step (pair_step6_dec hb ρ t w x y))
    (nativeReaches_trans (nativeReaches_step (pair_step7_inc hb ρ t w x y))
    (nativeReaches_step (pair_step8_jump hb ρ (t+1) w x y)))
   have ht:=ih (t+1) w y
   change nativeReaches _ (pairState offset ρ 9 ((t+1)+x) w 0 y) at ht
   have he:(t+1)+x=t+(x+1):=by ac_rfl
   rw [he] at ht
   exact nativeReaches_trans hr ht
end ZF209.NativePair
