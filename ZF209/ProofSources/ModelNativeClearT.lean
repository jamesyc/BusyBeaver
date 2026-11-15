module
public import ModelNativeMPGuard
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.NativeClearT
open ZF209.NativeSource ZFR.ArithmeticRepresentation ZF209.MM0ModelPeano M209.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
structure Bound (base:Nat) : Prop where
 range : base+2<4341
 row0 : program base=some (.dec 2 (base+2) (base+1))
 row1 : program (base+1)=some (.jump base)
noncomputable def cfg (ρ:Nat→M) (pc t:M) : NativeSource.State M :=
 ⟨pc,![ρ 0,ρ 1,t,ρ 3,ρ 4,ρ 5,ρ 6,ρ 7,ρ 8]⟩
lemma step_zero {b:Nat} (hb:Bound b) (ρ:Nat→M) : programStep (cfg ρ b 0) (cfg ρ (b+2:Nat) 0) := by
 refine ⟨b,by have h:=hb.range;omega,rfl,.dec 2 (b+2) (b+1),hb.row0,?_⟩
 simp [NativeSource.execute,cfg,registerIndex]
lemma step_dec {b:Nat} (hb:Bound b) (ρ:Nat→M) (t:M) : programStep (cfg ρ b (t+1)) (cfg ρ (b+1:Nat) t) := by
 refine ⟨b,by have h:=hb.range;omega,rfl,.dec 2 (b+2) (b+1),hb.row0,?_⟩
 unfold NativeSource.execute
 dsimp only
 rw [if_neg (show (cfg ρ b (t+1)).registers (registerIndex 2)≠0 from by change t+1≠0;simp)]
 congr 2
 funext j
 rcases j with ⟨j,hj⟩
 have hh:j=0∨j=1∨j=2∨j=3∨j=4∨j=5∨j=6∨j=7∨j=8 := by omega
 rcases hh with h0|h1|h2|h3|h4|h5|h6|h7|h8 <;> subst j <;> simp [cfg,modelPredecessor_succ]
lemma step_jump {b:Nat} (hb:Bound b) (ρ:Nat→M) (t:M) : programStep (cfg ρ (b+1:Nat) t) (cfg ρ b t) := by
 refine ⟨b+1,by have h:=hb.range;omega,rfl,.jump b,hb.row1,?_⟩
 simp [NativeSource.execute,cfg]
noncomputable def reachesFormula : ArithmeticSemiformula Nat 4 :=
 “pc t q u. ∀initial,∀hist,∀head,
 (!nativeRunFormula initial hist ∧ !listHeadGraph head hist ∧ !stateGraph head pc &0 &1 t &3 &4 &5 &6 &7 &8) →
 ∃out,∃last,!nativeRunFormula initial out ∧ !listHeadGraph last out ∧ !stateGraph last q &0 &1 u &3 &4 &5 &6 &7 &8”
lemma reachesFormula_eval (ρ:Nat→M) (pc t q u:M) :
 reachesFormula.Eval ![pc,t,q,u] ρ ↔ nativeReaches (cfg ρ pc t) (cfg ρ q u) := by
 have hv(z:M):(fun _:Fin 1=>z)=![z]:=by funext i;have h:i=0:=Subsingleton.elim _ _;subst i;rfl
 simp [reachesFormula,nativeReaches,cfg,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,nativeRunFormula_eval,ruleHead_defined.iff,stateGraph_eval]
noncomputable def certificate (b:Nat) (ρ:Nat→M) : FormulaCertificate ρ 1
 (fun v=>nativeReaches (cfg ρ b (v 0)) (cfg ρ (b+2:Nat) 0)) := by
 refine ⟨“t. !reachesFormula ↑b t ↑(b+2) 0”,?_⟩
 intro v
 have hv(z:M):(fun _:Fin 1=>z)=![z]:=by funext i;have h:i=0:=Subsingleton.elim _ _;subst i;rfl
 simp [Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,hv,reachesFormula_eval,numeral_eq_natCast]
theorem clear {b:Nat} (hb:Bound b) (ρ:Nat→M) : ∀t:M,nativeReaches (cfg ρ b t) (cfg ρ (b+2:Nat) 0) := by
 apply (certificate b ρ).induction
 · exact nativeReaches_step (step_zero hb ρ)
 · intro t ih
   exact nativeReaches_trans (nativeReaches_step (step_dec hb ρ t))
    (nativeReaches_trans (nativeReaches_step (step_jump hb ρ t)) ih)
end ZF209.NativeClearT
