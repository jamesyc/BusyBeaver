module
public import ModelNativePairTransfers
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativePair
open ZF207.NativeSource ZFR.ArithmeticRepresentation ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
lemma triangle_succ (s:M) : modelCantor (s+1) 0=modelCantor s 0+s+1 := by
 symm
 apply modelCantor_unique
 rw [mul_add,mul_add,modelCantor_equation]
 simp only [add_zero,mul_zero,zero_add,←one_add_one_eq_two,mul_one,add_mul,mul_add,one_mul]
 ac_rfl
lemma pair_triangle (x t:M) : t+modelCantor (x+t) 0=modelCantor x t := by
 apply modelCantor_unique
 rw [mul_add,modelCantor_equation]
 simp only [add_zero,mul_zero]
 ac_rfl
def pairLoop (offset:Nat) (ρ:Nat→M) (s:M) : Prop := ∀w y:M,
 nativeReaches (pairState offset ρ 4 0 w s y) (pairState offset ρ 10 0 w 0 (y+modelCantor s 0))
noncomputable def pairLoopFormula (offset:Nat) : ArithmeticSemiformula Nat 1 :=
 “s. ∀w, ∀y, ∀initial, ∀hist, ∀head,
 (!nativeRunFormula initial hist ∧ !listHeadGraph head hist ∧
 !stateGraph head ↑(offset+4) w &1 0 &3 &4 y &6 &7 s) →
 ∃out, ∃last, ∃tri, !nativeRunFormula initial out ∧ !listHeadGraph last out ∧ !exactCantorGraph tri s 0 ∧
 !stateGraph last ↑(offset+10) w &1 0 &3 &4 (y+tri) &6 &7 0”
lemma pairLoopFormula_eval (offset:Nat) (ρ:Nat→M) (s:M) : (pairLoopFormula offset).Eval ![s] ρ ↔ pairLoop offset ρ s := by
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 have hc (z a b:M) : exactCantorGraph.val.Evalb ![z,a,b] ↔ z=modelCantor a b := graphValue_spec exactCantorGraph exactCantorGraph_total z ![a,b]
 simp [pairLoopFormula,pairLoop,nativeReaches,pairState,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,nativeRunFormula_eval,ruleHead_defined.iff,stateGraph_eval,numeral_eq_natCast,hc]
noncomputable def pairLoop_certificate (offset:Nat) (ρ:Nat→M) : FormulaCertificate ρ 1 (fun v=>pairLoop offset ρ (v 0)) := by
 refine ⟨pairLoopFormula offset,?_⟩
 intro v
 have hv:v=![v 0] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 rw [hv]; exact (pairLoopFormula_eval offset ρ (v 0)).symm
theorem pairLoop_terminates {offset:Nat} (hb:Bound offset) (ρ:Nat→M) : ∀s:M,pairLoop offset ρ s := by
 apply (pairLoop_certificate offset ρ).induction
 · change pairLoop offset ρ 0
   intro w y
   change nativeReaches _ (pairState offset ρ 10 0 w 0 (y+modelCantor 0 0))
   rw [modelCantor_zero,add_zero]
   exact nativeReaches_step (pair_step4_zero hb ρ 0 w 0 y)
 · intro s ih
   change pairLoop offset ρ s at ih
   change pairLoop offset ρ (s+1)
   intro w y
   have h1:=nativeReaches_trans (nativeReaches_step (pair_step4_dec hb ρ 0 w s y))
     (nativeReaches_step (pair_step5_inc hb ρ 0 w s y))
   have h2:=drainX_terminates hb ρ s 0 w (y+1)
   change nativeReaches _ (pairState offset ρ 9 (0+s) w 0 (y+1)) at h2
   rw [zero_add] at h2
   have h3:=nativeReaches_step (pair_step9_jump hb ρ s w 0 (y+1))
   have h4:=drainT_terminates hb ρ s w 0 (y+1)
   change nativeReaches _ (pairState offset ρ 4 0 w (0+s) ((y+1)+s)) at h4
   rw [zero_add] at h4
   have h5:=ih w (y+1+s)
   change nativeReaches _ (pairState offset ρ 10 0 w 0 ((y+1+s)+modelCantor s 0)) at h5
   have he:(y+1+s)+modelCantor s 0=y+modelCantor (s+1) 0 := by rw [triangle_succ]; ac_rfl
   rw [he] at h5
   exact nativeReaches_trans h1 (nativeReaches_trans h2 (nativeReaches_trans h3 (nativeReaches_trans h4 h5)))
/-- Ten-row core reusable at any actual certified source offset, for nonstandard register values. -/
theorem native_pair {offset:Nat} (hb:Bound offset) (ρ:Nat→M) (t w x:M) :
 nativeReaches (pairState offset ρ 0 t w x 0) (pairState offset ρ 10 0 w 0 (modelCantor x t)) := by
 have h1:=drainT_terminates hb ρ t w x 0
 change nativeReaches _ (pairState offset ρ 4 0 w (x+t) (0+t)) at h1
 rw [zero_add] at h1
 have h2:=pairLoop_terminates hb ρ (x+t) w t
 change nativeReaches _ (pairState offset ρ 10 0 w 0 (t+modelCantor (x+t) 0)) at h2
 rw [pair_triangle] at h2
 exact nativeReaches_trans h1 h2
/-- Actual MP cons pairing site; checks the literal table rather than assuming relocation. -/
lemma mp_pair_bound : Bound 4273 := by
 constructor
 · decide
 · decide
end ZF207.NativePair
