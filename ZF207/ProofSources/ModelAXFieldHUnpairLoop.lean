module
public import ModelAXFieldHUnpairRound
@[expose] public section
set_option maxRecDepth 2000
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.AXFieldHSource
open ZF207.NativeSource ZFR.ArithmeticRepresentation ZF207.MM0ModelPeano M207.Source
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def unpairTerminates (ρ:Nat→M) (n:M) : Prop := ∀h x y:M,
 nativeReaches (unpairState ρ 131 n h x y)
 (unpairState ρ 139 0 h (modelUnpairLeft (n+modelCantor x y)) (modelUnpairRight (n+modelCantor x y)))
noncomputable def unpairLoopFormula : ArithmeticSemiformula Nat 1 :=
 “n. ∀h, ∀x, ∀y, ∀initial, ∀hist, ∀head,
 (!nativeRunFormula initial hist ∧ !listHeadGraph head hist ∧
 !stateGraph head 131 &0 n &2 &3 &4 y &6 h x) →
 ∃out, ∃last, ∃p, ∃a, ∃b,
 !nativeRunFormula initial out ∧ !listHeadGraph last out ∧ !exactCantorGraph p x y ∧
 !unpairLeftGraph a (n+p) ∧ !unpairRightGraph b (n+p) ∧
 !stateGraph last 139 &0 0 &2 &3 &4 b &6 h a”
lemma unpairLoopFormula_eval (ρ:Nat→M) (n:M) : unpairLoopFormula.Eval ![n] ρ ↔ unpairTerminates ρ n := by
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 have hc (z a b:M) : exactCantorGraph.val.Evalb ![z,a,b] ↔ z=modelCantor a b := graphValue_spec exactCantorGraph exactCantorGraph_total z ![a,b]
 have hl (z a:M) : unpairLeftGraph.val.Evalb ![z,a] ↔ z=modelUnpairLeft a := graphValue_spec unpairLeftGraph unpairLeftGraph_total z ![a]
 have hr (z a:M) : unpairRightGraph.val.Evalb ![z,a] ↔ z=modelUnpairRight a := graphValue_spec unpairRightGraph unpairRightGraph_total z ![a]
 simp [unpairLoopFormula,unpairTerminates,nativeReaches,unpairState,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,nativeRunFormula_eval,ruleHead_defined.iff,stateGraph_eval,numeral_eq_natCast,hc,hl,hr]
noncomputable def unpairLoop_certificate (ρ:Nat→M) : FormulaCertificate ρ 1 (fun v=>unpairTerminates ρ (v 0)) := by
 refine ⟨unpairLoopFormula,?_⟩
 intro v
 have hv:v=![v 0] := by funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 rw [hv]; exact (unpairLoopFormula_eval ρ (v 0)).symm
/-- Actual source11..138 outer loop; arbitrary model-sized input and retained registers. -/
theorem unpair_loop_terminates (ρ:Nat→M) : ∀n:M,unpairTerminates ρ n := by
 apply (unpairLoop_certificate ρ).induction
 · change unpairTerminates ρ 0
   intro h x y
   change nativeReaches (unpairState ρ 131 0 h x y) (unpairState ρ 139 0 h (modelUnpairLeft (0+modelCantor x y)) (modelUnpairRight (0+modelCantor x y)))
   rw [zero_add,modelUnpairLeft_pair,modelUnpairRight_pair]
   exact nativeReaches_step (unpair_step11_zero ρ 0 h x y)
 · intro n ih
   change unpairTerminates ρ n at ih
   change unpairTerminates ρ (n+1)
   intro h x y
   change nativeReaches (unpairState ρ 131 (n+1) h x y) (unpairState ρ 139 0 h (modelUnpairLeft (n+1+modelCantor x y)) (modelUnpairRight (n+1+modelCantor x y)))
   by_cases hx:x=0
   · subst x
     have ht:=ih h (y+1) 0
     change nativeReaches _ (unpairState ρ 139 0 h (modelUnpairLeft (n+modelCantor (y+1) 0)) (modelUnpairRight (n+modelCantor (y+1) 0))) at ht
     have he:n+modelCantor (y+1) 0=n+1+modelCantor 0 y := by rw [modelCantor_next_axis]; ac_rfl
     rw [he] at ht
     exact nativeReaches_trans (unpair_round_zero ρ n h y) ht
   · have hp:0<x:=pos_iff_ne_zero.mpr hx
     obtain ⟨a,ha⟩:=eq_succ_of_pos hp
     subst x
     have ht:=ih h a (y+1)
     change nativeReaches _ (unpairState ρ 139 0 h (modelUnpairLeft (n+modelCantor a (y+1))) (modelUnpairRight (n+modelCantor a (y+1)))) at ht
     have he:n+modelCantor a (y+1)=n+1+modelCantor (a+1) y := by rw [modelCantor_next_diagonal]; ac_rfl
     rw [he] at ht
     exact nativeReaches_trans (unpair_round_positive ρ n h a y) ht
end ZF207.AXFieldHSource
