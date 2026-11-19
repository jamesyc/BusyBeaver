module
public import ModelNativeAXCompareHSteps
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.NativeAXCompareH
open ZF207.NativeSource ZFR.ArithmeticRepresentation ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def guardReachesFormula : ArithmeticSemiformula Nat 6 :=
 “pc h x q i j. ∀initial, ∀hist, ∀head,
 (!nativeRunFormula initial hist ∧ !listHeadGraph head hist ∧
 !stateGraph head pc &0 &1 &2 &3 &4 &5 &6 h x) →
 ∃out, ∃last, !nativeRunFormula initial out ∧ !listHeadGraph last out ∧
 !stateGraph last q &0 &1 &2 &3 &4 &5 &6 i j”
lemma guardReachesFormula_eval (ρ:Nat→M) (pc h x q i j:M) :
 guardReachesFormula.Eval ![pc,h,x,q,i,j] ρ ↔ nativeReaches (guardState ρ pc h x) (guardState ρ q i j) := by
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext k; have hk:k=0:=Subsingleton.elim _ _; subst k; rfl
 simp [guardReachesFormula,nativeReaches,guardState,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,hv,Empty.eq_elim,nativeRunFormula_eval,ruleHead_defined.iff,stateGraph_eval]
def clearX (ρ:Nat→M) (x:M) : Prop := nativeReaches (guardState ρ 4198 0 x) (guardState ρ 4203 0 0)
def clearH (ρ:Nat→M) (h:M) : Prop := ∀x:M,nativeReaches (guardState ρ 4196 h x) (guardState ρ 4203 0 0)
def guardResult (ρ:Nat→M) (h:M) : Prop := ∀x:M,
 (h=x → nativeReaches (guardState ρ 4191 h x) (guardState ρ 4201 0 0)) ∧
 (h≠x → nativeReaches (guardState ρ 4191 h x) (guardState ρ 4203 0 0))
noncomputable def clearXFormula : ArithmeticSemiformula Nat 1 := “x. !guardReachesFormula 4198 0 x 4203 0 0”
noncomputable def clearHFormula : ArithmeticSemiformula Nat 1 := “h. ∀x, !guardReachesFormula 4196 h x 4203 0 0”
noncomputable def guardResultFormula : ArithmeticSemiformula Nat 1 :=
 “h. ∀x, (h=x → !guardReachesFormula 4191 h x 4201 0 0) ∧ (h≠x → !guardReachesFormula 4191 h x 4203 0 0)”
noncomputable def clearX_certificate (ρ:Nat→M) : FormulaCertificate ρ 1 (fun v=>clearX ρ (v 0)) := by
 refine ⟨clearXFormula,?_⟩
 intro v
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext k; have hk:k=0:=Subsingleton.elim _ _; subst k; rfl
 simp [clearXFormula,clearX,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',hv,Matrix.empty_eq,guardReachesFormula_eval,numeral_eq_natCast]
 try rfl
noncomputable def clearH_certificate (ρ:Nat→M) : FormulaCertificate ρ 1 (fun v=>clearH ρ (v 0)) := by
 refine ⟨clearHFormula,?_⟩
 intro v
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext k; have hk:k=0:=Subsingleton.elim _ _; subst k; rfl
 simp [clearHFormula,clearH,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',hv,Matrix.empty_eq,guardReachesFormula_eval,numeral_eq_natCast]
 try rfl
noncomputable def guardResult_certificate (ρ:Nat→M) : FormulaCertificate ρ 1 (fun v=>guardResult ρ (v 0)) := by
 refine ⟨guardResultFormula,?_⟩
 intro v
 have hv (z:M) : (fun _:Fin 1=>z)=![z] := by funext k; have hk:k=0:=Subsingleton.elim _ _; subst k; rfl
 simp [guardResultFormula,guardResult,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',hv,Matrix.empty_eq,guardReachesFormula_eval,numeral_eq_natCast]
 try rfl
end ZF207.NativeAXCompareH
