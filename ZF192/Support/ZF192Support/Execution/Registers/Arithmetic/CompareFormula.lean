module
public import ZF192Support.Execution.Registers.Arithmetic.CompareSteps
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF192Support.NativeCompare
open ZF192Support.NativeSource ZFR.ArithmeticRepresentation ZF192Support.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def guardReachesFormula : ArithmeticSemiformula Nat 6 :=
 “pc h x q i j. ∀initial, ∀hist, ∀head,
 (!nativeRunFormula initial hist ∧ !listHeadGraph head hist ∧
 !stateGraph head pc &0 &1 &2 &3 &4 &5 &6 h x) →
 ∃out, ∃last, !nativeRunFormula initial out ∧ !listHeadGraph last out ∧
 !stateGraph last q &0 &1 &2 &3 &4 &5 &6 i j”
lemma guardReachesFormula_eval (ρ:Nat→M) (pc h x q i j:M) :
 guardReachesFormula.Eval ![pc,h,x,q,i,j] ρ ↔ nativeReaches (guardState ρ pc h x) (guardState ρ q i j) := by
 simp [guardReachesFormula,nativeReaches,guardState,Semiformula.eval_rew,Function.comp_def,
 Matrix.comp_vecCons',Matrix.empty_eq,Matrix.constant_eq_singleton,Empty.eq_elim,nativeRunFormula_eval,ruleHead_defined.iff,stateGraph_eval]
def clearX (base unequal : Nat) (ρ:Nat→M) (x:M) : Prop := nativeReaches (guardState ρ ((base + 7 : Nat) : M) 0 x) (guardState ρ (unequal : M) 0 0)
def clearH (base unequal : Nat) (ρ:Nat→M) (h:M) : Prop := ∀x:M,nativeReaches (guardState ρ ((base + 5 : Nat) : M) h x) (guardState ρ (unequal : M) 0 0)
def guardResult (base unequal : Nat) (ρ:Nat→M) (h:M) : Prop := ∀x:M,
 (h=x → nativeReaches (guardState ρ (base : M) h x) (guardState ρ ((base + 10 : Nat) : M) 0 0)) ∧
 (h≠x → nativeReaches (guardState ρ (base : M) h x) (guardState ρ (unequal : M) 0 0))
noncomputable def clearXFormula (base unequal : Nat) : ArithmeticSemiformula Nat 1 := “x. !guardReachesFormula ↑(base+7) 0 x ↑unequal 0 0”
noncomputable def clearHFormula (base unequal : Nat) : ArithmeticSemiformula Nat 1 := “h. ∀x, !guardReachesFormula ↑(base+5) h x ↑unequal 0 0”
noncomputable def guardResultFormula (base unequal : Nat) : ArithmeticSemiformula Nat 1 :=
 “h. ∀x, (h=x → !guardReachesFormula ↑base h x ↑(base+10) 0 0) ∧ (h≠x → !guardReachesFormula ↑base h x ↑unequal 0 0)”
noncomputable def clearX_certificate (base unequal : Nat) (ρ:Nat→M) : FormulaCertificate ρ 1 (fun v=>clearX base unequal ρ (v 0)) := by
 refine ⟨clearXFormula base unequal,?_⟩
 intro v
 simp [clearXFormula,clearX,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.constant_eq_singleton,Matrix.empty_eq,guardReachesFormula_eval,numeral_eq_natCast]
 try rfl
noncomputable def clearH_certificate (base unequal : Nat) (ρ:Nat→M) : FormulaCertificate ρ 1 (fun v=>clearH base unequal ρ (v 0)) := by
 refine ⟨clearHFormula base unequal,?_⟩
 intro v
 simp [clearHFormula,clearH,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.constant_eq_singleton,Matrix.empty_eq,guardReachesFormula_eval,numeral_eq_natCast]
 try rfl
noncomputable def guardResult_certificate (base unequal : Nat) (ρ:Nat→M) : FormulaCertificate ρ 1 (fun v=>guardResult base unequal ρ (v 0)) := by
 refine ⟨guardResultFormula base unequal,?_⟩
 intro v
 simp [guardResultFormula,guardResult,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.constant_eq_singleton,Matrix.empty_eq,guardReachesFormula_eval,numeral_eq_natCast]
 try rfl
end ZF192Support.NativeCompare
