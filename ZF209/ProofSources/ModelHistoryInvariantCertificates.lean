module
public import ModelLiteralHistoryCertificate
public import ModelBoundPredicateCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def historyDomainFormula : ArithmeticSemiformula Nat 2 :=
 “h n. ∀k, (∃y, !literalBitApplicationPredicate y k h) ↔ k<n”
def historyFunctionalFormula : ArithmeticSemiformula Nat 2 :=
 “h n. ∀x, ∀y, ∀z, !literalBitApplicationPredicate y x h → !literalBitApplicationPredicate z x h → y=z”
lemma historyDomainFormula_eval (e : Nat → M) (h n : M) :
 historyDomainFormula.Eval ![h,n] e ↔ t17 (t76 (t120 h)) (t120 (t124 n)) := by
 simp [historyDomainFormula,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons']
 have hv (x : M) : (fun _ : Fin 1=>x)=![x] := by
   funext i; exact Fin.cases rfl (fun j=>Fin.elim0 j) i
 simp only [hv,literalBitApplicationPredicate_eval]
 simp [literalSetExtensional_iff,t76,t15,t9,t1,t8,t16,literalUpto_member]
lemma historyFunctionalFormula_eval (e : Nat → M) (h n : M) :
 historyFunctionalFormula.Eval ![h,n] e ↔ t72 (t120 h) := by
 simp [historyFunctionalFormula,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons']
 have hv (x : M) : (fun _ : Fin 1=>x)=![x] := by
   funext i; exact Fin.cases rfl (fun j=>Fin.elim0 j) i
 simp only [hv,literalBitApplicationPredicate_eval]
 rfl
noncomputable def historyDomain_certificate {e : Nat → M} {A : M → Prop}
 (a : FormulaCertificate e 1 (fun v=>A (v 0))) :
 FormulaCertificate e 1 (fun v=>t17 (t76 (t120 (t137 A (v 0)))) (t120 (t124 (v 0)))) := by
 let q : FormulaCertificate e 2 (fun v=>t17 (t76 (t120 (v 0))) (t120 (t124 (v 1)))) := {
   formula := historyDomainFormula
   correct := by
     intro v
     have hv : ![v 0,v 1]=v := by funext i; exact Fin.cases rfl (fun j=>Fin.cases rfl (fun k=>Fin.elim0 k) j) i
     rw [←hv]
     exact (historyDomainFormula_eval e (v 0) (v 1)).symm
 }
 exact (literalHistory_certificate a).substitute q
noncomputable def historyFunctional_certificate {e : Nat → M} {A : M → Prop}
 (a : FormulaCertificate e 1 (fun v=>A (v 0))) :
 FormulaCertificate e 1 (fun v=>t72 (t120 (t137 A (v 0)))) := by
 let q : FormulaCertificate e 2 (fun v=>t72 (t120 (v 0))) := {
   formula := historyFunctionalFormula
   correct := by
     intro v
     have hv : ![v 0,v 1]=v := by funext i; exact Fin.cases rfl (fun j=>Fin.cases rfl (fun k=>Fin.elim0 k) j) i
     rw [←hv]
     exact (historyFunctionalFormula_eval e (v 0) (v 1)).symm
 }
 exact (literalHistory_certificate a).substitute q
end ZF209.MM0ModelReplay
