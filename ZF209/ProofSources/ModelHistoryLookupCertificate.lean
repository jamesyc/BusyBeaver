module
public import ModelHistoryInvariantCertificates
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZF209.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
def historyLookupFormula : ArithmeticSemiformula Nat 2 :=
 “h n. &0<n → !(descriptionGraph literalBitApplicationPredicate) &1 &0 h”
lemma historyLookupFormula_eval (e : Nat → M) (h n : M) :
 historyLookupFormula.Eval ![h,n] e ↔ (e 0<n → t84 (t120 h) (e 0)=e 1) := by
 simp [historyLookupFormula,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons']
 have hv (x : M) : (fun _ : Fin 1=>x)=![x] := by
   funext i; exact Fin.cases rfl (fun j=>Fin.elim0 j) i
 simp only [hv]
 have hg : (descriptionGraph literalBitApplicationPredicate).Eval ![e 1,e 0,h] e ↔ e 1=t84 (t120 h) (e 0) :=
   (literalBitApplication_certificate e).correct ![e 0,h] (e 1)
 simp only [hg]
 simp [eq_comm]
noncomputable def historyLookup_certificate {e : Nat → M} {A : M → Prop}
 (p : FormulaCertificate e 1 (fun v=>A (v 0))) :
 FormulaCertificate e 1 (fun v=>e 0<v 0 → t84 (t120 (t137 A (v 0))) (e 0)=e 1) := by
 let q : FormulaCertificate e 2 (fun v=>e 0<v 1 → t84 (t120 (v 0)) (e 0)=e 1) := {
   formula := historyLookupFormula
   correct := by
     intro v
     have hv : ![v 0,v 1]=v := by funext i; exact Fin.cases rfl (fun j=>Fin.cases rfl (fun k=>Fin.elim0 k) j) i
     rw [←hv]
     exact (historyLookupFormula_eval e (v 0) (v 1)).symm
 }
 exact (literalHistory_certificate p).substitute q
end ZF209.MM0ModelReplay
