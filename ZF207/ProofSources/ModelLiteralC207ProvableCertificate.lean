module
public import ModelReplay4313
public import ModelLiteralC207RulesCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
open ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def literalC207Provable_certificate (e : Nat → M) :
 FormulaCertificate e 1 (fun v=>t337 (v 0)) := by
 let der := literalC207Derives_certificate e
 refine ⟨“n. ∃p, !der.formula p n”,?_⟩
 intro v
 have hd (p n:M) : der.formula.Eval ![p,n] e ↔ t336 p n := (der.correct ![p,n]).symm
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by funext i; exact Fin.cases rfl (fun j=>Fin.elim0 j) i
 simp [Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',hd,hv,t337,literalExists_iff]
end ZF207.MM0ModelReplay
