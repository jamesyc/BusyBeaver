module
public import ModelLiteralTraceStepCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
open ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def literalTraceCheck_certificate {e : Nat → M} {A : M → Prop}
 (a : FormulaCertificate e 1 (fun v=>A (v 0))) :
 FunctionGraphCertificate e 1 (fun v=>t171 A (v 0)) := by
 let g := FunctionGraphCertificate.bindFirst (e := e) (F := fun i n=>t142 i (t170 A) n)
  (fun i : M=>literalNestedRec_certificate (literalTraceStep_certificate (a.prependParameter i))) (by intro i; rfl)
 refine ⟨“y n. !g.formula y n 1”,?_⟩
 intro v y
 have hg (y n i:M) : g.formula.Eval ![y,n,i] e ↔ y=t142 i (t170 A) n := g.correct ![n,i] y
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,hv,hg]
 simp [t171,t30,t29,t28]
noncomputable def literalTraceValid_certificate {e : Nat → M} {A : M → Prop}
 (a : FormulaCertificate e 1 (fun v=>A (v 0))) :
 FormulaCertificate e 1 (fun v=>t172 A (v 0)) := by
 let g := literalTraceCheck_certificate a
 refine ⟨“x. ∃y, !g.formula y x ∧ y≠0”,?_⟩
 intro v
 have hg (y x:M) := g.correct ![x] y
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,hv,hg,t172,t51,t13,t10,t28,t1]
end ZF207.MM0ModelReplay
