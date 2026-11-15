module
public import ModelReplay2378
public import ModelLiteralNestedRecCertificate
public import ModelLiteralContextCodeCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZF209.MM0ModelPeano ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def literalSnd_certificate (e : Nat → M) :
 FunctionGraphCertificate e 1 (fun v => t65 (v 0)) where
 formula := Rew.bind (L:=ℒₒᵣ) Semiterm.bvar Empty.elim ▹ unpairRightGraph.val
 correct := by
   intro v y
   rw [Semiformula.eval_rew,literalSnd_modelUnpairRight]
   have he : (fun x : Empty => Semiterm.val (L:=ℒₒᵣ) (y :> v) e x.elim) = Empty.elim := by funext x; exact x.elim
   change unpairRightGraph.val.Eval (y :> v) (fun x : Empty => Semiterm.val (L:=ℒₒᵣ) (y :> v) e x.elim) ↔ _
   rw [he]
   have hv : ![v 0]=v := by funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
   simpa [Function.comp_def,hv,modelUnpairRight] using
     graphValue_spec unpairRightGraph unpairRightGraph_total y ![v 0]


lemma literalGrecStep_member (A : M → Prop) (b k : M) :
 t89 (fun n=>t82 (fun x=>t84 A (t63 (t46 b (t29 n)) x))) k ↔
 t65 k=t84 A (t63 (t46 b (t29 (t64 (t64 k)))) (t65 (t64 k))) := by
 simp [t89,t73,t15,t16,t25,t14,t8,t0,t10,literalGraph_pair_member,p1277,p1278]
noncomputable def literalGrecStep_certificate {e : Nat → M} {A : M → Prop}
 (a : FormulaCertificate e 1 (fun v=>A (v 0))) :
 FormulaCertificate e 1 (fun v=>t89 (fun n=>t82 (fun x=>t84 A (t63 (t46 (e 1) (t29 n)) x))) (v 0)) := by
 let app := literalApply_certificate a
 let sub := literalSubtractCertificate e
 let fst := literalFst_certificate e
 let snd := literalSnd_certificate e
 refine ⟨“k. ∃u, ∃y, ∃n, ∃x, ∃d, ∃p,
 !fst.formula u k ∧ !snd.formula y k ∧ !fst.formula n u ∧ !snd.formula x u ∧
 !sub.formula d &1 (n+1) ∧ !literalPairGraph p d x ∧ !app.formula y p”,?_⟩
 intro v
 rw [literalGrecStep_member]
 have hl (u k:M) := fst.correct ![k] u
 have hr (u k:M) := snd.correct ![k] u
 have hs (d b n:M) := sub.correct ![b,n] d
 have ha (y p:M) := app.correct ![p] y
 have hv (x:M) : (fun _ : Fin 1=>x)=![x] := by
  funext i; have hi:i=0:=Subsingleton.elim _ _; subst i; rfl
 simp [Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',Matrix.empty_eq,hv,hl,hr,hs,ha,literalPairGraph_eval,t29]
end ZF209.MM0ModelReplay
