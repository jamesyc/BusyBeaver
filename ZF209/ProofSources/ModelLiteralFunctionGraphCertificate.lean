module
public import ModelLiteralConditionalCertificate
public import LiteralProjectionModelAlignment
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF209.MM0ModelReplay
open ZF209.MM0ModelPeano ZFR.ArithmeticRepresentation
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
noncomputable def literalFst_certificate (e : Nat → M) :
 FunctionGraphCertificate e 1 (fun v => t64 (v 0)) where
 formula := Rew.bind (L:=ℒₒᵣ) Semiterm.bvar Empty.elim ▹ unpairLeftGraph.val
 correct := by
   intro v y
   rw [Semiformula.eval_rew,literalFst_modelUnpairLeft]
   have he : (fun x : Empty => Semiterm.val (L:=ℒₒᵣ) (y :> v) e x.elim) = Empty.elim := by funext x; exact x.elim
   change unpairLeftGraph.val.Eval (y :> v) (fun x : Empty => Semiterm.val (L:=ℒₒᵣ) (y :> v) e x.elim) ↔ _
   rw [he]
   have hv : ![v 0]=v := by funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
   simpa [Function.comp_def,hv,modelUnpairLeft] using
     graphValue_spec unpairLeftGraph unpairLeftGraph_total y ![v 0]

def literalGraph_certificate {e : Nat → M} {F : M → M}
 (g : FunctionGraphCertificate e 1 (fun v => F (v 0))) :
 FormulaCertificate e 1 (fun v => t82 F (v 0)) where
 formula := ∃¹ (Rew.bind (L:=ℒₒᵣ) ![#1,#0] Semiterm.fvar ▹ (g.pairWithArgument).formula)
 correct := by
   intro v
   classical
   have h (x : M) := (g.pairWithArgument).correct ![x] (v 0)
   simp [Semiformula.eval_rew,Function.comp_def]
   have hm (x : M) : (fun i => Semiterm.val (L:=ℒₒᵣ) (x :> v) e (![#1,#0] i : ArithmeticSemiterm Nat 2)) = ![v 0,x] := by
     funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
   simp only [hm,h]
   simp [t82,t15,t9,t1,t8,t10]
end ZF209.MM0ModelReplay
