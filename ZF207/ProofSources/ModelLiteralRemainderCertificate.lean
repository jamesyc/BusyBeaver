module
public import ModelLiteralPairCertificate
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
open ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def literalSubtractPredicate : ArithmeticSemiformula Nat 3 := “d a b. b+d=a”
def literalSubtractCertificate (e : Nat → M) :
 FunctionGraphCertificate e 2 (fun v => t46 (v 0) (v 1)) := by
 let p : FormulaCertificate e 3 (fun v => t10 (t44 (v 2) (v 0)) (v 1)) := {
   formula := literalSubtractPredicate
   correct := by intro v; simp [literalSubtractPredicate,t10,t44]
 }
 exact FunctionGraphCertificate.ofDescription p

def literalRemainderGraph : ArithmeticSemiformula Nat 3 :=
 ∃¹ ((Rew.bind (L := ℒₒᵣ) ![#0,#2,#3] Semiterm.fvar ▹ descriptionGraph literalDivisionPredicate) ⋏
   (Rew.bind (L := ℒₒᵣ) ![#1,#2,‘#3*#0’] Semiterm.fvar ▹ descriptionGraph literalSubtractPredicate))

lemma literalRemainderGraph_eval (e : Nat → M) (r a b : M) :
 literalRemainderGraph.Eval ![r,a,b] e ↔ r=t57 a b := by
 have hd (q : M) : (descriptionGraph literalDivisionPredicate).Eval ![q,a,b] e ↔ q=t56 a b :=
   (literalDivisionCertificate e).correct ![a,b] q
 have hs (q : M) : (descriptionGraph literalSubtractPredicate).Eval ![r,a,b*q] e ↔ r=t46 a (b*q) :=
   (literalSubtractCertificate e).correct ![a,b*q] r
 simp [literalRemainderGraph,Semiformula.eval_rew,Function.comp_def]
 have hm1 (w : Fin 4 → M) : (fun i => Semiterm.val w e (![#0,#2,#3] i : ArithmeticSemiterm Nat 4)) = ![w 0,w 2,w 3] := by
   funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.elim0 l) k) j) i
 have hm2 (w : Fin 4 → M) : (fun i => Semiterm.val w e (![#1,#2,‘#3*#0’] i : ArithmeticSemiterm Nat 4)) = ![w 1,w 2,w 3*w 0] := by
   funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.elim0 l) k) j) i
 simp only [hm1,hm2]
 change (∃q,(descriptionGraph literalDivisionPredicate).Eval ![q,a,b] e ∧ (descriptionGraph literalSubtractPredicate).Eval ![r,a,b*q] e) ↔ _
 simp only [hd,hs]
 constructor
 · rintro ⟨q,rfl,h⟩; exact h
 · intro h; exact ⟨_,rfl,h⟩
end ZF207.MM0ModelReplay
