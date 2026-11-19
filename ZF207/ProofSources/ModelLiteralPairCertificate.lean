module
public import ModelReplay1270
public import ModelGraphSubstitutionCertificates
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelReplay
open ZF207.MM0ModelPeano
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def literalDivisionPredicate : ArithmeticSemiformula Nat 3 :=
 “q a b. ∃ r, (∃d,(r+1)+d=b) ∧ b*q+r=a”

def literalDivisionCertificate (e : Nat → M) :
 FunctionGraphCertificate e 2 (fun v => t56 (v 0) (v 1)) := by
 let p : FormulaCertificate e 3 (fun v =>
   t9 (fun r => t2 (t48 r (v 2)) (t10 (t44 (t45 (v 2) (v 0)) r) (v 1)))) := {
   formula := literalDivisionPredicate
   correct := by
     intro v
     classical
     simp [literalDivisionPredicate,t9,t1,t8,t2,t0,t48,t47,t29,t10,t44,t45]
 }
 exact FunctionGraphCertificate.ofDescription p

/-- Graph of the ORIGINAL description-defined t63, not an assumed replacement
by modelCantor. Division graph is obtained syntactically from t56's definition. -/
def literalPairGraph : ArithmeticSemiformula Nat 3 :=
 ∃¹ ((Rew.bind (L := ℒₒᵣ)
   ![#0, ‘(#2+#3)*((#2+#3)+1)’, ‘(0+1)+1’] Semiterm.fvar ▹
   descriptionGraph literalDivisionPredicate) ⋏ “#1 = #0+#3”)

lemma literalPairGraph_eval (e : Nat → M) (z a b : M) :
 literalPairGraph.Eval ![z,a,b] e ↔ z=t63 a b := by
 have hd (q : M) : (descriptionGraph literalDivisionPredicate).Eval
   ![q,(a+b)*((a+b)+1),(0+1)+1] e ↔ q=t56 ((a+b)*((a+b)+1)) ((0+1)+1) :=
   (literalDivisionCertificate e).correct ![(a+b)*((a+b)+1),(0+1)+1] q
 simp [literalPairGraph,Semiformula.eval_rew,Function.comp_def]
 change (∃q,(descriptionGraph literalDivisionPredicate).Eval ![q,(a+b)*((a+b)+1),(0+1)+1] e ∧ z=q+b) ↔ z=t63 a b
 simp only [hd]
 constructor
 · rintro ⟨q,rfl,h⟩; exact h
 · intro h; exact ⟨_,rfl,h⟩
def literalPairExistsFormula : ArithmeticSemiformula Nat 1 :=
 ∃¹ ∃¹ (Rew.bind (L := ℒₒᵣ) ![#2,#1,#0] Semiterm.fvar ▹ literalPairGraph)

lemma reverseTriple_eval (φ : ArithmeticSemiformula Nat 3) (e : Nat → M)
 (v : Fin 1 → M) (a b : M) :
 (Rew.bind (L := ℒₒᵣ) ![#2,#1,#0] Semiterm.fvar ▹ φ).Eval (b :> a :> v) e ↔
 φ.Eval ![v 0,a,b] e := by
 rw [Semiformula.eval_rew]
 have hb : Semiterm.val (b :> a :> v) e ∘
   (Rew.bind (L := ℒₒᵣ) ![#2,#1,#0] Semiterm.fvar) ∘ Semiterm.bvar = ![v 0,a,b] := by
   funext i
   exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.elim0 l) k) j) i
 have hf : Semiterm.val (b :> a :> v) e ∘
   (Rew.bind (L := ℒₒᵣ) ![#2,#1,#0] Semiterm.fvar) ∘ Semiterm.fvar = e := by
   funext i; rfl
 rw [hb,hf]

def literalPairExists_certificate (e : Nat → M) :
 FormulaCertificate e 1 (fun v => ∃a b,v 0=t63 a b) where
 formula := literalPairExistsFormula
 correct := by
   intro v
   change (∃a b,v 0=t63 a b) ↔ ∃a b,
     (Rew.bind (L := ℒₒᵣ) ![#2,#1,#0] Semiterm.fvar ▹ literalPairGraph).Eval (b :> a :> v) e
   apply exists_congr; intro a
   apply exists_congr; intro b
   rw [reverseTriple_eval]
   exact (literalPairGraph_eval e (v 0) a b).symm

end ZF207.MM0ModelReplay
