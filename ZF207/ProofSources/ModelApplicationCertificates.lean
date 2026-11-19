module
public import ModelGraphSubstitutionCertificates
public import ExactCantorGraph
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZF207.MM0ModelPeano
open ZFR.ArithmeticRepresentation

def pairMembershipFormula (φ : ArithmeticSemiformula Nat 1) : ArithmeticSemiformula Nat 2 :=
 ∃¹ ((Rew.bind (L := ℒₒᵣ) ![#0,#2,#1] Empty.elim ▹ exactCantorGraph.val) ⋏
      (Rew.bind (L := ℒₒᵣ) ![#0] Semiterm.fvar ▹ φ))

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

lemma pairMembership_eval (φ : ArithmeticSemiformula Nat 1) (e : Nat → M) (y x : M) :
 (pairMembershipFormula φ).Eval ![y,x] e ↔ φ.Eval ![modelCantor x y] e := by
 have hc (p : M) : exactCantorGraph.val.Evalb ![p,x,y] ↔ p=modelCantor x y := by
   exact graphValue_spec exactCantorGraph exactCantorGraph_total p ![x,y]
 simp only [pairMembershipFormula,Semiformula.eval_ex]
 simp [Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons']

 have he (p : M) : (fun x₂ : Empty => Semiterm.val (L := ℒₒᵣ) ![p,y,x] e x₂.elim) = (Empty.elim : Empty → M) := by funext z; exact z.elim
 simp only [he]
 have hv (p : M) : (fun _ : Fin 1 => p) = ![p] := by funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
 simp only [hv]
 change (∃p, exactCantorGraph.val.Evalb ![p,x,y] ∧ φ.Eval ![p] e) ↔ _
 simp only [hc]
 constructor
 · rintro ⟨p,rfl,h⟩; exact h
 · intro h; exact ⟨modelCantor x y,rfl,h⟩

/-- Graph-application pattern of t84, using exact model Cantor pairing.
This does not assert transport of the original t63 division/description code. -/
noncomputable def modelApply (A : M → Prop) (x : M) : M :=
 the (fun y => A (modelCantor x y))

def FormulaCertificate.pairMembership {e : Nat → M} {A : M → Prop}
 (a : FormulaCertificate e 1 (fun v => A (v 0))) :
 FormulaCertificate e 2 (fun v => A (modelCantor (v 1) (v 0))) where
 formula := pairMembershipFormula a.formula
 correct := by
   intro v
   have hv : ![v 0,v 1]=v := by funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
   rw [←hv]
   rw [pairMembership_eval]
   exact a.correct ![modelCantor (v 1) (v 0)]

def FormulaCertificate.application {e : Nat → M} {A : M → Prop}
 (a : FormulaCertificate e 1 (fun v => A (v 0))) :
 FunctionGraphCertificate e 1 (fun v => modelApply A (v 0)) :=
 FunctionGraphCertificate.ofDescription a.pairMembership

end ZF207.MM0ModelPeano
