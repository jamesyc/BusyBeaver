module
public import ExactSourceNodeGraph
public import ModelCourseOfValuesSentences
public import ExactIndexEquations
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation

/-- Literal source-transform branch computation, with prior values in an HFS history.
The index graph is supplied explicitly; no recursive result is assumed. -/
def substTransformBranchGraph (idx : 𝚺ᴬ₁.Semisentence 4) : 𝚺ᴬ₁.Semisentence 8 := .mkSigma
 “z h d n t a b r.
 (n = 0 ∧ z = 0) ∨ (n ≠ 0 ∧ (
 ((t = 1 ∨ t = 2) ∧ ∃ x, ∃ y, !idx x d r a ∧ !idx y d r b ∧ !sourceNodeGraph z t x y) ∨
 ((t = 3 ∨ t = 4 ∨ t = 5) ∧ ∃ ca, ∃ cb, ∃ x, ∃ y,
    !exactCantorGraph ca d a ∧ !exactCantorGraph cb d b ∧
    !znthDef x h ca ∧ !znthDef y h cb ∧ !sourceNodeGraph z t x y) ∨
 ((t = 6 ∨ t = 7) ∧ b = 0 ∧ ∃ ca, ∃ x,
    !exactCantorGraph ca (d + 1) a ∧ !znthDef x h ca ∧ !sourceNodeGraph z t x 0) ∨
 (¬(t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ ((t = 6 ∨ t = 7) ∧ b = 0)) ∧ z = 0)))”

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma substTransformBranchGraph_eval (idx : 𝚺ᴬ₁.Semisentence 4)
 (hi : GraphTotalIn (M := M) idx) (z h d n t a b r : M) :
 (substTransformBranchGraph idx).val.Evalb ![z,h,d,n,t,a,b,r] ↔
 (n=0 ∧ z=0) ∨ (n≠0 ∧ (
 ((t=1 ∨ t=2) ∧ z=modelSourceNode t (graphValue idx hi ![d,r,a]) (graphValue idx hi ![d,r,b])) ∨
 ((t=3 ∨ t=4 ∨ t=5) ∧ z=modelSourceNode t (znth h (modelCantor d a)) (znth h (modelCantor d b))) ∨
 ((t=6 ∨ t=7) ∧ b=0 ∧ z=modelSourceNode t (znth h (modelCantor (d+1) a)) 0) ∨
 (¬(t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ ((t=6 ∨ t=7) ∧ b=0)) ∧ z=0))) := by
 simp [substTransformBranchGraph,Semiformula.eval_rew,Function.comp_def,Empty.eq_elim,
   Matrix.comp_vecCons',Matrix.empty_eq,graphValue_spec idx hi,sourceNodeGraph_eval,
   modelCantor_defined.iff,znth_defined.iff,numeral_eq_natCast]
 simp [sourceNodeGraph,modelCantor_defined.iff,modelSourceNode,numeral_eq_natCast]
 have hv (x : M) : (fun _ : Fin 1 => x)=![x] := by
   funext i; have hi : i=0 := Subsingleton.elim _ _; subst i; rfl
 simp only [hv]
 simp
 by_cases h6 : t=6 <;> by_cases h7 : t=7 <;> simp [h6,h7]

lemma substTransformBranchGraph_total (idx : 𝚺ᴬ₁.Semisentence 4)
 (hi : GraphTotalIn (M := M) idx) : GraphTotalIn (M := M) (substTransformBranchGraph idx) := by
 intro v
 have hv : v=![v 0,v 1,v 2,v 3,v 4,v 5,v 6] := by
   funext i
   refine Fin.cases rfl (fun i => ?_) i
   refine Fin.cases rfl (fun i => ?_) i
   refine Fin.cases rfl (fun i => ?_) i
   refine Fin.cases rfl (fun i => ?_) i
   refine Fin.cases rfl (fun i => ?_) i
   refine Fin.cases rfl (fun i => ?_) i
   refine Fin.cases rfl (fun i => Fin.elim0 i) i
 rw [hv]
 simp only [substTransformBranchGraph_eval idx hi]
 by_cases hn : v 2=0
 · simp [hn]
 · by_cases h1 : v 3=1
   · simp [hn,h1]
   · by_cases h2 : v 3=2
     · simp [hn,h1,h2]
     · by_cases h3 : v 3=3
       · simp [hn,h1,h2,h3]
       · by_cases h4 : v 3=4
         · simp [hn,h1,h2,h3,h4]
         · by_cases h5 : v 3=5
           · simp [hn,h1,h2,h3,h4,h5]
           · by_cases h6 : v 3=6
             · by_cases hb : v 5=0 <;> simp [hn,h1,h2,h3,h4,h5,h6,hb]
             · by_cases h7 : v 3=7
               · by_cases hb : v 5=0 <;> simp [hn,h1,h2,h3,h4,h5,h6,h7,hb]
               · simp [hn,h1,h2,h3,h4,h5,h6,h7]

end ZFR.ArithmeticRepresentation
