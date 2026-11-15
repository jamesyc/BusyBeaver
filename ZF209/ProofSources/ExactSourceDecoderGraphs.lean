module
public import ExactRadix8Graphs
public import UniformGraphSyntax
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation

def sourceLeftGraph : 𝚺ᴬ₁.Semisentence 2 :=
 compositionGraph unpairLeftGraph (fun _ : Fin 1 => radix8QuotientGraph)
def sourceRightGraph : 𝚺ᴬ₁.Semisentence 2 :=
 compositionGraph unpairRightGraph (fun _ : Fin 1 => radix8QuotientGraph)

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
lemma sourceLeftGraph_total : GraphTotalIn (M := M) sourceLeftGraph :=
 compositionGraph_total _ _ unpairLeftGraph_total (fun _ => radix8QuotientGraph_total)
lemma sourceRightGraph_total : GraphTotalIn (M := M) sourceRightGraph :=
 compositionGraph_total _ _ unpairRightGraph_total (fun _ => radix8QuotientGraph_total)

omit [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma sourceLeftGraph_nat (a n : Nat) :
 sourceLeftGraph.val.Evalb ![a,n] ↔ a=(C209Soundness.unpair (n/8)).1 := by
 rw [sourceLeftGraph,compositionGraph_eval]
 constructor
 · rintro ⟨w,ha,hw⟩
   have hw0 : w 0=n/8 := (radix8QuotientGraph_nat _ _).mp (hw 0)
   have hv : w=![w 0] := by funext i; have hi : i=0 := Subsingleton.elim _ _; subst i; rfl
   rw [hv,hw0] at ha
   exact (unpairLeftGraph_nat _ _).mp ha
 · intro h
   refine ⟨![n/8],(unpairLeftGraph_nat _ _).mpr h,?_⟩
   intro i
   have hi : i=0 := Subsingleton.elim _ _; subst i
   exact (radix8QuotientGraph_nat _ _).mpr rfl

omit [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma sourceRightGraph_nat (b n : Nat) :
 sourceRightGraph.val.Evalb ![b,n] ↔ b=(C209Soundness.unpair (n/8)).2 := by
 rw [sourceRightGraph,compositionGraph_eval]
 constructor
 · rintro ⟨w,hb,hw⟩
   have hw0 : w 0=n/8 := (radix8QuotientGraph_nat _ _).mp (hw 0)
   have hv : w=![w 0] := by funext i; have hi : i=0 := Subsingleton.elim _ _; subst i; rfl
   rw [hv,hw0] at hb
   exact (unpairRightGraph_nat _ _).mp hb
 · intro h
   refine ⟨![n/8],(unpairRightGraph_nat _ _).mpr h,?_⟩
   intro i
   have hi : i=0 := Subsingleton.elim _ _; subst i
   exact (radix8QuotientGraph_nat _ _).mpr rfl

end ZFR.ArithmeticRepresentation
