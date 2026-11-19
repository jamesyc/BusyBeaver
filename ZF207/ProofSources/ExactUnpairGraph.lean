module
public import ExactCantorInverseLaws
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
open C207Soundness

def unpairLeftGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma “a n. ∃ b, !exactCantorGraph n a b”
def unpairRightGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma “b n. ∃ a, !exactCantorGraph n a b”

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma unpairLeftGraph_eval (a n : M) : unpairLeftGraph.val.Evalb ![a,n] ↔ ∃ b,n=modelCantor a b := by
 simp [unpairLeftGraph,modelCantor_defined.iff]
lemma unpairRightGraph_eval (b n : M) : unpairRightGraph.val.Evalb ![b,n] ↔ ∃ a,n=modelCantor a b := by
 simp [unpairRightGraph,modelCantor_defined.iff]

lemma unpairLeftGraph_total : GraphTotalIn (M := M) unpairLeftGraph := by
 intro v
 have hv : v=![v 0] := by funext i; have hi : i=0 := Subsingleton.elim _ _; subst i; rfl
 rw [hv]
 obtain ⟨a,b,h⟩ := modelCantor_surjective (v 0)
 refine ⟨a,(unpairLeftGraph_eval a _).mpr ⟨b,h.symm⟩,?_⟩
 intro z hz
 obtain ⟨b',hb⟩ := (unpairLeftGraph_eval z _).mp hz
 exact (modelCantor_injective (hb.symm.trans h.symm)).1

lemma unpairRightGraph_total : GraphTotalIn (M := M) unpairRightGraph := by
 intro v
 have hv : v=![v 0] := by funext i; have hi : i=0 := Subsingleton.elim _ _; subst i; rfl
 rw [hv]
 obtain ⟨a,b,h⟩ := modelCantor_surjective (v 0)
 refine ⟨b,(unpairRightGraph_eval b _).mpr ⟨a,h.symm⟩,?_⟩
 intro z hz
 obtain ⟨a',ha⟩ := (unpairRightGraph_eval z _).mp hz
 exact (modelCantor_injective (ha.symm.trans h.symm)).2

noncomputable def modelUnpairLeft (n : M) : M := graphValue unpairLeftGraph unpairLeftGraph_total ![n]
noncomputable def modelUnpairRight (n : M) : M := graphValue unpairRightGraph unpairRightGraph_total ![n]

lemma modelUnpairLeft_pair (a b : M) : modelUnpairLeft (modelCantor a b)=a := by
 symm
 exact (graphValue_spec unpairLeftGraph unpairLeftGraph_total a ![modelCantor a b]).mp
   ((unpairLeftGraph_eval a _).mpr ⟨b,rfl⟩)
lemma modelUnpairRight_pair (a b : M) : modelUnpairRight (modelCantor a b)=b := by
 symm
 exact (graphValue_spec unpairRightGraph unpairRightGraph_total b ![modelCantor a b]).mp
   ((unpairRightGraph_eval b _).mpr ⟨a,rfl⟩)
lemma modelUnpair_reconstruct (n : M) : modelCantor (modelUnpairLeft n) (modelUnpairRight n)=n := by
 obtain ⟨a,b,h⟩ := modelCantor_surjective n
 rw [←h,modelUnpairLeft_pair,modelUnpairRight_pair]

omit [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma modelCantor_nat (a b : Nat) : modelCantor a b=cantor a b :=
 (exactCantorGraph_nat _ a b).mp (modelCantor_defined.iff.mpr rfl)

omit [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma modelUnpairLeft_nat (n : Nat) : modelUnpairLeft n=(C207Soundness.unpair n).1 := by
 have h : modelCantor (C207Soundness.unpair n).1 (C207Soundness.unpair n).2=n := by rw [modelCantor_nat]; exact C207Soundness.unpair_spec n
 rw [←h,modelUnpairLeft_pair,h]

omit [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma modelUnpairRight_nat (n : Nat) : modelUnpairRight n=(C207Soundness.unpair n).2 := by
 have h : modelCantor (C207Soundness.unpair n).1 (C207Soundness.unpair n).2=n := by rw [modelCantor_nat]; exact C207Soundness.unpair_spec n
 rw [←h,modelUnpairRight_pair,h]

omit [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma unpairLeftGraph_nat (a n : Nat) : unpairLeftGraph.val.Evalb ![a,n] ↔ a=(C207Soundness.unpair n).1 := by
 have h := graphValue_spec unpairLeftGraph unpairLeftGraph_total a ![n]
 change unpairLeftGraph.val.Evalb ![a,n] ↔ a=modelUnpairLeft n at h
 simpa only [modelUnpairLeft_nat] using h
omit [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma unpairRightGraph_nat (b n : Nat) : unpairRightGraph.val.Evalb ![b,n] ↔ b=(C207Soundness.unpair n).2 := by
 have h := graphValue_spec unpairRightGraph unpairRightGraph_total b ![n]
 change unpairRightGraph.val.Evalb ![b,n] ↔ b=modelUnpairRight n at h
 simpa only [modelUnpairRight_nat] using h

end ZFR.ArithmeticRepresentation
