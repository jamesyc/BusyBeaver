module
public import ExactSourceDescent
public import UnaryGraphComposition
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation

def predecessorGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
 “p n. (n=0 ∧ p=0) ∨ (n≠0 ∧ p+1=n)”
def listHeadGraph : 𝚺ᴬ₁.Semisentence 2 := compositionGraph unpairLeftGraph (fun _ : Fin 1 => predecessorGraph)
def listTailGraph : 𝚺ᴬ₁.Semisentence 2 := compositionGraph unpairRightGraph (fun _ : Fin 1 => predecessorGraph)
def listConsGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
 “n a b. ∃ p, !exactCantorGraph p a b ∧ n=p+1”

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
lemma predecessorGraph_eval (p n : M) : predecessorGraph.val.Evalb ![p,n] ↔
 (n=0 ∧ p=0) ∨ (n≠0 ∧ p+1=n) := by simp [predecessorGraph]

lemma predecessorGraph_total : GraphTotalIn (M := M) predecessorGraph := by
 intro v
 have hv : v=![v 0] := by funext i; have hi : i=0 := Subsingleton.elim _ _; subst i; rfl
 rw [hv]
 by_cases hn : v 0=0
 · refine ⟨0,?_,?_⟩ <;> simp [predecessorGraph,hn]
 · obtain ⟨p,hp⟩ := eq_succ_of_pos (pos_iff_ne_zero.mpr hn)
   refine ⟨p,?_,?_⟩
   · exact (predecessorGraph_eval _ _).mpr (Or.inr ⟨hn,hp.symm⟩)
   · intro q hq
     have hq' : q+1=v 0 := by simpa [predecessorGraph,hn] using hq
     exact add_right_cancel (hq'.trans hp)

noncomputable def modelListCons (a b : M) : M := modelCantor a b+1
noncomputable def modelPredecessor (n : M) : M := graphValue predecessorGraph predecessorGraph_total ![n]
noncomputable def modelListHead (n : M) : M := modelUnpairLeft (modelPredecessor n)
noncomputable def modelListTail (n : M) : M := modelUnpairRight (modelPredecessor n)

lemma predecessorGraph_value (p n : M) : predecessorGraph.val.Evalb ![p,n] ↔ p=modelPredecessor n :=
 graphValue_spec predecessorGraph predecessorGraph_total p ![n]

lemma modelPredecessor_succ (p : M) : modelPredecessor (p+1)=p := by
 symm
 apply (predecessorGraph_value _ _).mp
 exact (predecessorGraph_eval _ _).mpr (Or.inr ⟨ne_of_gt (by simp),rfl⟩)

lemma modelPredecessor_of_pos (n : M) (hn : 0<n) : modelPredecessor n+1=n := by
 have h := (predecessorGraph_eval (modelPredecessor n) n).mp ((predecessorGraph_value (modelPredecessor n) n).mpr rfl)
 rcases h with ⟨hz,_⟩|⟨_,hs⟩
 · exact False.elim ((ne_of_gt hn) hz)
 · exact hs

lemma listConsGraph_eval (n a b : M) : listConsGraph.val.Evalb ![n,a,b] ↔ n=modelListCons a b := by
 simp [listConsGraph,modelCantor_defined.iff,modelListCons]

lemma modelListHead_cons (a b : M) : modelListHead (modelListCons a b)=a := by
 simp only [modelListHead,modelListCons,modelPredecessor_succ,modelUnpairLeft_pair]
lemma modelListTail_cons (a b : M) : modelListTail (modelListCons a b)=b := by
 simp only [modelListTail,modelListCons,modelPredecessor_succ,modelUnpairRight_pair]

lemma modelList_reconstruct (n : M) (hn : 0<n) : modelListCons (modelListHead n) (modelListTail n)=n := by
 rw [modelListCons,modelListHead,modelListTail,modelUnpair_reconstruct,modelPredecessor_of_pos n hn]

lemma modelListHead_lt (n : M) (hn : 0<n) : modelListHead n<n := by
 have h := modelCantor_left_le (modelListHead n) (modelListTail n)
 have hr : modelCantor (modelListHead n) (modelListTail n)+1=n := modelList_reconstruct n hn
 exact lt_of_le_of_lt h (lt_of_lt_of_eq (lt_add_one _) hr)
lemma modelListTail_lt (n : M) (hn : 0<n) : modelListTail n<n := by
 have h := modelCantor_right_le (modelListHead n) (modelListTail n)
 have hr : modelCantor (modelListHead n) (modelListTail n)+1=n := modelList_reconstruct n hn
 exact lt_of_le_of_lt h (lt_of_lt_of_eq (lt_add_one _) hr)

omit [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma predecessorGraph_nat (p n : Nat) : predecessorGraph.val.Evalb ![p,n] ↔ p=n-1 := by
 rw [predecessorGraph_eval]
 change ((n=0 ∧ p=0) ∨ (n≠0 ∧ p+1=n)) ↔ p=n-1
 omega

lemma listHeadGraph_eval (a n : M) : listHeadGraph.val.Evalb ![a,n] ↔ a=modelListHead n := by
 rw [listHeadGraph,unaryCompositionGraph_eval]
 simp only [graphValue_spec unpairLeftGraph unpairLeftGraph_total,predecessorGraph_value]
 simp [modelListHead,modelUnpairLeft]

lemma listTailGraph_eval (b n : M) : listTailGraph.val.Evalb ![b,n] ↔ b=modelListTail n := by
 rw [listTailGraph,unaryCompositionGraph_eval]
 simp only [graphValue_spec unpairRightGraph unpairRightGraph_total,predecessorGraph_value]
 simp [modelListTail,modelUnpairRight]

omit [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma modelPredecessor_nat (n : Nat) : modelPredecessor n=n-1 :=
 (predecessorGraph_nat _ _).mp ((predecessorGraph_value _ _).mpr rfl)

omit [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma modelListHead_nat (n : Nat) : modelListHead n=(C207Soundness.unpair (n-1)).1 := by
 rw [modelListHead,modelPredecessor_nat,modelUnpairLeft_nat]

omit [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma modelListTail_nat (n : Nat) : modelListTail n=(C207Soundness.unpair (n-1)).2 := by
 rw [modelListTail,modelPredecessor_nat,modelUnpairRight_nat]

end ZFR.ArithmeticRepresentation
