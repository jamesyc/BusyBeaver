module
public import ExactSourceNodeDecomposition
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation

def radix8QuotientGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
 “q n. ∃ t, t < 8 ∧ n = 8*q+t”
def radix8ResidueGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
 “t n. t < 8 ∧ ∃ q, n = 8*q+t”

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
lemma radix8QuotientGraph_eval (q n : M) :
 radix8QuotientGraph.val.Evalb ![q,n] ↔ ∃t : M,t<8 ∧ n=8*q+t := by
 simp [radix8QuotientGraph,numeral_eq_natCast]
lemma radix8ResidueGraph_eval (t n : M) :
 radix8ResidueGraph.val.Evalb ![t,n] ↔ t<8 ∧ ∃q : M,n=8*q+t := by
 simp [radix8ResidueGraph,numeral_eq_natCast]

lemma radix8QuotientGraph_total : GraphTotalIn (M := M) radix8QuotientGraph := by
 intro v
 have hv : v=![v 0] := by funext i; have hi : i=0 := Subsingleton.elim _ _; subst i; rfl
 rw [hv]
 obtain ⟨q,t,ht,hn⟩ := radix8_exists (v 0)
 refine ⟨q,(radix8QuotientGraph_eval _ _).mpr ⟨t,ht,hn⟩,?_⟩
 intro q' hq'
 obtain ⟨t',ht',hn'⟩ := (radix8QuotientGraph_eval _ _).mp hq'
 exact (radix8_unique q' q t' t ht' ht (hn'.symm.trans hn)).1

lemma radix8ResidueGraph_total : GraphTotalIn (M := M) radix8ResidueGraph := by
 intro v
 have hv : v=![v 0] := by funext i; have hi : i=0 := Subsingleton.elim _ _; subst i; rfl
 rw [hv]
 obtain ⟨q,t,ht,hn⟩ := radix8_exists (v 0)
 refine ⟨t,(radix8ResidueGraph_eval _ _).mpr ⟨ht,q,hn⟩,?_⟩
 intro t' ht'
 obtain ⟨hlt',q',hn'⟩ := (radix8ResidueGraph_eval _ _).mp ht'
 exact (radix8_unique q' q t' t hlt' ht (hn'.symm.trans hn)).2

omit [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma radix8QuotientGraph_nat (q n : Nat) :
 radix8QuotientGraph.val.Evalb ![q,n] ↔ q=n/8 := by
 rw [radix8QuotientGraph_eval]
 change (∃t : Nat,t<8 ∧ n=8*q+t) ↔ q=n/8
 constructor
 · rintro ⟨t,ht,hn⟩; omega
 · intro h; exact ⟨n%8,by omega,by omega⟩

omit [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma radix8ResidueGraph_nat (t n : Nat) :
 radix8ResidueGraph.val.Evalb ![t,n] ↔ t=n%8 := by
 rw [radix8ResidueGraph_eval]
 change (t<8 ∧ ∃q : Nat,n=8*q+t) ↔ t=n%8
 constructor
 · rintro ⟨ht,q,hn⟩; omega
 · intro h; exact ⟨by omega,n/8,by omega⟩

end ZFR.ArithmeticRepresentation
