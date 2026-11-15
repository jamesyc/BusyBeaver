module
public import ExactUnpairGraph
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation

def sourceNodeGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
 “y t a b. ∃ p, !exactCantorGraph p a b ∧ y = 8*p+t”

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def modelSourceNode (t a b : M) : M := 8*modelCantor a b+t

lemma sourceNodeGraph_eval (y t a b : M) :
 sourceNodeGraph.val.Evalb ![y,t,a,b] ↔ y=modelSourceNode t a b := by
 simp [sourceNodeGraph,modelCantor_defined.iff,modelSourceNode,numeral_eq_natCast]

lemma radix8_sum_lt (q r t u : M) (ht : t<8) (hqr : q<r) :
 8*q+t<8*r+u := by
 have hs : q+1≤r := succ_le_iff_lt.mpr hqr
 calc
  8*q+t < 8*q+8 := by simpa [add_comm] using (_root_.add_lt_add_left ht (8*q))
  _ = 8*(q+1) := by rw [mul_add,mul_one]
  _ ≤ 8*r := mul_le_mul_of_nonneg_left hs (by simp)
  _ ≤ 8*r+u := by simp

lemma radix8_unique (q r t u : M) (ht : t<8) (hu : u<8)
 (h : 8*q+t=8*r+u) : q=r ∧ t=u := by
 have hq : q=r := by
  rcases lt_trichotomy q r with hl|he|hr
  · have hh := radix8_sum_lt q r t u ht hl
    rw [h] at hh
    exact False.elim (_root_.lt_irrefl _ hh)
  · exact he
  · have hh := radix8_sum_lt r q u t hu hr
    rw [h] at hh
    exact False.elim (_root_.lt_irrefl _ hh)
 refine ⟨hq,?_⟩
 rw [hq] at h
 exact add_left_cancel h

lemma modelSourceNode_injective (t a b u c d : M) (ht : t<8) (hu : u<8)
 (h : modelSourceNode t a b=modelSourceNode u c d) : t=u ∧ a=c ∧ b=d := by
 have hh := radix8_unique (modelCantor a b) (modelCantor c d) t u ht hu h
 exact ⟨hh.2,modelCantor_injective hh.1⟩

end ZFR.ArithmeticRepresentation
