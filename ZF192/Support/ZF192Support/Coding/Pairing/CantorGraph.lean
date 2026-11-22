module
public import ZF192Support.Coding.Arithmetic.GraphPrimitiveRecursion
public import ZF192Support.Coding.Pairing.Model
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
open CCodeSoundness

def exactCantorGraph : 𝚺ᴬ₁.Semisentence 3 := ZF192Support.Internal.cantorDef.ofZero _

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma exactCantorGraph_total : GraphTotalIn (M := M) exactCantorGraph := by
 intro v
 simp [exactCantorGraph, existsUnique_eq]

noncomputable def modelCantor (a b : M) : M := graphValue exactCantorGraph exactCantorGraph_total ![a,b]

lemma modelCantor_equation (a b : M) :
 2*modelCantor a b=(a+b)*((a+b)+1)+2*b := by
 have h := (graphValue_spec exactCantorGraph exactCantorGraph_total (modelCantor a b) ![a,b]).mpr rfl
 exact ZF192Support.Internal.cantor_eq_iff.mp (by simpa [exactCantorGraph] using h)

lemma modelCantor_unique (a b z : M) (h : 2*z=(a+b)*((a+b)+1)+2*b) : z=modelCantor a b := by
 apply mul_left_cancel₀ (by simp : (2:M)≠0)
 exact h.trans (modelCantor_equation a b).symm

omit [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem exactCantorGraph_nat (z a b : Nat) : exactCantorGraph.val.Evalb ![z,a,b] ↔ z=cantor a b := by
 simp [exactCantorGraph, ZF192Support.Internal.cantor_nat]

lemma modelCantor_sum_le_double (a b : M) : 2*(a+b)≤2*modelCantor a b := by
 by_cases hs : a+b=0
 · rw [hs]; simp
 · have hp : 0<a+b := pos_iff_ne_zero.mpr hs
   have h1 : 1≤a+b := one_le_of_zero_lt _ hp
   have h2 : 2≤(a+b)+1 := by
     simpa only [one_add_one_eq_two] using (_root_.add_le_add h1 (_root_.le_refl (1:M)))
   calc
    2*(a+b) ≤ ((a+b)+1)*(a+b) := mul_le_mul_of_nonneg_right h2 (by simp)
    _ = (a+b)*((a+b)+1) := mul_comm _ _
    _ ≤ (a+b)*((a+b)+1)+2*b := by simp
    _ = 2*modelCantor a b := (modelCantor_equation a b).symm

lemma modelCantor_sum_le (a b : M) : a+b≤modelCantor a b :=
 (mul_le_mul_iff_right₀ (show (0 : M) < 2 by simp)).mp (modelCantor_sum_le_double a b)

lemma modelCantor_left_le (a b : M) : a≤modelCantor a b :=
 le_trans (by simp : a≤a+b) (modelCantor_sum_le a b)
lemma modelCantor_right_le (a b : M) : b≤modelCantor a b :=
 le_trans (by simp : b≤a+b) (modelCantor_sum_le a b)

end ZFR.ArithmeticRepresentation
