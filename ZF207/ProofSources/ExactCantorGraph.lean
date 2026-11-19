module
public import GraphPrimitiveRecursion
public import NumericSource
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
open C207Soundness

def exactCantorGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
 “z a b. 2*z = (a+b)*((a+b)+1)+2*b”

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Induction over arbitrary MODEL elements, not the standard natural numbers. -/
lemma successorProduct_even (s : M) : ∃ h : M, 2*h=s*(s+1) := by
 induction s using ISigma1.sigma1_succ_induction
 · definability
 case zero => exact ⟨0,by simp⟩
 case succ s ih =>
   obtain ⟨h,hh⟩ := ih
   refine ⟨h+(s+1),?_⟩
   rw [mul_add,hh]
   simp only [←one_add_one_eq_two,mul_add,add_mul,mul_one,one_mul]
   ac_rfl

lemma exactCantorGraph_total : GraphTotalIn (M := M) exactCantorGraph := by
 intro v
 obtain ⟨h,hh⟩ := successorProduct_even (v 0+v 1)
 refine ⟨h+v 1,?_,?_⟩
 · simp [exactCantorGraph,mul_add,hh]
 · intro y hy
   have he : 2*y=(v 0+v 1)*((v 0+v 1)+1)+2*v 1 := by
     simpa [exactCantorGraph] using hy
   have he' : 2*y=2*(h+v 1) := by rw [mul_add,hh]; exact he
   exact mul_left_cancel₀ (by simp : (2:M)≠0) he'

noncomputable def modelCantor (a b : M) : M := graphValue exactCantorGraph exactCantorGraph_total ![a,b]

lemma modelCantor_equation (a b : M) :
 2*modelCantor a b=(a+b)*((a+b)+1)+2*b := by
 have h := (graphValue_spec exactCantorGraph exactCantorGraph_total (modelCantor a b) ![a,b]).mpr rfl
 simpa [exactCantorGraph] using h

lemma modelCantor_unique (a b z : M) (h : 2*z=(a+b)*((a+b)+1)+2*b) : z=modelCantor a b := by
 apply mul_left_cancel₀ (by simp : (2:M)≠0)
 exact h.trans (modelCantor_equation a b).symm

omit [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem exactCantorGraph_nat (z a b : Nat) : exactCantorGraph.val.Evalb ![z,a,b] ↔ z=cantor a b := by
 let s := a+b
 have hr : s%2=0 ∨ s%2=1 := by omega
 have hm : (s*(s+1))%2=0 := by
   rcases hr with h|h <;> simp [Nat.mul_mod,Nat.add_mod,h]
 have he := Nat.mod_add_div (s*(s+1)) 2
 simp only [hm,Nat.zero_add] at he
 simp only [exactCantorGraph]
 change 2*z=(a+b)*((a+b)+1)+2*b ↔ z=cantor a b
 unfold cantor
 dsimp [s] at he
 omega

end ZFR.ArithmeticRepresentation
