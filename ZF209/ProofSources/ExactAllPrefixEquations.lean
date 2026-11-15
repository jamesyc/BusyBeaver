module
public import PrimitiveRecursionEquations
public import NumericTheory
@[expose] public section
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace ZFR.ArithmeticRepresentation
open C209Soundness

theorem allNode_polynomial (a : Nat) : sourceNode 6 a 0=4*(a*(a+1))+6 := by
 have hr : a%2=0 ∨ a%2=1 := by omega
 have hm : (a*(a+1))%2=0 := by
   rcases hr with h|h <;> simp [Nat.mul_mod,Nat.add_mod,h]
 have he := Nat.mod_add_div (a*(a+1)) 2
 simp only [hm,Nat.zero_add] at he
 unfold sourceNode cantor
 simp only [Nat.add_zero]
 omega

def allPrefixBlueprint : PR.Blueprint 1 where
 zero := .mkSigma “z a. z = a”
 succ := .mkSigma “u z i a. u = 4 * (z * (z + 1)) + 6”

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def allPrefixConstruction : PR.Construction M allPrefixBlueprint where
 zero := fun v => v 0
 succ := fun _ _ z => 4*(z*(z+1))+6
 zero_defined := .mk (by intro v; simp [allPrefixBlueprint,numeral_eq_natCast])
 succ_defined := .mk (by intro v; simp [allPrefixBlueprint,numeral_eq_natCast])

omit [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem allPrefix_result_exact (n a : Nat) :
 (allPrefixConstruction (M := Nat)).result ![a] n=numericAllPrefix n a := by
 induction n with
 | zero => rw [PR.Construction.result_zero]; rfl
 | succ n ih =>
   rw [PR.Construction.result_succ]
   change 4*((allPrefixConstruction (M := Nat)).result ![a] n *
     ((allPrefixConstruction (M := Nat)).result ![a] n+1))+6=_
   rw [ih,←allNode_polynomial]
   rfl

end ZFR.ArithmeticRepresentation
