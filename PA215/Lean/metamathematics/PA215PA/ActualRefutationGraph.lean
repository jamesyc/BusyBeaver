import PA215PA.ActualCheckerStandard
namespace PA215.PA.ActualRefutationGraph
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open ActualCheckerBlueprint ActualCheckerStandard ActualTableCoding
open NativeCalculus.ActualBasis.Code

/-- The V1 refutation graph uses the actual-basis proof codec. -/
noncomputable def formula : 𝚺ᴬ₁.Semisentence 1 := .mkSigma “code. !verifyGraph 2 code”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem formula_graph (code : V) : formula.val.Evalb ![code] ↔ verifyValue code=2 := by
  simp [formula,verify_graph,eq_comm]

theorem formula_standard (code : Nat) : formula.val.Evalb ![code] ↔ verify code=some 1 := by
  rw [formula_graph,verify_standard]
  constructor
  · intro h
    apply optionCode_injective
    exact h
  · rintro h
    rw [h]
    rfl

#print axioms formula_graph
#print axioms formula_standard
end PA215.PA.ActualRefutationGraph
