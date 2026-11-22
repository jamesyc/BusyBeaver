module
public import ZF192Support.Calculus.Internal.Tait.Derivation
public import ZF192Support.Calculus.Internal.EqualityModel
@[expose] public section
/-! # The machine's calculus as the logic pass's calculus

A Σ1 provability predicate closed under the machine's rules gives an
`IntLogic`, with the defined equality binding the reserved label `rlab 0`. So
an internal refutation of a set-language theory whose axioms translate to such
theorems gives an internal proof of the falsity code. -/
namespace ZF192Support.Internal.Tait
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {D : 𝚺ᴬ₁.Semisentence 1}

/-- The logic pass's calculus from the machine's rules. -/
noncomputable def _root_.ZF192Support.Internal.ProvRules.intLogic (h : ProvRules D V) : IntLogic V where
  D := D
  S := h.eqLogic (rlab 0)
  codes_eq := rfl
  prov_iff _ := Iff.rfl
  E_eq _ _ := rfl
  ok_iff _ := Iff.rfl

/-- Internal refutations of a set-language theory become proofs of `1`. -/
theorem _root_.ZF192Support.Internal.ProvRules.refutation [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] (h : ProvRules D V) (U : Theory ℒₛₑₜ) [U.Δ₁]
    (hU : ∀ p ∈ U.Δ₁Class (V := V), ∀ m, D.val.Evalb ![chiS m p])
    (hr : Bootstrapping.Provable U (^⊥ : V)) : D.val.Evalb ![(1 : V)] :=
  refutation_tr h.intLogic U hU hr

end ZF192Support.Internal.Tait
