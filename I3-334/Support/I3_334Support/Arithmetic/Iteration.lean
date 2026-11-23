module
public import Foundation.FirstOrder.Arithmetic.HFS.PRF
public import Foundation.FirstOrder.Arithmetic.Induction.Basic
@[expose] public section

namespace PalomarI3380.ArithmeticMachine

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

def iterationBlueprint (graph : 𝚺ᴬ₁.Semisentence 2) : PR.Blueprint 1 where
  zero := .mkSigma “out start. out = start”
  succ := .mkSigma “out previous time start. !graph out previous”

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def iterationConstruction (graph : 𝚺ᴬ₁.Semisentence 2) (f : M → M)
    (meaning : ∀ y x, graph.val.Evalb ![y,x] ↔ y = f x) :
    PR.Construction M (iterationBlueprint graph) where
  zero := fun v => v 0
  succ := fun _ _ code => f code
  zero_defined := .mk fun v => by simp [iterationBlueprint]
  succ_defined := .mk fun v => by simpa [iterationBlueprint] using meaning (v 0) (v 1)

end PalomarI3380.ArithmeticMachine
