module
public import Foundation.FirstOrder.SetTheory.Recursion
@[expose] public section
namespace FFL.FirstOrder.SetTheory.ScottHulls
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

/-- Definable stage operator: union of powersets of previous values. -/
noncomputable def stageStep (g : V) : V := ⋃ˢ (repl power (by definability) (range g))

instance stageStep_definable : ℒₛₑₜ-function₁ (stageStep : V → V) := by
 unfold stageStep
 definability

/-- Cumulative-stage candidate in an ARBITRARY ZF model, not concrete ZFSet. -/
noncomputable def hierarchy (a : V) : V :=
 Replacement.transfiniteRec stageStep (by definability) a

instance hierarchy_definable : ℒₛₑₜ-function₁ (hierarchy : V → V) :=
 Replacement.transfiniteRec_definable (by definability)

theorem hierarchy_recursion (a : Ordinal V) :
 hierarchy (a : V) = stageStep
   (repl (fun b : V => ⟨b, hierarchy b⟩ₖ) (by definability) (a : V)) := by
 exact Replacement.transfiniteRec_spec stageStep (by definability) a

end FFL.FirstOrder.SetTheory.ScottHulls
