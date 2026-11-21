module
public import Foundation.FirstOrder.SetTheory.ZF.ZF
@[expose] public section
namespace ZF207.OmegaInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
/-- Relational domain for arithmetic inside the pure membership language. -/
def domain : SetTheorySemisentence 1 := “x. ∃ w, !isω w ∧ x ∈ w”
def zeroGraph : SetTheorySemisentence 1 := isEmpty
def succGraph : SetTheorySemisentence 2 := succ.dfn
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
@[simp] theorem domain_eval (v : Fin 1 → V) : domain.Evalb v ↔ v 0 ∈ (ω : V) := by
 simp [domain, ω.defined.iff]
@[simp] theorem zero_eval (v : Fin 1 → V) : zeroGraph.Evalb v ↔ v 0 = (∅ : V) := by
 simp [zeroGraph, isEmpty, mem_ext_iff]
@[simp] theorem succ_eval (v : Fin 2 → V) : succGraph.Evalb v ↔ v 0 = succ (v 1) :=
 succ.defined.eval_iff v
/-- The domain is nonempty in every ZF model, not just the standard universe. -/
theorem domain_nonempty : (𝗭𝗙 : SetTheory) ⊢ “∃ x, !domain x” := by
 apply SetTheory.complete.{0}
 intro V _ _ _
 simpa [models_iff] using (show ∃ x : V, x ∈ (ω : V) from ⟨∅,empty_mem_ω⟩)
end ZF207.OmegaInterpretation
