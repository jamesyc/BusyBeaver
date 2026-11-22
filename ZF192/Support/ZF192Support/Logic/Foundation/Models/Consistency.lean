module
public import ZF192Support.Logic.Source.Models
public import Foundation.FirstOrder.SetTheory.ZF.ZF
public import Foundation.FirstOrder.SetTheory.Basic.Misc
@[expose] public section
namespace ZFR.NDSemantics
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
/-- The ONLY remaining input is source axiom validity in arbitrary actual ZF
models. Completeness turns a source contradiction into a Foundation proof of
bottom; no existence of a ZF model is separately assumed. -/
theorem foundation_bot_of_source_bot
 (valid : ∀ (V : Type) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
   AxiomsTrue (fun x y : V => x ∈ y))
 (h : ZFR.SourceTheorem Formula.bot) :
 (𝗭𝗙 : SetTheory) ⊢ (⊥ : SetTheorySentence) := by
 apply SetTheory.complete.{0}
 intro V _ _ _
 have hf : False := consistent_of_model (fun x y : V => x ∈ y) (valid V) h
 exact False.elim hf

theorem source_consistent_of_foundation_not_bot
 (valid : ∀ (V : Type) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
   AxiomsTrue (fun x y : V => x ∈ y))
 (hc : ¬ ((𝗭𝗙 : SetTheory) ⊢ (⊥ : SetTheorySentence))) :
 (¬ ZFR.SourceTheorem Formula.bot) :=
 fun h => hc (foundation_bot_of_source_bot valid h)
theorem source_consistent_of_foundation_consistent
 (valid : ∀ (V : Type) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙],
   AxiomsTrue (fun x y : V => x ∈ y))
 [FFL.Entailment.Consistent (𝗭𝗙 : SetTheory)] :
 (¬ ZFR.SourceTheorem Formula.bot) :=
 source_consistent_of_foundation_not_bot valid FFL.Entailment.Consistent.not_bot
end ZFR.NDSemantics
