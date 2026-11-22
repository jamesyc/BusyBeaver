module
public import Foundation.FirstOrder.SetTheory.ZF.Model
@[expose] public section
namespace ZF192Support.Independence
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory FFL.Entailment

/-- A consistent ZF has a model. -/
lemma exists_zf_model [hZF : Consistent (𝗭𝗙 : SetTheory)] :
    ∃ (V : Type) (_ : SetStructure V) (_ : Nonempty V), V↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  by_contra hne
  push Not at hne
  have hbot : (𝗭𝗙 : SetTheory) ⊢ ⊥ :=
    SetTheory.complete.{0} _ ⊥ fun V _ _ hV => (hne V _ _ hV).elim
  exact (consistent_iff_unprovable_bot.mp hZF) hbot

end ZF192Support.Independence
