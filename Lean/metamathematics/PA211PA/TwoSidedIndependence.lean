module

public import User211LiteralEndpoint

@[expose] public section

/-! Two-sided independence for the exact literal 211-state machine.
Foundation's standard model supplies PA soundness and consistency in Lean's
metatheory. The imported consistency-conditional statements are unchanged. -/

namespace PA211.UserCandidate.PA.Independence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

/-- Soundness in Nat rules out a PA proof of the exact nonhalting sentence's negation. -/
theorem nonhalting_irrefutable (hcons : PA215.PA.Consistent) :
    theory ⊬ ∼ExactHaltingFormula.nonhaltingSentence := by
  intro hp
  have ht := consequence_iff.mp (Theory.Proof.sound hp) Nat inferInstance
  have hn := InternalUnprovability.nonhalting_true hcons
  have hf : ¬ (Nat ⊧/![] ExactHaltingFormula.nonhaltingSentence) := by
    simpa [models_iff, Semiformula.Realize, Semiformula.Evalb] using ht
  exact hf hn

/-- Neither the exact nonhalting sentence nor its negation is provable in PA. -/
theorem two_sided_independence :
    (theory ⊬ ExactHaltingFormula.nonhaltingSentence) ∧
    (theory ⊬ ∼ExactHaltingFormula.nonhaltingSentence) :=
  ⟨InternalUnprovability.nonhalting_unprovable inferInstance,
    nonhalting_irrefutable inferInstance⟩

/-- Nonhalting of the published literal table, starting at state 0 on a blank tape. -/
theorem machine_nonhalting :
    ¬ PA215.Zip.Halts Dense.machine (PA215.Zip.zc 0 [] []) :=
  consistent_literal_nonhalting inferInstance

end PA211.UserCandidate.PA.Independence
