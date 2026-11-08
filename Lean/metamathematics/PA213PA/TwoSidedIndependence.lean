import PA213PA.NonhaltingUnprovability

/-! Two-sided independence of the exact PA213 nonhalting sentence.

Foundation proves that Nat models Peano, and derives PA consistency by
logical soundness. These are metatheorems in Lean, not PA proofs of its own
soundness or consistency. The original consistency-conditional endpoint
remains unchanged.
-/

namespace PA213.PA.Independence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

/-- Standard-model soundness rules out a PA proof of the negation of the
exact nonhalting sentence. The model instance is supplied by Foundation.
The consistency premise mirrors the original endpoint; it also follows from
that model instance, as `two_sided_independence` uses. -/
theorem nonhalting_irrefutable (hcons : PA215.PA.Consistent) :
    theory ⊬ ∼ExactHaltingFormula.nonhaltingSentence := by
  intro hp
  have ht := consequence_iff.mp (Theory.Proof.sound hp) Nat inferInstance
  have hn := InternalUnprovability.nonhalting_true hcons
  have hf : ¬ (Nat ⊧/![] ExactHaltingFormula.nonhaltingSentence) := by
    simpa [models_iff, Semiformula.Realize, Semiformula.Evalb] using ht
  exact hf hn

/-- Neither the exact nonhalting sentence nor its negation is provable in
PA. Foundation's standard-model consistency instance discharges the
consistency premises in Lean's metatheory, without a new axiom. -/
theorem two_sided_independence :
    (theory ⊬ ExactHaltingFormula.nonhaltingSentence) ∧
    (theory ⊬ ∼ExactHaltingFormula.nonhaltingSentence) :=
  ⟨InternalUnprovability.nonhalting_unprovable inferInstance,
    nonhalting_irrefutable inferInstance⟩

/-- The physical machine does not halt from the blank tape. Foundation's
standard-model consistency instance discharges the premise of
`consistent_machine_nonhalting` in Lean's metatheory, without a new axiom. -/
theorem machine_nonhalting :
    ¬ PA215.Zip.Halts PA213.CandidateTable.machine PA213.Startup.blank :=
  consistent_machine_nonhalting inferInstance

end PA213.PA.Independence
