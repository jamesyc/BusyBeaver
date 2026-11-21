module
public import I3_380.Logic.HenkinModel
public import I3_380.Logic.Soundness
@[expose] public section

namespace PalomarI3380.Logic

theorem zfci3_equalityAxioms : Theory.EqualityAxioms ZFCI3Axiom :=
  ⟨Or.inl (Or.inl (by simp [FixedAxiom])),
   Or.inl (Or.inl (by simp [FixedAxiom])),
   Or.inl (Or.inl (by simp [FixedAxiom])),
   Or.inl (Or.inl (by simp [FixedAxiom]))⟩

theorem countable_zfci3_model_of_consistency (h : ZFCI3Consistent) :
    ∃ (V : Type) (E : V → V → Prop), Nonempty (Expanded.Listing V) ∧ ZFCI3Model E :=
  Theory.countable_model_of_consistency ZFCI3Axiom h (fun _ => zfci3_closed) zfci3_equalityAxioms

/-- Completeness for closed sentences of the actual source proof system. -/
theorem zfci3_complete {p : Formula} (closed : Closed p)
    (valid : ∀ (V : Type) (E : V → V → Prop), Nonempty V → ZFCI3Model E →
      ∀ env : Nat → V, eval E p env) : ZFCI3Provable p := by
  classical
  by_cases consistent : ZFCI3Consistent
  · apply Classical.byContradiction
    intro missing
    let extension := Theory.add ZFCI3Axiom (Neg p)
    have consistentExt : extension.Consistent :=
      (Theory.consistent_add_iff consistent).mpr (fun hn => missing hn.neg_elim)
    have closedExt : ∀ p, extension p → Closed p := fun q h =>
      h.elim (fun eq => eq.symm ▸ And.intro closed trivial) zfci3_closed
    have eq := zfci3_equalityAxioms
    have eqExt : Theory.EqualityAxioms extension :=
      ⟨Or.inr eq.refl,Or.inr eq.symm,Or.inr eq.trans,Or.inr eq.membership⟩
    obtain ⟨V,E,⟨listing⟩,model⟩ := extension.countable_model_of_consistency consistentExt closedExt eqExt
    let env : Nat → V := fun _ => listing.get 0
    exact model (Neg p) (Or.inl rfl) env
      (valid V E ⟨env 0⟩ (fun q ax => model q (Or.inr ax)) env)
  · exact (Classical.byContradiction (fun hn => consistent hn) : Theory.Derives ZFCI3Axiom .bot).explode

end PalomarI3380.Logic
