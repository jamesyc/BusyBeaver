module
public import I3_334Support.Equations.EquationModelLaws
public import I3_334Support.Equations.RecoveredI3
public import I3_334Support.Logic.Completeness
@[expose] public section

namespace PalomarI3380

open Logic Expanded SquareRepresentation.SetContext

/-- A countable model of ZFC + I3 yields the class algebra in which the
native equations hold and the domain differs from the embedding. -/
theorem underivability_of_countable_zfci3_model {V : Type} {E : V → V → Prop}
    (enumerated : Listing V) (model : ZFCI3Model E) :
    ¬Derives Manifest.final (.const .D) (.const .J) := by
  let v := enumerated.get 0
  have nonempty : Nonempty V := ⟨v⟩
  have ordinary : ZFCModel E := fun p hp => model p
    (hp.elim Or.inl (fun h => Or.inr (Or.inl h)))
  have large : Internal.HasI3 E :=
    (SetFormula.holds_i3 (E := E) (env := fun _ => v)).mp (model _ (Or.inr (Or.inr rfl)) _)
  obtain ⟨G,axioms,minimum⟩ := OrdinaryContext.amenable_global_order ordinary nonempty enumerated
  exact EquationModel.underivability axioms nonempty minimum large

theorem equational_underivability_of_consistency (h : ZFCI3Consistent) :
    ¬Derives Manifest.final (.const .D) (.const .J) := by
  obtain ⟨V,E,⟨enumerated⟩,model⟩ := countable_zfci3_model_of_consistency h
  exact underivability_of_countable_zfci3_model enumerated model

theorem equational_underivability_iff_consistency :
    (¬Derives Manifest.final (.const .D) (.const .J)) ↔ ZFCI3Consistent :=
  ⟨consistency_of_equational_underivability,equational_underivability_of_consistency⟩

end PalomarI3380
