module
public import I0451.Logic.CanonicalTruthFamily
public import I0451.Logic.ParameterEnvelope
public import I0451.Logic.RankGraph
public import I0451.Logic.CodedRestrictions
public import I0451.Logic.FiniteFormulaEncoding
public import I0451.Logic.TruthRepresentation

/-! Reduce a moved set in the emitted sentence to a moved ordinal in
any transitive domain containing the rank bound. The resulting
restriction preserves the internally coded satisfaction relation. -/
@[expose] public section
namespace I0451.Logic.SetAssignments

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.AssignmentCode I0451.Logic.ZFModel

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local notation "E" => (fun (x y : V) => x ∈ y)

def CodedCriticalPoint (M code κ : V) : Prop :=
  κ ∈ M ∧ ¬At E code κ κ ∧ ∀ γ ∈ κ, At E code γ γ

def ProtoBerkeleyOrdinal (bound : V) : Prop :=
  IsOrdinal bound ∧ ∀ M, IsTransitive M → bound ∈ M →
    ∃ code κ, κ ∈ bound ∧ CodedElementary M code ∧ CodedCriticalPoint M code κ

private theorem movedBelow_definable (bound code : V) :
    ℒₛₑₜ-predicate (fun k => k ∈ bound ∧ ¬At E code k k) := by
  have symbols := At_definable (V := V)
  definability

theorem berkeleyFormula_has_ordinal_bound (formula : SetSentences.BerkeleyFormula E) :
    ∃ bound : V, ProtoBerkeleyOrdinal bound := by
  classical
  obtain ⟨a, covers⟩ := berkeleyFormula_iff_generated.mp formula
  obtain ⟨bound, atRank⟩ := cumulativeLevel_covers a
  refine ⟨bound.val, bound.ordinal, fun M transM boundM => ?_⟩
  let graph := rankGraph (bound : V)
  let values := ⟨a, (ω : V)⟩ₖ
  let extras := ⟨graph, values⟩ₖ
  let parameter := ⟨M, extras⟩ₖ
  obtain ⟨D, mark, transD, named⟩ := parameterEnvelope_fixes parameter
  obtain ⟨mIn, extrasIn⟩ := pair_components_in transD mark
  obtain ⟨graphIn, valuesIn⟩ := pair_components_in transD extrasIn
  obtain ⟨aIn, omegaIn⟩ := pair_components_in transD valuesIn
  have usesNaturals := transD.transitive _ omegaIn
  obtain ⟨code, moved, compared⟩ := covers D (fun x hx y hy => transD.transitive x hx y hy) aIn
  have elementaryCode := generatedComparison_codedElementary transD usesNaturals compared
  obtain ⟨j, decoded, elementary⟩ := elementaryCode.decoded_elementary
  let Mpoint : Domain E D := ⟨M, mIn⟩
  let extrasPoint : Domain E D := ⟨extras, extrasIn⟩
  let valuesPoint : Domain E D := ⟨values, valuesIn⟩
  let graphPoint : Domain E D := ⟨graph, graphIn⟩
  have parameterFixed := named j elementary
  obtain ⟨Mfixed, extrasFixed⟩ := elementary_fixed_pair_components transD elementary
    (p := ⟨parameter, mark⟩) (x := Mpoint) (y := extrasPoint) rfl parameterFixed
  have graphFixed := (elementary_fixed_pair_components transD elementary
    (p := extrasPoint) (x := graphPoint) (y := valuesPoint) rfl extrasFixed).1
  have ordinalMoved : ∃ k ∈ (bound : V), ¬At E code k k := by
    by_contra noOrdinal
    have fixes : ∀ k ∈ (bound : V), At E code k k := by
      intro k below
      by_contra neg
      exact noOrdinal ⟨k, below, neg⟩
    have fixedLower := fixed_sets_below transD bound graphIn elementary decoded graphFixed fixes
    obtain ⟨x, inA, notFixed⟩ := moved
    obtain ⟨k, below, aSubset⟩ := (mem_cumulativeLevel bound).mp atRank
    exact notFixed (fixedLower k below x (aSubset x inA))
  let movedBelow (k : V) : Prop := k ∈ (bound : V) ∧ ¬At E code k k
  have definableMoved : ℒₛₑₜ-predicate movedBelow := movedBelow_definable (bound : V) code
  have someOrdinal : ∃ k : Ordinal V, movedBelow k := by
    obtain ⟨k, below, changed⟩ := ordinalMoved
    exact ⟨(IsOrdinal.of_mem below).toOrdinal, below, changed⟩
  obtain ⟨κ, movedK, least⟩ := exists_minimal movedBelow definableMoved someOrdinal
  have kInM : (κ : V) ∈ M := transM.transitive _ boundM _ movedK.1
  have subsetMD : M ⊆ D := transD.transitive M mIn
  have fixedCode : At E code M M := (decoded.at_iff Mpoint M).mpr (congrArg Subtype.val Mfixed)
  have preserves (x : V) (xIn : x ∈ M) (y : V) (value : At E code x y) : y ∈ M := by
    let point : Domain E D := ⟨x, subsetMD x xIn⟩
    have belongs := (elementary.mem_iff point Mpoint).mp xIn
    rw [Mfixed] at belongs
    have result : (j point).val = y := (decoded.at_iff point y).mp value
    exact result ▸ belongs
  have restriction := elementaryCode.restrictGraph transM subsetMD mIn fixedCode preserves
  refine ⟨restrictedGraph code M, κ.val, movedK.1, restriction, kInM, ?_, ?_⟩
  · intro fixed
    exact movedK.2 ((restrictedGraph_at code M _ _).mp fixed).2.2
  · intro γ before
    have gInM : γ ∈ M := transM.transitive _ kInM γ before
    have belowBound := bound.ordinal.toIsTransitive.transitive κ.val movedK.1 γ before
    let gOrd : Ordinal V := (IsOrdinal.of_mem before).toOrdinal
    have fixed : At E code γ γ := by
      by_contra changed
      exact not_lt_of_ge (least gOrd ⟨belowBound, changed⟩) (show gOrd < κ from before)
    exact (restrictedGraph_at code M _ _).mpr ⟨gInM, gInM, fixed⟩

end I0451.Logic.SetAssignments
