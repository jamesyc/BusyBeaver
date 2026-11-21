module
public import I0451.Logic.ElementarySets
public import I0451.Logic.RankCollection
public import I0451.Logic.TruthFamily

/-! Marking the hierarchy graph lets us prove rank preservation in the
ambient ZF model. The transitive domain containing the graph need
only see its entries as ordered pairs. -/
@[expose] public section
namespace I0451.Logic.ZFModel

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.AssignmentCode I0451.Logic.SetAssignments

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local notation "E" => (fun (x y : V) => x ∈ y)

attribute [local irreducible] cumulativeLevel

theorem rankGraphEntry_defined :
    ℒₛₑₜ-function₁[V] (fun x : V => ⟨x,cumulativeLevel x⟩ₖ) := by
  have levels := cumulativeLevel_defined (V := V)
  definability

noncomputable def rankGraph (bound : V) : V :=
  repl (fun x => ⟨x,cumulativeLevel x⟩ₖ) rankGraphEntry_defined bound

theorem rankGraph_entry (bound index value : V) :
    ⟨index,value⟩ₖ ∈ rankGraph bound ↔ index ∈ bound ∧ value = cumulativeLevel index := by
  rw [rankGraph, repl_spec]
  constructor
  · rintro ⟨i, hi, pair⟩
    obtain ⟨rfl, rfl⟩ := kpair_inj pair
    exact ⟨hi, rfl⟩
  · rintro ⟨inside, rfl⟩
    exact ⟨index, inside, rfl⟩

theorem rankGraph_values_in {d a i : V} (transitive : IsTransitive d)
    (graph : rankGraph a ∈ d) (stage : i ∈ a) :
    i ∈ d ∧ cumulativeLevel i ∈ d := by
  have entry := (rankGraph_entry a i _).mpr ⟨stage, rfl⟩
  exact pair_components_in transitive (transitive.transitive _ graph _ entry)

theorem fixed_rank_level {d a i e : V} (transitive : IsTransitive d) (graph : rankGraph a ∈ d)
    {j : Domain E d → Domain E d} (elementary : Identity.Elementary (domainMem d) j)
    (decoded : Encodes E d e j) (fixedGraph : j ⟨rankGraph a, graph⟩ = ⟨rankGraph a, graph⟩)
    (stage : i ∈ a) (fixedIndex : At E e i i) : At E e (cumulativeLevel i) (cumulativeLevel i) := by
  have entry := (rankGraph_entry a i _).mpr ⟨stage, rfl⟩
  let pair : Domain E d := ⟨⟨i,cumulativeLevel i⟩ₖ, transitive.transitive _ graph _ entry⟩
  obtain ⟨iMem, valueMem⟩ := rankGraph_values_in transitive graph stage
  let index : Domain E d := ⟨i, iMem⟩
  let value : Domain E d := ⟨cumulativeLevel i, valueMem⟩
  let fn : Domain E d := ⟨rankGraph a, graph⟩
  have iFixed : (j index).val = i := (decoded.at_iff index i).mp fixedIndex
  have transported := (elementary.mem_iff pair fn).mp entry
  rw [show j fn = fn from fixedGraph] at transported
  have pairEq := elementary_preserves_kpair transitive elementary (p := pair) (x := index) (y := value) rfl
  change (j pair).val ∈ rankGraph a at transported
  rw [pairEq, iFixed] at transported
  exact (decoded.at_iff value _).mpr ((rankGraph_entry a i _).mp transported).2

theorem fixed_sets_below {d e : V} (transitive : IsTransitive d) (a : Ordinal V)
    (graph : rankGraph (a : V) ∈ d) {j : Domain E d → Domain E d}
    (elementary : Identity.Elementary (domainMem d) j) (decoded : Encodes E d e j)
    (fixedGraph : j ⟨rankGraph (a : V), graph⟩ = ⟨rankGraph (a : V), graph⟩)
    (ordinals : ∀ i ∈ (a : V), At E e i i) :
    ∀ i ∈ (a : V), ∀ x ∈ cumulativeLevel i, At E e x x := by
  let P (i : V) := i ∈ (a : V) → ∀ x ∈ cumulativeLevel i, At E e x x
  have defined : ℒₛₑₜ-predicate P := by
    have levels := cumulativeLevel_defined (V := V)
    have relations := At_definable (V := V)
    unfold P
    definability
  have holds : ∀ i : Ordinal V, P i := by
    apply transfinite_induction P defined
    intro i previous inBound x belongs
    obtain ⟨k, earlier, subset⟩ := (mem_cumulativeLevel i).mp belongs
    have kBound := a.ordinal.toIsTransitive.transitive i.val inBound k earlier
    have kOrdinal : IsOrdinal k := IsOrdinal.of_mem earlier
    have fixedLevel := fixed_rank_level transitive graph elementary decoded fixedGraph kBound (ordinals k kBound)
    have levelD := (rankGraph_values_in transitive graph kBound).2
    have xD : x ∈ d := transitive.transitive _ (rankGraph_values_in transitive graph inBound).2 _ belongs
    let y : Domain E d := ⟨x, xD⟩
    let level : Domain E d := ⟨cumulativeLevel k, levelD⟩
    have levelFixed : (j level).val = cumulativeLevel k := (decoded.at_iff level _).mp fixedLevel
    have imageSubset := (elementary_preserves_subset transitive elementary y level).mp subset
    rw [levelFixed] at imageSubset
    have same (z : V) (zLevel : z ∈ cumulativeLevel k) : z ∈ x ↔ z ∈ (j y).val := by
      have zD := transitive.transitive _ levelD z zLevel
      let point : Domain E d := ⟨z, zD⟩
      have inLower : kOrdinal.toOrdinal < i := earlier
      have fixedZ : (j point).val = z :=
        (decoded.at_iff point _).mp (previous kOrdinal.toOrdinal inLower kBound z zLevel)
      have relation := elementary.mem_iff point y
      change z ∈ x ↔ (j point).val ∈ (j y).val at relation
      rwa [fixedZ] at relation
    apply (decoded.at_iff y _).mpr
    apply mem_ext_iff.mpr
    intro z
    exact ⟨fun hz => (same z (imageSubset z hz)).mpr hz,
      fun hz => (same z (subset z hz)).mp hz⟩
  intro i earlier
  exact holds (IsOrdinal.of_mem earlier).toOrdinal earlier

end I0451.Logic.ZFModel
