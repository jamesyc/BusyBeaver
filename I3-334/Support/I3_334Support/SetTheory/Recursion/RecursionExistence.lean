module
public import I3_334Support.SetTheory.Graphs.GraphUpdates
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetRecursion

open Logic

variable {A V : Type} {M : Algebra A} {N : SetContext M V} (R : SetRecursion N)

private theorem restriction_stable {f cut g x value : V} (hn : ¬ N.mem x cut)
    (h : N.Restricts f cut g) :
    N.Restricts (N.adjoinValue f x value) cut g := by
  intro p
  rw [h p, SetContext.adjoinValue, N.mem_union₂, N.mem_singleton]
  constructor
  · exact fun ⟨hf, coordinates⟩ => ⟨Or.inl hf, coordinates⟩
  · rintro ⟨hf | absolute, a, ha, b, pair⟩
    · exact ⟨hf, a, ha, b, pair⟩
    · subst p
      have same := (Internal.orderedPair_injective pair (N.orderedPair_intro x value)).1
      exact (hn (same ▸ ha)).elim

/-- Extend a graph approximation by the next value obtained from the
recursion rule, keeping every earlier update equation. -/
theorem extend_solution {x cut f : V} (hx : N.mem x R.domain) (hc : R.IsCut x cut)
    (sol : R.Solution cut f) :
    ∃ g, R.FullSolution x g := by
  obtain ⟨inclusive, shape⟩ := R.through_exists x
  obtain ⟨value, computes⟩ := R.update_exists x f
  let graph := N.adjoinValue f x value
  have split (z : V) : N.mem z inclusive ↔ N.mem z cut ∨ z = x := by
    rw [shape, hc]
    constructor
    · rintro ⟨hz, h | h⟩
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr h
    · rintro (⟨hz, h⟩ | rfl)
      · exact ⟨hz, Or.inl h⟩
      · exact ⟨hx, Or.inr rfl⟩
  have notCut : ¬N.mem x cut := fun h => R.wellOrder.irrefl x hx ((hc x).mp h).2
  have values := N.at_adjoinValue f x value
  have domain : inclusive = N.succDomain cut x :=
    N.ext _ _ fun z => (split z).trans (N.mem_succDomain cut x z).symm
  refine ⟨graph, inclusive, shape, ⟨domain.symm ▸ N.function_adjoinValue sol.functionOn notCut, ?_⟩⟩
  · intro z hz
    rcases (split z).mp hz with earlier | eq
    · obtain ⟨d, g, b, dCut, prior, old, rule⟩ := sol.agrees z earlier
      obtain ⟨zDomain, order⟩ := (hc z).mp earlier
      have notPrior : ¬N.mem x d := by
        intro h
        exact SetContext.WellOrderOn.asymm N R.wellOrder zDomain hx order ((dCut x).mp h).2
      exact ⟨d, g, b, dCut, restriction_stable (N := N) notPrior prior,
        (values z b).mpr (Or.inl old), rule⟩
    · subst z
      have restrictSame : N.Restricts f cut f := by
        intro p
        constructor
        · intro h
          obtain ⟨z, b, hz, pair⟩ := sol.functionOn.2 p h
          exact ⟨h, z, hz, b, pair⟩
        · exact And.left
      exact ⟨cut, f, value, hc, restriction_stable (N := N) notCut restrictSame,
        (values x value).mpr (Or.inr ⟨rfl, rfl⟩), computes⟩

private theorem failure_set : ∃ set, ∀ x, N.mem x set ↔
    N.mem x R.domain ∧ ¬∃ graph, R.FullSolution x graph := by
  let params := [R.domain, R.orderKey, R.updateKey]
  have formula := Definable.not (Definable.ex (R.full_solution_definable
    (n := 6) (d := 3) (o := 4) (u := 5) (x := 1) (f := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide)))
  obtain ⟨bad, spec⟩ := N.separate params formula R.domain R.domain
  refine ⟨bad, fun x => (spec x).trans (and_congr_right fun _ => not_congr ?_)⟩
  change (∃ graph b, R.IsThrough x b ∧ Internal.FunctionOn N.mem graph b ∧
    (∀ y, N.mem y b → ∃ cut prior value, R.IsCut y cut ∧ N.Restricts graph cut prior ∧
      Internal.At N.mem graph y value ∧ R.update R.updateKey y prior value)) ↔ _
  constructor
  · rintro ⟨g, a, h, funOn, eq⟩
    exact ⟨g, a, h, ⟨funOn, eq⟩⟩
  · rintro ⟨g, a, h, solution⟩
    exact ⟨g, a, h, solution.functionOn, solution.agrees⟩

theorem full_solution_exists {x : V} (hx : N.mem x R.domain) : ∃ f, R.FullSolution x f := by
  classical
  obtain ⟨bad, spec⟩ := R.failure_set
  have inside : N.Subset bad R.domain := fun x hx => ((spec x).mp hx).1
  apply Classical.byContradiction
  intro no
  have inhabited : N.NonemptySet bad := ⟨x, (spec x).mpr ⟨hx, no⟩⟩
  obtain ⟨y, hy, minimum⟩ := R.wellOrder.least bad inside inhabited
  have earlier : ∀ z, N.mem z R.domain → R.before z y → ∃ f, R.FullSolution z f := by
    intro z hz zy
    apply Classical.byContradiction
    intro h
    have badZ := (spec z).mpr ⟨hz, h⟩
    rcases minimum z badZ with same | yz
    · exact R.wellOrder.irrefl y (inside y hy) (same.symm ▸ zy)
    · exact SetContext.WellOrderOn.asymm N R.wellOrder hz (inside y hy) zy yz
  obtain ⟨a, cut⟩ := R.cut_exists y
  obtain ⟨f, sol⟩ := R.gather_solutions a (R.cut_initial (inside y hy) cut) fun z hz =>
    let where_ := (cut z).mp hz; earlier z where_.1 where_.2
  exact ((spec y).mp hy).2 (R.extend_solution (inside y hy) cut sol)

/-- Transfinite recursion needs only the internally wellordered
index set, full definable images, and the specified update operation. -/
theorem solution_exists : ∃ f, R.Solution R.domain f :=
  R.gather_solutions R.domain R.initial_domain fun _ => R.full_solution_exists

end PalomarI3380.SquareRepresentation.SetRecursion
