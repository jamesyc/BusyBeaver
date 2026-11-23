module
public import I3_334Support.SetTheory.Rank.RankRelations
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Logic Manifest SetContext
variable {A V : Type} {M : Algebra A} {N : NamedModel M V}

namespace Definable

theorem stage {n i : Nat} (hi : i < n) :
    N.square.Definable n (fun s => N.square.Stage (s i)) :=
  atom (M.constant .S) hi hi

theorem unranked {n i : Nat} (hi : i < n) :
    N.square.Definable n (fun s => ¬ ∃ height, N.Rank height (s i)) :=
  not (ex (rank (N := N.toSetContext) (n := n + 1) (i := 0) (j := i + 1) (by omega) (by omega)))

theorem active {n i : Nat} (hi : i < n) :
    N.square.Definable n (fun s => N.square.activePoint (s i)) :=
  atom (M.constant .D) hi hi

end Definable

namespace NamedModel

variable (N : NamedModel M V)

theorem stage_cardinal_increase {a b α β : V}
    (sa : N.square.Stage a) (sb : N.square.Stage b) (inside : N.mem b a)
    (ca : N.Cardinal a α) (cb : N.Cardinal b β) :
    N.mem β α := by
  apply Classical.byContradiction
  intro no
  have boundAlpha : N.Subset α β := by
    apply (N.ordinal_subset_iff ca.ordinal cb.ordinal).mpr
    rcases N.ordinal_compare ca.ordinal cb.ordinal with before | same | after
    · exact Or.inl before
    · exact Or.inr same
    · exact (no after).elim
  have contained := N.injects_trans ca.equinumerous.1
    (N.injects_trans (N.injects_sub boundAlpha) cb.equinumerous.2)
  obtain ⟨f, injection⟩ := contained
  obtain ⟨formula, bound, meanings⟩ := Definable.graphValue (N := N.toSetContext) (n := 3) (i := 2) (j := 0) (k := 1)
    (by decide) (by decide) (by decide)
  obtain ⟨edge, described⟩ := N.square.represented_binary N.projections N.names [f] formula bound
  have desc (x y : V) : N.square.rel edge x y ↔ Internal.At N.mem f x y :=
    (described x y).trans (meanings _)
  apply no_stage_contraction N.laws N.names sa sb inside edge
  · intro x ha
    obtain ⟨y, hy, _⟩ := injection.functionOn.1 x ha
    exact ⟨y, injection.into x y hy, (desc x y).mpr hy⟩
  · exact fun x y z hx hy => injection.unique x y z ((desc x z).mp hx) ((desc y z).mp hy)

private theorem successor_heights (a : V) :
    ∃ lengths, ∀ length, N.mem length lengths ↔
      ∃ before, N.mem before a ∧ N.square.Stage before ∧
        ∃ height, N.Rank height before ∧ length = N.succ height := by
  have described := (Definable.stage (N := N) (n := 2) (i := 0) (by decide)).and
    (Definable.ex ((Definable.rank (N := N.toSetContext) (n := 3) (i := 0) (j := 1) (by decide) (by decide)).and
      (Definable.successor (N := N.toSetContext) (n := 3) (i := 0) (j := 2) (by decide) (by decide))))
  have one (x y z : V) :
      (N.square.Stage x ∧ ∃ h, N.Rank h x ∧ Internal.Succ N.mem h y) →
      (N.square.Stage x ∧ ∃ h, N.Rank h x ∧ Internal.Succ N.mem h z) → y = z := by
    rintro ⟨_, h, hRank, ySucc⟩ ⟨_, k, kRank, zSucc⟩
    cases N.rank_height_unique hRank kRank
    exact ((N.internal_succ _ _).mp ySucc).trans ((N.internal_succ _ _).mp zSucc).symm
  obtain ⟨lengths, found⟩ := N.image [] described one a
  refine ⟨lengths, fun length => (found length).trans ?_⟩
  constructor
  · rintro ⟨before, hb, stage, height, rank, next⟩
    exact ⟨before, hb, stage, height, rank, (N.internal_succ _ _).mp next⟩
  · rintro ⟨before, hb, stage, height, rank, next⟩
    exact ⟨before, hb, stage, height, rank, (N.internal_succ _ _).mpr next⟩

theorem stage_rank_of_predecessors {a : V} (ha : N.square.Stage a)
    (before : ∀ b, N.mem b a → N.square.Stage b → ∃ height, N.Rank height b) :
    ∃ height, N.Rank height a := by
  obtain ⟨lengths, members⟩ := N.successor_heights a
  have lengthsOrdinal (l : V) (hl : N.mem l lengths) : N.Ordinal l := by
    obtain ⟨_, _, _, b, hb, rfl⟩ := (members l).mp hl
    exact N.ordinal_succ hb.1
  let height := N.union lengths
  have ho : N.Ordinal height := N.ordinal_union lengths lengthsOrdinal
  obtain ⟨stage, rank⟩ := N.rank_exists ho
  have same : a = stage := by
    apply N.ext
    intro x
    rw [N.mem_rank_iff rank]
    constructor
    · intro hx
      obtain ⟨b, hb, stageB, subset⟩ := (N.square.stage_iff N.laws ha x).mp hx
      obtain ⟨o, ranked⟩ := before b hb stageB
      have length : N.mem (N.succ o) lengths := (members _).mpr ⟨b, hb, stageB, o, ranked, rfl⟩
      exact ⟨o, b, (N.mem_union _ _).mpr ⟨N.succ o, length, (N.mem_succ _ _).mpr (Or.inr rfl)⟩,
        ranked, (N.square.subset_iff N.laws x b).mp subset⟩
    · rintro ⟨o, earlier, found, oRank, subset⟩
      obtain ⟨l, hl, contains⟩ := (N.mem_union lengths o).mp found
      obtain ⟨b, hb, bs, heightB, rankB, rfl⟩ := (members l).mp hl
      have sub : N.Subset o heightB := (N.ordinal_subset_iff oRank.1 rankB.1).mpr
        ((N.mem_succ heightB o).mp contains)
      exact subsets_in_later_stage N.laws ha bs hb (N.subset_trans subset (N.rank_subset oRank rankB sub))
  exact ⟨height, same.symm ▸ rank⟩

/-- A least-cardinality counterexample would have only ranked
predecessors, and therefore would itself be a rank stage. -/
theorem stage_rank {a : V} (stage : N.square.Stage a) : ∃ height, N.Rank height a := by
  classical
  apply Classical.byContradiction
  intro absent
  obtain ⟨card, measures⟩ := N.cardinal_exists a
  let bound := N.succ card
  have rule := Definable.ex ((Definable.stage (N := N) (n := 3) (i := 0) (by decide)).and
    ((Definable.cardinal (N := N.toSetContext) (n := 3) (i := 0) (j := 1) (by decide) (by decide)).and
      (Definable.unranked (N := N) (n := 3) (i := 0) (by decide))))
  obtain ⟨bad, spec⟩ := N.separate [] rule bound a
  have hit : N.NonemptySet bad := ⟨card, (spec card).mpr ⟨(N.mem_succ _ _).mpr (Or.inr rfl),
    a, stage, measures, absent⟩⟩
  have sub : N.Subset bad bound := fun x hx => ((spec x).mp hx).1
  have hOrd := N.ordinal_succ measures.ordinal
  obtain ⟨first, hFirst, minimum⟩ := hOrd.ordered.least bad sub hit
  obtain ⟨bounded, b, stageB, bCard, notRank⟩ := (spec first).mp hFirst
  apply notRank
  apply N.stage_rank_of_predecessors stageB
  intro predecessor hPred stagePred
  apply Classical.byContradiction
  intro absentPred
  obtain ⟨o, hCard⟩ := N.cardinal_exists predecessor
  have less := N.stage_cardinal_increase stageB stagePred hPred bCard hCard
  have below : N.mem o bound := hOrd.transitive first bounded o less
  have wrong := (spec o).mpr ⟨below, predecessor, stagePred, hCard, absentPred⟩
  rcases minimum o wrong with same | greater
  · exact hOrd.ordered.irrefl first bounded (same.symm ▸ less)
  · exact WellOrderOn.asymm N.toSetContext hOrd.ordered below bounded less greater

theorem every_set_in_rank (x : V) : ∃ height stage, N.Rank height stage ∧ N.mem x stage := by
  obtain ⟨a, stage, sub⟩ := N.square.stage_choice N.laws x
  obtain ⟨h, rank⟩ := N.stage_rank stage
  obtain ⟨b, next⟩ := N.rank_exists (N.ordinal_succ rank.1)
  exact ⟨N.succ h, b, next, (N.mem_rank_iff next x).mpr ⟨h, a,
    (N.mem_succ _ _).mpr (Or.inr rfl), rank, (N.square.subset_iff N.laws x a).mp sub⟩⟩

theorem active_rank {x : V} (hx : N.square.activePoint x) :
    ∃ h s, N.Rank h s ∧ N.square.activePoint s ∧ N.mem x s := by
  obtain ⟨a, ha, stage, active⟩ := (active_iff N.laws x).mp hx
  obtain ⟨h, ranked⟩ := N.stage_rank stage
  exact ⟨h, a, ranked, active, ha⟩

theorem active_closure : N.square.LocalClosure where
  transitive := fun h => active_transitive N.laws h.2 h.1
  pairs {x y} xActive yActive := by
    obtain ⟨a, stageA, ha, activeA, hx⟩ := N.active_rank xActive
    obtain ⟨b, stageB, hb, activeB, hy⟩ := N.active_rank yActive
    have shared : ∃ s, N.square.activePoint s ∧ N.mem x s ∧ N.mem y s := by
      rcases N.ordinal_compare ha.1 hb.1 with lt | eq | gt
      · exact ⟨stageB, activeB, N.rank_subset ha hb (hb.1.transitive a lt) _ hx, hy⟩
      · have same := N.rank_unique (eq ▸ ha) hb
        exact ⟨stageB, activeB, same ▸ hx, hy⟩
      · exact ⟨stageA, activeA, hx, N.rank_subset hb ha (ha.1.transitive b gt) _ hy⟩
    obtain ⟨s, hs, xIn, yIn⟩ := shared
    obtain ⟨p, hp⟩ := N.exists_pair _ _
    exact ⟨p, active_subset N.laws hs (fun z hz => ((hp z).mp hz).elim
      (fun same => same.symm ▸ xIn) (fun same => same.symm ▸ yIn)), hp⟩

end NamedModel
end PalomarI3380.SquareRepresentation
