module
public import I3_334Support.SetTheory.Classes.ActiveRanks
@[expose] public section

namespace PalomarI3380.SquareRepresentation.NamedModel

open Logic SetContext

variable {A V : Type} {M : Algebra A} (N : NamedModel M V)

def Moved (x : V) : Prop :=
  ∃ y, N.square.rel (M.constant .J) x y ∧ x ≠ y

theorem moved_iff (x : N.Active) : N.Moved x.val ↔ N.embedding x ≠ x := by
  constructor
  · rintro ⟨y, edge, different⟩ same
    have jxx := (N.fixed_iff_self_edge x).mp same
    exact different (j_single_valued N.laws N.active_closure jxx edge)
  · intro h
    exact ⟨(N.embedding x).val, N.embedding_edge x, fun eq => h (Subtype.ext eq.symm)⟩

private theorem moved_def {n i : Nat} (hi : i < n) :
    N.square.Definable n (fun s => N.Moved (s i)) := by
  have edge := Definable.atom (S := N.square) (n := n + 1) (M.constant .J)
    (i := i + 1) (j := 0) (by omega) (by omega)
  have different := Definable.not (Definable.eq (S := N.square) (n := n + 1)
    (i := i + 1) (j := 0) (by omega) (by omega))
  exact Definable.ex (edge.and different)

structure Critical (N : NamedModel M V) (point stage : N.Active) : Prop where
  rank : N.Rank point.val stage.val
  fixedBelow : ∀ x, N.localMem x stage → N.embedding x = x
  movesUp : N.localMem point (N.embedding point)

/-- Choose a bounded least rank containing a moved point. A predecessor
stage bounds that point as a subset and is fixed pointwise. -/
theorem critical_exists : ∃ point stage : N.Active, N.Critical point stage := by
  classical
  obtain ⟨x, y, edge, moved⟩ := N.movement
  have active := (j_active N.laws N.active_closure edge).1
  obtain ⟨a, v, ranked, activeV, contains⟩ := N.active_rank active
  let bound := N.succ a
  have boundOrd := N.ordinal_succ ranked.1
  have defi := Definable.ex ((Definable.rank (N := N.toSetContext) (n := 3) (i := 1) (j := 0)
    (by decide) (by decide)).and
      (Definable.boundedEx (S := N.square) (n := 3) (i := 0) (by decide) _
        (N.moved_def (n := 4) (i := 0) (by decide))))
  obtain ⟨candidates, spec⟩ := N.separate [] defi bound v
  have sub : N.Subset candidates bound := fun z hz => ((spec z).mp hz).1
  have inhabited : N.NonemptySet candidates :=
    ⟨a, (spec a).mpr ⟨(N.mem_succ _ _).mpr (Or.inr rfl), v, ranked, x, contains, y, edge, moved⟩⟩
  obtain ⟨least, hit, minimal⟩ := boundOrd.ordered.least candidates sub inhabited
  obtain ⟨boundHit, found, leastRank, z, belongs, movesZ⟩ := (spec least).mp hit
  obtain ⟨b, before, previous, beforeRank, subZ⟩ := (N.mem_rank_iff leastRank z).mp belongs
  have beforeBound := boundOrd.transitive least boundHit b previous
  have earlierFixed (w : V) (hw : N.mem w before) : ¬ N.Moved w := by
    intro changes
    have bad := (spec b).mpr ⟨beforeBound, before, beforeRank, w, hw, changes⟩
    rcases minimal b bad with same | after
    · exact boundOrd.ordered.irrefl least boundHit (same.symm ▸ previous)
    · exact WellOrderOn.asymm N.toSetContext boundOrd.ordered beforeBound boundHit previous after
  have activeA := active_subset N.laws activeV (N.rank_contains_ordinal ranked)
  have activeB : N.square.activePoint b := by
    rcases (N.mem_succ a b).mp beforeBound with pre | same
    · exact active_transitive N.laws activeA pre
    · exact same.symm ▸ activeA
  let stage : N.Active := ⟨before, N.active_rank_value activeB beforeRank⟩
  let point : N.Active := ⟨b, activeB⟩
  have fixed (w : N.Active) (hw : N.localMem w stage) : N.embedding w = w :=
    Classical.byContradiction fun h => earlierFixed w.val hw ((N.moved_iff w).mpr h)
  have bOrd := (N.preserves_ordinal point).mp beforeRank.1
  have bigger : N.Subset b (N.embedding point).val := by
    intro w hw
    let p : N.Active := ⟨w, active_transitive N.laws activeB hw⟩
    have pFix := fixed p (N.rank_contains_ordinal beforeRank w hw)
    have edge := (N.preserves_membership p point).mp hw
    rw [pFix] at edge
    exact edge
  refine ⟨point, stage, beforeRank, fixed, ?_⟩
  rcases (N.ordinal_subset_iff beforeRank.1 bOrd).mp bigger with strict | equal
  · exact strict
  · have jPoint : N.embedding point = point := Subtype.ext equal.symm
    have h := (N.preserves_rank point stage).mp beforeRank
    rw [jPoint] at h
    have jStage : N.embedding stage = stage := Subtype.ext (N.rank_unique h beforeRank)
    have dZ := (j_active N.laws N.active_closure (movesZ.choose_spec.1)).1
    let p : N.Active := ⟨z, dZ⟩
    exact ((N.moved_iff p).mp movesZ (N.fixes_subsets stage jStage fixed p subZ)).elim

end PalomarI3380.SquareRepresentation.NamedModel
