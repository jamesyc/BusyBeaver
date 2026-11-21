module
public import I3_380.RankHierarchy
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Logic

variable {A V : Type} {M : Algebra A}

namespace Definable

variable {N : SetContext M V}

theorem rank {n i j : Nat} (hi : i < n) (hj : j < n) :
    N.square.Definable n (fun s => N.Rank (s i) (s j)) := by
  have hOrdinal := ordinal (N := N) hi
  have next := successor (N := N) (n := n + 2) (i := i + 2) (j := 0) (by omega) (by omega)
  have funOn := functionOn (N := N) (n := n + 2) (i := 1) (j := 0) (by omega) (by omega)
  have value := graphValue (N := N) (n := n + 2) (i := 1) (j := i + 2) (k := j + 2)
    (by omega) (by omega) (by omega)
  have stage := graphValue (N := N) (n := n + 4) (i := 3) (j := 1) (k := 0)
    (by omega) (by omega) (by omega)
  have member := mem (N := N) (n := n + 5) (i := 0) (j := 1) (by omega) (by omega)
  have previous := graphValue (N := N) (n := n + 7) (i := 6) (j := 1) (k := 0)
    (by omega) (by omega) (by omega)
  have inclusion := subset (N := N) (n := n + 7) (i := 2) (j := 0) (by omega) (by omega)
  have earlier := boundedEx (i := 2) (by omega) _ (ex (previous.and inclusion))
  have hierarchy := all (all (stage.implies (all (member.iff earlier))))
  refine (hOrdinal.and (ex (ex (next.and (funOn.and (value.and hierarchy)))))).congr fun env => ?_
  constructor
  · rintro ⟨ord, g, bound, successor, function, result, members⟩
    have eq : bound = N.succ (env i) := (N.internal_succ _ _).mp successor
    subst bound
    exact ⟨ord, g, ⟨function, members⟩, result⟩
  · rintro ⟨ord, g, hg, result⟩
    exact ⟨ord, g, N.succ (env i), N.mem_succ _, hg.functionOn, result, hg.members⟩

end Definable

namespace SetContext

variable (N : SetContext M V)

theorem hierarchy_restrict {a b f : V} (ha : N.Ordinal a) (hb : N.Ordinal b)
    (sub : N.Subset a b) (h : N.Hierarchy b f) :
    N.Hierarchy a (N.restrictGraph f (N.succ a)) := by
  have incl : N.Subset (N.succ a) (N.succ b) := by
    intro i hi
    rcases (N.mem_succ a i).mp hi with less | rfl
    · exact (N.mem_succ _ _).mpr (Or.inl (sub i less))
    · exact (N.mem_succ _ _).mpr ((N.ordinal_subset_iff ha hb).mp sub)
  have restriction := N.restricts_canonical f (N.succ a)
  refine ⟨N.restricts_function h.functionOn incl restriction, fun i stage edge x => ?_⟩
  obtain ⟨inside, atFull⟩ := (N.restricts_value restriction).mp edge
  refine (h.members i stage atFull x).trans ?_
  constructor
  · rintro ⟨j, before, stage, has, subs⟩
    exact ⟨j, before, stage, (N.restricts_value restriction).mpr
      ⟨(N.ordinal_succ ha).transitive i inside j before, has⟩, subs⟩
  · rintro ⟨j, before, stage, atRestr, subs⟩
    exact ⟨j, before, stage, ((N.restricts_value restriction).mp atRestr).2, subs⟩

theorem hierarchy_value_rank {a b f stage : V} (ha : N.Ordinal a) (hb : N.Ordinal b)
    (sub : N.Subset a b) (h : N.Hierarchy b f) (v : Internal.At N.mem f a stage) :
    N.Rank a stage :=
  ⟨ha, N.restrictGraph f (N.succ a), N.hierarchy_restrict ha hb sub h,
    (N.restricts_value (N.restricts_canonical _ _)).mpr ⟨(N.mem_succ _ _).mpr (Or.inr rfl), v⟩⟩

theorem mem_rank_iff {height stage : V} (h : N.Rank height stage) (x : V) :
    N.mem x stage ↔ ∃ a before, N.mem a height ∧ N.Rank a before ∧ N.Subset x before := by
  obtain ⟨ho, f, hf, value⟩ := h
  refine (hf.members _ _ value x).trans ?_
  constructor
  · rintro ⟨a, earlier, before, has, sub⟩
    exact ⟨a, before, earlier, N.hierarchy_value_rank (ho.of_mem N earlier) ho (ho.transitive a earlier) hf has, sub⟩
  · rintro ⟨a, before, earlier, rank, sub⟩
    obtain ⟨actual, atActual, _⟩ := hf.functionOn.1 a ((N.mem_succ _ _).mpr (Or.inl earlier))
    have same := N.rank_unique rank
      (N.hierarchy_value_rank (ho.of_mem N earlier) ho (ho.transitive a earlier) hf atActual)
    exact ⟨a, earlier, before, same.symm ▸ atActual, sub⟩

theorem rank_subset {a b u v : V} (hu : N.Rank a u) (hv : N.Rank b v) (sub : N.Subset a b) :
    N.Subset u v := by
  intro x hx
  obtain ⟨c, stage, earlier, hc, inside⟩ := (N.mem_rank_iff hu x).mp hx
  exact (N.mem_rank_iff hv x).mpr ⟨c, stage, sub c earlier, hc, inside⟩

theorem rank_member {a b u v : V} (hu : N.Rank a u) (hv : N.Rank b v) (earlier : N.mem a b) :
    N.mem u v :=
  (N.mem_rank_iff hv u).mpr ⟨a, u, earlier, hu, N.subset_refl _⟩

theorem rank_transitive {a u : V} (hu : N.Rank a u) : N.Transitive u := by
  intro x hx y hy
  obtain ⟨b, v, earlier, hv, sub⟩ := (N.mem_rank_iff hu x).mp hx
  exact N.rank_subset hv hu (hu.1.transitive b earlier) y (sub y hy)

theorem rank_no_self_members {a stage : V} (rank : N.Rank a stage) :
    ∀ x, N.mem x stage → ¬N.mem x x := by
  let bound := N.succ a
  have ord := N.ordinal_succ rank.1
  have pred := Definable.all ((Definable.rank (N := N) (n := 3) (i := 1) (j := 0)
    (by decide) (by decide)).implies (Definable.boundedAll (i := 0) (by decide) _
      (Definable.not (Definable.mem (N := N) (n := 4) (i := 0) (j := 0) (by decide) (by decide)))))
  have step := N.order_induction (a := bound) ord.ordered [] pred
  have proves := step (fun b hb ih v hv x hx self => by
    obtain ⟨c, u, earlier, hc, sub⟩ := (N.mem_rank_iff hv x).mp hx
    exact ih c (ord.transitive b hb c earlier) earlier u hc x (sub x self) self)
  exact proves a ((N.mem_succ _ _).mpr (Or.inr rfl)) stage rank

theorem rank_no_self {a stage : V} (h : N.Rank a stage) : ¬N.mem stage stage := by
  intro self
  exact N.rank_no_self_members h stage self self

theorem rank_height_unique {a b stage : V} (ha : N.Rank a stage) (hb : N.Rank b stage) : a = b := by
  rcases N.ordinal_compare ha.1 hb.1 with less | eq | greater
  · exact (N.rank_no_self ha (N.rank_member ha hb less)).elim
  · exact eq
  · exact (N.rank_no_self ha (N.rank_member hb ha greater)).elim

end SetContext
end PalomarI3380.SquareRepresentation
