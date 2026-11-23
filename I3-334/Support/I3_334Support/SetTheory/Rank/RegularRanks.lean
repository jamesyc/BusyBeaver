module
public import I3_334Support.SetTheory.Recursion.OmegaSets
public import I3_334Support.Logic.RankSemantics
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Logic
variable {A V : Type} {M : Algebra A}

namespace SetContext

variable (N : SetContext M V)

def Regular : Prop :=
  ∀ a, N.NonemptySet a → ∃ x, N.mem x a ∧ ∀ y, N.mem y x → ¬N.mem y a

theorem ordinal_of_transitives (foundation : N.Regular) {a : V} (trans : N.Transitive a)
    (members : ∀ x, N.mem x a → N.Transitive x) : N.Ordinal a := by
  classical
  let bound := N.succ a
  obtain ⟨bad, spec⟩ := N.separate []
    (Definable.not (Definable.ordinal (N := N) (n := 2) (i := 0) (by decide))) bound a
  have none : ¬N.NonemptySet bad := by
    intro h
    obtain ⟨x, hx, min⟩ := foundation bad h
    obtain ⟨hxB, absent⟩ := (spec x).mp hx
    apply absent
    have transX : N.Transitive x := ((N.mem_succ a x).mp hxB).elim (members x)
      (fun eq => eq.symm ▸ trans)
    apply N.ordinal_of_transitive_members transX
    intro y hy
    apply Classical.byContradiction
    intro no
    have yB := N.trans_succ trans x hxB y hy
    exact min y hy ((spec y).mpr ⟨yB, no⟩)
  exact Classical.byContradiction fun absent => none ⟨a,
    (spec a).mpr ⟨(N.mem_succ a a).mpr (Or.inr rfl), absent⟩⟩

theorem rank_from_internal (foundation : N.Regular) {height stage : V}
    (h : Internal.RankLike N.mem height stage) : N.Rank height stage := by
  obtain ⟨⟨transitive,members⟩,domain,graph,successor,hierarchy,atHeight⟩ := h
  have domain_eq := (N.internal_succ height domain).mp successor
  subst domain
  exact ⟨N.ordinal_of_transitives foundation transitive members,graph,
    ⟨hierarchy.1,fun _ _ edge => hierarchy.2 _ (SetRecursion.at_domain hierarchy.1 edge) _ edge⟩,
    atHeight⟩

def ClosureStep (root : V) (_ : V) (graph result : V) : Prop :=
  ∀ x, N.mem x result ↔ x = root ∨
    (∃ i set, Internal.At N.mem graph i set ∧ N.mem x set) ∨
    (∃ i set y, Internal.At N.mem graph i set ∧ N.mem y set ∧ N.mem x y)

theorem closureStep_def : Definable.Relation4 N (N.ClosureStep) := by
  intro n r _ g s hr _ hg hs
  have out := Definable.mem (N := N) (n := n + 1) (i := 0) (j := s + 1) (by omega) (by omega)
  have root := Definable.eq (S := N.square) (n := n + 1) (i := 0) (j := r + 1) (by omega) (by omega)
  have previous := Definable.graphValue (N := N) (n := n + 3) (i := g + 3) (j := 1) (k := 0)
    (by omega) (by omega) (by omega)
  have members := Definable.mem (N := N) (n := n + 3) (i := 2) (j := 0) (by omega) (by omega)
  have earlier := Definable.graphValue (N := N) (n := n + 4) (i := g + 4) (j := 2) (k := 1)
    (by omega) (by omega) (by omega)
  have parent := Definable.mem (N := N) (n := n + 4) (i := 0) (j := 1) (by omega) (by omega)
  have child := Definable.mem (N := N) (n := n + 4) (i := 3) (j := 0) (by omega) (by omega)
  exact Definable.all (out.iff (root.or
    ((Definable.ex (Definable.ex (previous.and members))).or
      (Definable.ex (Definable.ex (Definable.ex (earlier.and (parent.and child))))))))

theorem closureStep_exists (root i graph : V) : ∃ value, N.ClosureStep root i graph value := by
  let prior := N.union (N.range graph)
  have before (x : V) : N.mem x prior ↔ ∃ j set, Internal.At N.mem graph j set ∧ N.mem x set := by
    rw [N.mem_union]
    constructor
    · rintro ⟨y, hy, member⟩
      obtain ⟨j, value⟩ := (N.mem_range _ _).mp hy
      exact ⟨j,y,value,member⟩
    · rintro ⟨j,y,value,member⟩
      exact ⟨y,(N.mem_range _ _).mpr ⟨j,value⟩,member⟩
  refine ⟨N.union₂ (N.singleton root) (N.union₂ prior (N.union prior)), fun x => ?_⟩
  rw [N.mem_union₂, N.mem_singleton, N.mem_union₂, before x, N.mem_union]
  apply or_congr Iff.rfl
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨y, ys, xy⟩
    obtain ⟨j,s,edge,inside⟩ := (before y).mp ys
    exact ⟨j,s,y,edge,inside,xy⟩
  · rintro ⟨j,s,y,edge,inside,xy⟩
    exact ⟨y,(before y).mpr ⟨j,s,edge,inside⟩,xy⟩

theorem closureStep_unique (root i graph x y : V)
    (hx : N.ClosureStep root i graph x) (hy : N.ClosureStep root i graph y) : x = y :=
  N.ext x y fun z => (hx z).trans (hy z).symm

theorem transitive_cover {w : V} (omega : Internal.Omega N.mem w) (root : V) :
    ∃ cover, N.Transitive cover ∧ N.mem root cover := by
  let recursion : SetRecursion N :=
    ⟨w,w,root,fun _ => N.mem,Definable.membership_relation,(N.omega_ordinal omega).ordered,
      N.ClosureStep,N.closureStep_def,N.closureStep_exists root,N.closureStep_unique root⟩
  obtain ⟨graph, h⟩ := recursion.solution_exists
  let cover := N.union (N.range graph)
  refine ⟨cover,?_,?_⟩
  · intro x hx y hy
    obtain ⟨later, inRange, member⟩ := (N.mem_union _ _).mp hx
    obtain ⟨n, atStage⟩ := (N.mem_range _ _).mp inRange
    have inW := SetRecursion.at_domain h.functionOn atStage
    have next := N.omega_succ omega inW
    obtain ⟨cut, f, value, desc, restricted, computed, rule⟩ := h.agrees (N.succ n) next
    have nIn : N.mem n cut := (desc n).mpr ⟨inW,(N.mem_succ _ _).mpr (Or.inr rfl)⟩
    have reference := (N.restricts_value restricted).mpr ⟨nIn,atStage⟩
    have included : N.mem y value := (rule y).mpr (Or.inr (Or.inr ⟨n,later,x,reference,member,hy⟩))
    exact (N.mem_union _ _).mpr ⟨value,(N.mem_range _ _).mpr ⟨N.succ n,computed⟩,included⟩
  · obtain ⟨_,_,value,_,_,atZero,step⟩ := h.agrees N.empty (N.omega_zero omega)
    exact (N.mem_union _ _).mpr ⟨value,(N.mem_range _ _).mpr ⟨N.empty,atZero⟩,
      (step root).mpr (Or.inl rfl)⟩

def RankMember (a height : V) : Prop :=
  ∃ stage, N.Rank height stage ∧ N.mem a stage

def LeastRankMember (a height : V) : Prop :=
  N.RankMember a height ∧ ∀ smaller, N.mem smaller height → ¬N.RankMember a smaller

theorem rankMember_def {n i j : Nat} (hi : i < n) (hj : j < n) :
    N.square.Definable n (fun env => N.RankMember (env i) (env j)) :=
  Definable.ex ((Definable.rank (N := N) (n := n + 1) (i := j + 1) (j := 0)
    (by omega) (by omega)).and (Definable.mem (i := i + 1) (j := 0) (by omega) (by omega)))

theorem leastRankMember_def {n i j : Nat} (hi : i < n) (hj : j < n) :
    N.square.Definable n (fun env => N.LeastRankMember (env i) (env j)) :=
  (N.rankMember_def hi hj).and (Definable.boundedAll hj _
    (N.rankMember_def (n := n + 1) (i := i + 1) (j := 0) (by omega) (by omega)).not)

theorem least_rank {a height : V} (h : N.RankMember a height) : ∃ b, N.LeastRankMember a b := by
  obtain ⟨stage, hs, member⟩ := h
  let bound := N.succ height
  have ord := N.ordinal_succ hs.1
  obtain ⟨candidates, spec⟩ := N.separate []
    (N.rankMember_def (n := 2) (i := 1) (j := 0) (by decide) (by decide)) bound a
  have existsCandidate : N.NonemptySet candidates :=
    ⟨height,(spec height).mpr ⟨(N.mem_succ _ _).mpr (Or.inr rfl),stage,hs,member⟩⟩
  have subset : N.Subset candidates bound := fun x hx => ((spec x).mp hx).1
  obtain ⟨least, hl, minimum⟩ := ord.ordered.least candidates subset existsCandidate
  obtain ⟨leastIn, leastRank⟩ := (spec least).mp hl
  refine ⟨least,leastRank,fun z hz ex => ?_⟩
  have inBound : N.mem z bound := ord.transitive least leastIn z hz
  rcases minimum z ((spec z).mpr ⟨inBound,ex⟩) with same | after
  · exact ord.ordered.irrefl least leastIn (same.symm ▸ hz)
  · exact WellOrderOn.asymm N ord.ordered inBound leastIn hz after

theorem least_rank_unique {a x y : V} (hx : N.LeastRankMember a x) (hy : N.LeastRankMember a y) : x = y := by
  obtain ⟨_, first, _⟩ := hx.1
  obtain ⟨_, next, _⟩ := hy.1
  rcases N.ordinal_compare first.1 next.1 with before | same | after
  · exact (hy.2 x before hx.1).elim
  · exact same
  · exact (hx.2 y after hy.1).elim

/-- Foundation ranks every set by examining a least unranked member of a
transitive cover, with Replacement collecting the already-ranked members. -/
theorem rank_cover {w : V} (omega : Internal.Omega N.mem w) (foundation : N.Regular) (x : V) :
    ∃ height, N.RankMember x height := by
  classical
  apply Classical.byContradiction
  intro absent
  obtain ⟨cover, trans, included⟩ := N.transitive_cover omega x
  have defn := Definable.not (Definable.ex (N.rankMember_def (n := 3) (i := 1) (j := 0) (by decide) (by decide)))
  obtain ⟨bad, spec⟩ := N.separate [] defn cover cover
  obtain ⟨z, hz, minimal⟩ := foundation bad ⟨x, (spec x).mpr ⟨included, absent⟩⟩
  obtain ⟨zHere, unranked⟩ := (spec z).mp hz
  have each (a : V) (ha : N.mem a z) : ∃ height, N.LeastRankMember a height := by
    apply Classical.byContradiction
    intro lack
    have unrankedA : ¬∃ h, N.RankMember a h := by
      rintro ⟨b,h⟩
      exact lack (N.least_rank h)
    exact minimal a ha ((spec a).mpr ⟨trans z zHere a ha,unrankedA⟩)
  have rankDef := N.leastRankMember_def (n := 2) (i := 0) (j := 1) (by decide) (by decide)
  obtain ⟨levels, members⟩ := N.image [] rankDef (fun _ _ _ => N.least_rank_unique) z
  let supremum := N.union levels
  have ho : N.Ordinal supremum := by
    apply N.ordinal_union
    intro b hb
    obtain ⟨a,_,⟨stage, ranked, _⟩,_⟩ := (members b).mp hb
    exact ranked.1
  obtain ⟨rankAtSup, hs⟩ := N.rank_exists ho
  have contained : N.Subset z rankAtSup := by
    intro a ha
    obtain ⟨b, least⟩ := each a ha
    obtain ⟨s,ranked,member⟩ := least.1
    have level := (members b).mpr ⟨a,ha,least⟩
    have sub : N.Subset b supremum := fun v hv => (N.mem_union _ _).mpr ⟨b,level,hv⟩
    exact N.rank_subset ranked hs sub a member
  obtain ⟨next,ranked⟩ := N.rank_exists (N.ordinal_succ ho)
  exact unranked ⟨N.succ supremum, next, ranked,
    (N.mem_rank_iff ranked z).mpr ⟨supremum,rankAtSup,(N.mem_succ _ _).mpr (Or.inr rfl),hs,contained⟩⟩

end SetContext
end PalomarI3380.SquareRepresentation
