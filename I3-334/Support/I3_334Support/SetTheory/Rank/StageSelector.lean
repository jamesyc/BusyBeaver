module
public import I3_334Support.SetTheory.Rank.RankCollection
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic
variable {A V : Type} {M : Algebra A} (N : SetContext M V)

def CoverHeight (x height : V) : Prop :=
  ∃ stage, N.Rank height stage ∧ N.Subset x stage

def StageChoice (x stage : V) : Prop :=
  ∃ height, N.Rank height stage ∧ N.Subset x stage ∧
    ∀ lower, N.mem lower height → ¬N.CoverHeight x lower

theorem coverHeight_def {n x a : Nat} (hx : x < n) (ha : a < n) :
    N.square.Definable n (fun env => N.CoverHeight (env x) (env a)) :=
  Definable.ex ((Definable.rank (N := N) (n := n+1) (i := a+1) (j := 0) (by omega) (by omega)).and
    (Definable.subset (N := N) (n := n+1) (i := x+1) (j := 0) (by omega) (by omega)))

theorem stageChoice_def {n x s : Nat} (hx : x < n) (hs : s < n) :
    N.square.Definable n (fun env => N.StageChoice (env x) (env s)) := by
  have atStage := Definable.rank (N := N) (n := n+1) (i := 0) (j := s+1) (by omega) (by omega)
  have inside := Definable.subset (N := N) (n := n+1) (i := x+1) (j := s+1) (by omega) (by omega)
  have lower := N.coverHeight_def (n := n+2) (x := x+2) (a := 0) (by omega) (by omega)
  exact Definable.ex (atStage.and (inside.and (Definable.boundedAll (i := 0) (by omega) _ lower.not)))

theorem stageChoice_exists {w : V} (omega : Internal.Omega N.mem w) (foundation : N.Regular)
    (x : V) : ∃ stage, N.StageChoice x stage := by
  obtain ⟨a,s,hr,hx⟩ := N.rank_cover omega foundation x
  obtain ⟨height,_,⟨stage,rank,contained⟩,below⟩ := N.least_definable_ordinal [] x
    (N.coverHeight_def (n := 2) (x := 1) (a := 0) (by decide) (by decide))
    ⟨a,hr.1,s,hr,fun y hy => N.rank_transitive hr x hx y hy⟩
  exact ⟨stage,height,rank,contained,below⟩

theorem stageChoice_unique {x a b : V} (first : N.StageChoice x a) (second : N.StageChoice x b) : a = b := by
  obtain ⟨i,ha,subA,leastA⟩ := first
  obtain ⟨j,hb,subB,leastB⟩ := second
  rcases N.ordinal_compare ha.1 hb.1 with lower | same | upper
  · exact (leastB i lower ⟨a,ha,subA⟩).elim
  · exact N.rank_unique ha (same.symm ▸ hb)
  · exact (leastA j upper ⟨b,hb,subB⟩).elim

theorem stageChoice_of_rank {a stage : V} (rank : N.Rank a stage) : N.StageChoice stage stage := by
  refine ⟨a,rank,N.subset_refl _,fun lower below ⟨earlier,atEarlier,sub⟩ => ?_⟩
  exact N.rank_no_self atEarlier (sub earlier (N.rank_member atEarlier rank below))

theorem stageChoice_range {s : V} : (∃ x, N.StageChoice x s) ↔ ∃ a, N.Rank a s :=
  ⟨fun ⟨_,a,rank,_⟩ => ⟨a,rank⟩, fun ⟨_,rank⟩ => ⟨s,N.stageChoice_of_rank rank⟩⟩

theorem rank_member_iff {a b u v : V} (first : N.Rank a u) (second : N.Rank b v) :
    N.mem u v ↔ N.mem a b := by
  refine ⟨fun h => ?_,N.rank_member first second⟩
  rcases N.ordinal_compare first.1 second.1 with left | same | right
  · exact left
  · have eq := N.rank_unique (same ▸ first) second
    exact (N.rank_no_self second (eq ▸ h)).elim
  · exact (N.rank_no_self first (N.rank_transitive first v (N.rank_member second first right) u h)).elim

theorem rank_limit_cover {a s : V} (rank : N.Rank a s) (limit : Internal.Inductive N.mem a) :
    ∀ x, N.mem x s ↔ ∃ t, N.mem x t ∧ N.mem t s ∧ ∃ b, N.Rank b t := by
  intro x
  constructor
  · intro hx
    obtain ⟨b,t,below,atRank,sub⟩ := (N.mem_rank_iff rank x).mp hx
    obtain ⟨next,spec,inside⟩ := limit.2 b below
    have equal := (N.internal_succ b next).mp spec
    subst next
    obtain ⟨u,hu⟩ := N.rank_exists (N.ordinal_succ atRank.1)
    exact ⟨u,(N.mem_rank_iff hu x).mpr ⟨b,t,(N.mem_succ _ _).mpr (Or.inr rfl),atRank,sub⟩,
      N.rank_member hu rank inside,_,hu⟩
  · rintro ⟨t,xt,ts,_⟩
    exact N.rank_transitive rank t ts x xt

end PalomarI3380.SquareRepresentation.SetContext
