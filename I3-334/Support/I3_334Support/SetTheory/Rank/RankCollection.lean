module
public import I3_334Support.SetTheory.Rank.RegularRanks
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic
variable {A V : Type} {M : Algebra A} (N : SetContext M V)

theorem least_definable_ordinal (params : List V) (anchor : V) {P : (Nat → V) → Prop}
    (defn : N.square.Definable (params.length + 2) P)
    (known : ∃ a, N.Ordinal a ∧ P (parameterEnv params a anchor)) :
    ∃ a, N.Ordinal a ∧ P (parameterEnv params a anchor) ∧
      ∀ b, N.mem b a → ¬P (parameterEnv params b anchor) := by
  obtain ⟨bound,ordinal,good⟩ := known
  let domain := N.succ bound
  have boundOrd := N.ordinal_succ ordinal
  obtain ⟨candidates,spec⟩ := N.separate params defn domain anchor
  have nonempty : N.NonemptySet candidates :=
    ⟨bound,(spec bound).mpr ⟨(N.mem_succ _ _).mpr (Or.inr rfl),good⟩⟩
  have sub : N.Subset candidates domain := fun x hx => ((spec x).mp hx).1
  obtain ⟨a,where_,minimal⟩ := boundOrd.ordered.least candidates sub nonempty
  obtain ⟨ha,hP⟩ := (spec a).mp where_
  refine ⟨a,boundOrd.of_mem N ha,hP,fun b below hB => ?_⟩
  have hb := boundOrd.transitive a ha b below
  have inCandidates := (spec b).mpr ⟨hb,hB⟩
  rcases minimal b inCandidates with same | reverse
  · exact boundOrd.ordered.irrefl a ha (same.symm ▸ below)
  · exact WellOrderOn.asymm N boundOrd.ordered hb ha below reverse

def WitnessInRank (R : V → V → V → Prop) (key x height : V) : Prop :=
  ∃ y, R key x y ∧ N.RankMember y height

theorem witnessRank_def {R : V → V → V → Prop} (defn : Definable.Relation3 N R)
    {n k x a : Nat} (hk : k < n) (hx : x < n) (ha : a < n) :
    N.square.Definable n (fun s => N.WitnessInRank R (s k) (s x) (s a)) :=
  Definable.ex ((defn (n := n+1) (i := k+1) (j := x+1) (k := 0) (by omega) (by omega) (by omega)).and
    (N.rankMember_def (n := n+1) (i := 0) (j := a+1) (by omega) (by omega)))

def LeastWitnessRank (R : V → V → V → Prop) (key x height : V) : Prop :=
  N.WitnessInRank R key x height ∧ ∀ a, N.mem a height → ¬N.WitnessInRank R key x a

theorem leastWitnessRank_def {R : V → V → V → Prop} (defn : Definable.Relation3 N R)
    {n k x a : Nat} (hk : k < n) (hx : x < n) (ha : a < n) :
    N.square.Definable n (fun s => N.LeastWitnessRank R (s k) (s x) (s a)) :=
  (N.witnessRank_def defn hk hx ha).and (Definable.boundedAll ha _
    (N.witnessRank_def defn (n := n+1) (k := k+1) (x := x+1) (a := 0)
      (by omega) (by omega) (by omega)).not)

theorem witnessRank_unique {R : V → V → V → Prop} {k x a b : V}
    (ha : N.LeastWitnessRank R k x a) (hb : N.LeastWitnessRank R k x b) : a = b := by
  have ordinal {h : V} (witness : N.WitnessInRank R k x h) : N.Ordinal h := by
    obtain ⟨_,_,_,hr,_⟩ := witness
    exact hr.1
  rcases N.ordinal_compare (ordinal ha.1) (ordinal hb.1) with less | same | more
  · exact (hb.2 a less ha.1).elim
  · exact same
  · exact (ha.2 b more hb.1).elim

/-- Set-sized Collection for a definable class relation. Pick least
witness ranks by Replacement, then take their supremum. -/
theorem collect_in_rank {w : V} (omega : Internal.Omega N.mem w) (foundation : N.Regular)
    {R : V → V → V → Prop} (defn : Definable.Relation3 N R) (key domain : V) :
    ∃ height stage, N.Rank height stage ∧
      ∀ x, N.mem x domain → (∃ y, R key x y) → ∃ y, N.mem y stage ∧ R key x y := by
  have least (x : V) (inhabited : ∃ y, R key x y) : ∃ h, N.LeastWitnessRank R key x h := by
    obtain ⟨y, relation⟩ := inhabited
    obtain ⟨h, stage, rank, here⟩ := N.rank_cover omega foundation y
    have described := N.witnessRank_def defn (n := 3) (k := 2) (x := 1) (a := 0)
      (by decide) (by decide) (by decide)
    obtain ⟨a,_,found,minimal⟩ := N.least_definable_ordinal [key] x described
      ⟨h,rank.1,⟨y,relation,stage,rank,here⟩⟩
    exact ⟨a,found,minimal⟩
  have described := N.leastWitnessRank_def defn (n := 3) (k := 2) (x := 0) (a := 1)
    (by decide) (by decide) (by decide)
  obtain ⟨heights,contents⟩ := N.image [key] described
    (fun _ _ _ => N.witnessRank_unique) domain
  let height := N.union heights
  have ord : N.Ordinal height := N.ordinal_union heights fun a ha => by
    obtain ⟨x,_,⟨y,_,t,rank,hIn⟩,_⟩ := (contents a).mp ha
    exact rank.1
  obtain ⟨stage,rank⟩ := N.rank_exists ord
  refine ⟨height,stage,rank,fun x hx existsY => ?_⟩
  obtain ⟨a,first⟩ := least x existsY
  obtain ⟨y,hy,t,ranked,belongs⟩ := first.1
  have aHit : N.mem a heights := (contents a).mpr ⟨x,hx,first⟩
  have subset : N.Subset a height := fun i hi => (N.mem_union _ _).mpr ⟨a,aHit,hi⟩
  exact ⟨y,N.rank_subset ranked rank subset y belongs,hy⟩

end PalomarI3380.SquareRepresentation.SetContext
