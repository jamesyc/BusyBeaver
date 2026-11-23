module
public import I3_334Support.SetTheory.Graphs.BinaryGraphs
public import I3_334Support.SetTheory.Rank.RankCollection
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic
variable {A V : Type} {M : Algebra A} (N : SetContext M V)

def Triple (x y z code : V) : Prop :=
  ∃ yz, Internal.OrderedPair N.mem y z yz ∧ Internal.OrderedPair N.mem x yz code

noncomputable def triple (x y z : V) : V :=
  N.orderedPair x (N.orderedPair y z)

theorem triple_intro (a b c : V) : N.Triple a b c (N.triple a b c) :=
  ⟨_,N.orderedPair_intro _ _,N.orderedPair_intro _ _⟩

theorem triple_inj {a b c x y z p : V} (first : N.Triple a b c p) (second : N.Triple x y z p) :
    a = x ∧ b = y ∧ c = z := by
  obtain ⟨l,hl,ac⟩ := first
  obtain ⟨r,hr,bc⟩ := second
  obtain ⟨same,eq⟩ := Internal.orderedPair_injective ac bc
  subst r
  exact ⟨same,Internal.orderedPair_injective hl hr⟩

theorem triple_def {n a b c p : Nat}
    (ha : a < n) (hb : b < n) (hc : c < n) (hp : p < n) :
    N.square.Definable n (fun env => N.Triple (env a) (env b) (env c) (env p)) := by
  have right := Definable.orderedPair (N := N) (n := n+1) (i := b+1) (j := c+1) (k := 0)
    (by omega) (by omega) (by omega)
  have left := Definable.orderedPair (N := N) (n := n+1) (i := a+1) (j := 0) (k := p+1)
    (by omega) (by omega) (by omega)
  exact Definable.ex (right.and left)

def IsUnion (family contents : V) : Prop :=
  ∀ x, N.mem x contents ↔ ∃ y, N.mem y family ∧ N.mem x y

theorem isUnion_unique {family a b : V} (ha : N.IsUnion family a) (hb : N.IsUnion family b) : a = b :=
  N.ext a b fun x => (ha x).trans (hb x).symm

theorem union_def {n f u : Nat} (hf : f < n) (hu : u < n) :
    N.square.Definable n (fun env => N.IsUnion (env f) (env u)) := by
  have left := Definable.mem (N := N) (n := n+1) (i := 0) (j := u+1) (by omega) (by omega)
  have right := Definable.boundedEx (S := N.square) (n := n+1) (i := f+1) (by omega) _
    (Definable.mem (N := N) (n := n+2) (i := 1) (j := 0) (by omega) (by omega))
  exact Definable.all (left.iff right)

def SupRank (heights stage : V) : Prop :=
  ∃ range height, N.IsRange heights range ∧ N.IsUnion range height ∧ N.Rank height stage

theorem supRank_unique {f a b : V} (ha : N.SupRank f a) (hb : N.SupRank f b) : a = b := by
  obtain ⟨ra,m,ha,ua,rank⟩ := ha
  obtain ⟨rb,n,hb,ub,rank'⟩ := hb
  have same := N.range_unique ha hb
  subst rb
  have eq := N.isUnion_unique ua ub
  subst n
  exact N.rank_unique rank rank'

theorem supRank_def {n f s : Nat} (hf : f < n) (hs : s < n) :
    N.square.Definable n (fun env => N.SupRank (env f) (env s)) := by
  have range := Definable.range (N := N) (n := n+2) (i := f+2) (j := 1) (by omega) (by omega)
  have union := N.union_def (n := n+2) (f := 1) (u := 0) (by omega) (by omega)
  have rank := Definable.rank (N := N) (n := n+2) (i := 0) (j := s+2) (by omega) (by omega)
  exact Definable.ex (Definable.ex (range.and (union.and rank)))

def RelationBetween (graph a b : V) : Prop :=
  ∀ p, N.mem p graph → ∃ x y, N.mem x a ∧ N.mem y b ∧ Internal.OrderedPair N.mem x y p

theorem relationBetween_def {n f a b : Nat} (hf : f < n) (ha : a < n) (hb : b < n) :
    N.square.Definable n (fun env => N.RelationBetween (env f) (env a) (env b)) := by
  have left := Definable.mem (N := N) (n := n+3) (i := 1) (j := a+3) (by omega) (by omega)
  have right := Definable.mem (N := N) (n := n+3) (i := 0) (j := b+3) (by omega) (by omega)
  have pair := Definable.orderedPair (N := N) (n := n+3) (i := 1) (j := 0) (k := 2)
    (by omega) (by omega) (by omega)
  exact Definable.boundedAll hf _ (Definable.ex (Definable.ex (left.and (right.and pair))))

theorem relationBetween_bound {f a b : V} (h : N.RelationBetween f a b) :
    N.mem f (N.power (N.PairBound a b)) := by
  apply (N.mem_power _ _).mpr
  intro p hp
  obtain ⟨x,y,hx,hy,code⟩ := h p hp
  exact ((N.orderedPair_iff x y p).mp code).symm ▸ N.in_pairBound hx hy

end PalomarI3380.SquareRepresentation.SetContext
