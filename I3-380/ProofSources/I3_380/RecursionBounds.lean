module
public import I3_380.ModelTuples
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic
variable {A V : Type} {M : Algebra A} {N : SetContext M V}

/-- A set-length recursion whose update relation is total but need not
select a unique output. Its class of possible outputs has a fixed
first-order definition. -/
structure ClassUpdate (N : SetContext M V) where
  domain : V
  ordered : N.Ordinal domain
  key : V
  choices : V → V → V → V → Prop
  definable : Definable.Relation4 N choices
  total : ∀ i, N.mem i domain → ∀ prior, ∃ y, choices key i prior y

namespace ClassUpdate

variable (U : ClassUpdate N)

def CollectionWitness (params pair value : V) : Prop :=
  ∃ key domain bound i prior, N.Triple key domain bound params ∧
    Internal.OrderedPair N.mem i prior pair ∧ N.mem i domain ∧ N.mem prior bound ∧ U.choices key i prior value

theorem collectionWitness_def : Definable.Relation3 N U.CollectionWitness := by
  intro n p x y hp hx hy
  have packed := N.triple_def (n := n+5) (a := 4) (b := 3) (c := 2) (p := p+5)
    (by omega) (by omega) (by omega) (by omega)
  have pair := Definable.orderedPair (N := N) (n := n+5) (i := 1) (j := 0) (k := x+5)
    (by omega) (by omega) (by omega)
  have index := Definable.mem (N := N) (n := n+5) (i := 1) (j := 3) (by omega) (by omega)
  have graph := Definable.mem (N := N) (n := n+5) (i := 0) (j := 2) (by omega) (by omega)
  have value := U.definable (n := n+5) (i := 4) (j := 1) (k := 0) (l := y+5)
    (by omega) (by omega) (by omega) (by omega)
  have witness := packed.and (pair.and (index.and (graph.and value)))
  exact Definable.ex (Definable.ex (Definable.ex (Definable.ex (Definable.ex witness))))

def CoveredBy (key domain preceding height : V) : Prop :=
  ∃ output, N.Rank height output ∧
    ∀ i, N.mem i domain → ∀ previous, N.RelationBetween previous domain preceding →
      ∃ value, N.mem value output ∧ U.choices key i previous value

theorem coveredBy_def {n k d s a : Nat} (hk : k < n) (hd : d < n) (hs : s < n) (ha : a < n) :
    N.square.Definable n (fun env => U.CoveredBy (env k) (env d) (env s) (env a)) := by
  have rank := Definable.rank (N := N) (n := n+1) (i := a+1) (j := 0) (by omega) (by omega)
  have graph := N.relationBetween_def (n := n+3) (f := 0) (a := d+3) (b := s+3)
    (by omega) (by omega) (by omega)
  have value := U.definable (n := n+4) (i := k+4) (j := 2) (k := 1) (l := 0)
    (by omega) (by omega) (by omega) (by omega)
  have update := Definable.boundedAll (i := d+1) (by omega) _
    (Definable.all (graph.implies (Definable.boundedEx (i := 2) (by omega) _ value)))
  exact Definable.ex (rank.and update)

private theorem possible_bound {w : V} (omega : Internal.Omega N.mem w) (regular : N.Regular)
    (preceding : V) : ∃ a, U.CoveredBy U.key U.domain preceding a := by
  let input := N.power (N.PairBound U.domain preceding)
  let params := N.triple U.key U.domain input
  obtain ⟨height,stage,ranked,contains⟩ := N.collect_in_rank omega regular
    U.collectionWitness_def params (N.PairBound U.domain input)
  refine ⟨height,stage,ranked,fun i hi f shaped => ?_⟩
  have available : N.mem f input := N.relationBetween_bound shaped
  obtain ⟨v,choice⟩ := U.total i hi f
  have witness : U.CollectionWitness params (N.orderedPair i f) v :=
    ⟨U.key,U.domain,input,i,f,N.triple_intro _ _ _,N.orderedPair_intro _ _,hi,available,choice⟩
  obtain ⟨y,here,k,d,b,j,g,read,pair,jIn,gIn,result⟩ :=
    contains _ (N.in_pairBound hi available) ⟨v,witness⟩
  obtain ⟨sameK,sameD,sameB⟩ := N.triple_inj read (N.triple_intro U.key U.domain input)
  obtain ⟨sameJ,sameG⟩ := Internal.orderedPair_injective pair (N.orderedPair_intro i f)
  subst k
  subst j
  subst g
  exact ⟨y,here,result⟩

def LeastBound (key domain previous height : V) : Prop :=
  U.CoveredBy key domain previous height ∧ ∀ a, N.mem a height → ¬U.CoveredBy key domain previous a

theorem leastBound_def {n k d s a : Nat} (hk : k < n) (hd : d < n) (hs : s < n) (ha : a < n) :
    N.square.Definable n (fun env => U.LeastBound (env k) (env d) (env s) (env a)) :=
  (U.coveredBy_def hk hd hs ha).and (Definable.boundedAll ha _
    (U.coveredBy_def (n := n+1) (k := k+1) (d := d+1) (s := s+1) (a := 0)
      (by omega) (by omega) (by omega) (by omega)).not)

theorem leastBound_unique {key domain s a b : V}
    (ha : U.LeastBound key domain s a) (hb : U.LeastBound key domain s b) : a = b := by
  obtain ⟨_, rankA,_⟩ := ha.1
  obtain ⟨_, rankB,_⟩ := hb.1
  rcases N.ordinal_compare rankA.1 rankB.1 with left | same | right
  · exact (hb.2 a left ha.1).elim
  · exact same
  · exact (ha.2 b right hb.1).elim

theorem leastBound_exists {w : V} (omega : Internal.Omega N.mem w) (regular : N.Regular) (preceding : V) :
    ∃ a, U.LeastBound U.key U.domain preceding a := by
  obtain ⟨bound, covered⟩ := U.possible_bound omega regular preceding
  have ordinal : N.Ordinal bound := by
    obtain ⟨_,rank,_⟩ := covered
    exact rank.1
  have defn := U.coveredBy_def (n := 4) (k := 2) (d := 3) (s := 1) (a := 0)
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨a,_,hA,minimal⟩ := N.least_definable_ordinal [U.key,U.domain] preceding defn ⟨bound,ordinal,covered⟩
  exact ⟨a,hA,minimal⟩

def BoundStep (params : V) (_ : V) (previous height : V) : Prop :=
  ∃ key domain, Internal.OrderedPair N.mem key domain params ∧
    ((∃ stage, N.SupRank previous stage ∧ U.LeastBound key domain stage height) ∨
      ((¬∃ stage, N.SupRank previous stage) ∧ Internal.Empty N.mem height))

theorem boundStep_def : Definable.Relation4 N U.BoundStep := by
  intro n k _ f h hk _ hf hh
  have key := Definable.orderedPair (N := N) (n := n+2) (i := 1) (j := 0) (k := k+2)
    (by omega) (by omega) (by omega)
  have supremum := N.supRank_def (n := n+3) (f := f+3) (s := 0) (by omega) (by omega)
  have covering := U.leastBound_def (n := n+3) (k := 2) (d := 1) (s := 0) (a := h+3)
    (by omega) (by omega) (by omega) (by omega)
  have default_ := (Definable.ex supremum).not.and
    (Definable.empty (N := N) (n := n+2) (i := h+2) (by omega))
  exact Definable.ex (Definable.ex (key.and ((Definable.ex (supremum.and covering)).or default_)))

theorem boundStep_exists {w : V} (omega : Internal.Omega N.mem w) (regular : N.Regular)
    (i previous : V) : ∃ height, U.BoundStep (N.orderedPair U.key U.domain) i previous height := by
  classical
  by_cases existsStage : ∃ stage, N.SupRank previous stage
  · obtain ⟨stage,sup⟩ := existsStage
    obtain ⟨a, ha⟩ := U.leastBound_exists omega regular stage
    exact ⟨a,U.key,U.domain,N.orderedPair_intro _ _,Or.inl ⟨stage,sup,ha⟩⟩
  · exact ⟨N.empty,U.key,U.domain,N.orderedPair_intro _ _,Or.inr ⟨existsStage,N.empty_mem⟩⟩

theorem boundStep_unique (params i previous a b : V)
    (ha : U.BoundStep params i previous a) (hb : U.BoundStep params i previous b) : a = b := by
  obtain ⟨k,d,ka,hA⟩ := ha
  obtain ⟨k',d',kb,hB⟩ := hb
  obtain ⟨same,eq⟩ := Internal.orderedPair_injective ka kb
  subst k'
  subst d'
  rcases hA with ⟨stage, prior, validA⟩ | ⟨none, emptyA⟩ <;>
    rcases hB with ⟨s, prior', validB⟩ | ⟨none', emptyB⟩
  · cases N.supRank_unique prior prior'
    exact U.leastBound_unique validA validB
  · exact (none' ⟨stage,prior⟩).elim
  · exact (none ⟨s,prior'⟩).elim
  · exact ((N.empty_unique a).mp emptyA).trans ((N.empty_unique b).mp emptyB).symm

theorem boundStep_ordinal {params i previous a : V} (h : U.BoundStep params i previous a) : N.Ordinal a := by
  obtain ⟨k,d,code,step⟩ := h
  rcases step with ⟨s,sup,covered⟩ | ⟨no,empty⟩
  · obtain ⟨v,rank,_⟩ := covered.1
    exact rank.1
  · exact ((N.empty_unique a).mp empty).symm ▸ N.ordinal_empty

noncomputable def boundsRecursor {w : V} (omega : Internal.Omega N.mem w) (regular : N.Regular) :
    SetRecursion N :=
  ⟨U.domain,U.domain,N.orderedPair U.key U.domain,fun _ => N.mem,Definable.membership_relation,
    U.ordered.ordered,U.BoundStep,U.boundStep_def,U.boundStep_exists omega regular,U.boundStep_unique _⟩

end ClassUpdate
end PalomarI3380.SquareRepresentation.SetContext
