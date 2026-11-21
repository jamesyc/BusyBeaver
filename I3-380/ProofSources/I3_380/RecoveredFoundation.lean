module
public import I3_380.RankedStages
public import I3_380.RegularRanks
@[expose] public section

namespace PalomarI3380.SquareRepresentation.NamedModel

open Logic SetContext

variable {A V : Type} {M : Algebra A} (N : NamedModel M V)

/-- Every nonempty set has a member of least rank. The minimization
takes place in a bounded set of ordinal candidates. -/
theorem foundation (a : V) (ha : N.NonemptySet a) :
    ∃ x, N.mem x a ∧ ∀ y, N.mem y x → ¬N.mem y a := by
  obtain ⟨z, hz⟩ := ha
  obtain ⟨height, stage, ranked, belongs⟩ := N.every_set_in_rank z
  let bound := N.succ height
  have hOrd := N.ordinal_succ ranked.1
  have hRank := Definable.rank (N := N.toSetContext) (n := 4) (i := 2) (j := 0) (by decide) (by decide)
  have inStage := Definable.mem (N := N.toSetContext) (n := 4) (i := 1) (j := 0) (by decide) (by decide)
  have defn := Definable.boundedEx (S := N.square) (n := 2) (i := 1) (by decide) _
    (Definable.ex (hRank.and inStage))
  obtain ⟨candidates, spec⟩ := N.separate [] defn bound a
  have sub : N.Subset candidates bound := fun x hx => ((spec x).mp hx).1
  have inhabited : N.NonemptySet candidates := ⟨height, (spec height).mpr
    ⟨(N.mem_succ _ _).mpr (Or.inr rfl), z, hz, stage, ranked, belongs⟩⟩
  obtain ⟨l, hl, minimal⟩ := hOrd.ordered.least candidates sub inhabited
  obtain ⟨inBound, x, xIn, bottom, bottomRank, member⟩ := (spec l).mp hl
  refine ⟨x, xIn, fun y yIn alsoA => ?_⟩
  obtain ⟨k, earlier, kl, rank, subX⟩ := (N.mem_rank_iff bottomRank x).mp member
  have less : N.mem k bound := hOrd.transitive l inBound k kl
  have yes := (spec k).mpr ⟨less, y, alsoA, earlier, rank, subX y yIn⟩
  rcases minimal k yes with eq | wrong
  · exact hOrd.ordered.irrefl l inBound (eq.symm ▸ kl)
  · exact WellOrderOn.asymm N.toSetContext hOrd.ordered less inBound kl wrong

theorem fixed_foundation (env : Nat → V) : eval N.mem fixedFoundation env := by
  intro a hasElem
  obtain ⟨x, hx, min⟩ := N.foundation a hasElem
  exact ⟨x, hx, min⟩

theorem ordinal_of_transitives {a : V} (trans : N.Transitive a)
    (members : ∀ x, N.mem x a → N.Transitive x) : N.Ordinal a :=
  N.toSetContext.ordinal_of_transitives N.foundation trans members

/-- Each rank contains the corresponding initial segment of ordinals. -/
theorem rank_contains_ordinal {a stage : V} (h : N.Rank a stage) : N.Subset a stage := by
  let bound := N.succ a
  have ord := N.ordinal_succ h.1
  have desc := Definable.all ((Definable.rank (N := N.toSetContext) (n := 3) (i := 1) (j := 0)
    (by decide) (by decide)).implies
    (Definable.subset (N := N.toSetContext) (n := 3) (i := 1) (j := 0) (by decide) (by decide)))
  have induction_ := N.order_induction (a := bound) ord.ordered [] desc fun b hb ih u hu => by
    intro c hc
    obtain ⟨v, hv⟩ := N.rank_exists (hu.1.of_mem N.toSetContext hc)
    exact (N.mem_rank_iff hu c).mpr ⟨c, v, hc, hv, ih c (ord.transitive b hb c hc) hc v hv⟩
  exact induction_ a ((N.mem_succ _ _).mpr (Or.inr rfl)) stage h

theorem rank_empty {v : V} (h : N.Rank N.empty v) : v = N.empty := by
  apply (N.empty_unique v).mp
  intro z hz
  obtain ⟨a, u, ha, _, _⟩ := (N.mem_rank_iff h z).mp hz
  exact N.empty_mem a ha

theorem rank_successor {a v next : V} (r : N.Rank a v) (r' : N.Rank (N.succ a) next) :
    next = N.power v := by
  apply N.ext
  intro x
  rw [N.mem_power, N.mem_rank_iff r']
  constructor
  · rintro ⟨b, u, hb, hr, sub⟩
    have entry := (N.mem_succ a b).mp hb
    have subHeight := (N.ordinal_subset_iff hr.1 r.1).mpr entry
    exact N.subset_trans sub (N.rank_subset hr r subHeight)
  · exact fun h => ⟨a, v, (N.mem_succ _ _).mpr (Or.inr rfl), r, h⟩

end PalomarI3380.SquareRepresentation.NamedModel
