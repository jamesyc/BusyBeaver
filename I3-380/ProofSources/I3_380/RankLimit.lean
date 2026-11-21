module
public import I3_380.CriticalSequence
@[expose] public section

namespace PalomarI3380.SquareRepresentation.NamedModel

open Logic SetContext

variable {A V : Type} {M : Algebra A} {N : NamedModel M V}

theorem CriticalRun.pairwise {w heights stages : V} (run : N.CriticalRun w heights stages)
    (omega : Internal.Omega N.mem w) :
    ∀ n, N.mem n w → ∀ m u v,
      (N.mem m n ∨ m = n) → Internal.At N.mem stages m u → Internal.At N.mem stages n v →
      Internal.ElementaryIncluded N.mem w u v := by
  have before := (Definable.mem (N := N.toSetContext) (n := 7) (i := 2) (j := 3) (by decide) (by decide)).or
    (Definable.eq (S := N.square) (n := 7) (i := 2) (j := 3) (by decide) (by decide))
  have earlier := Definable.graphValue (N := N.toSetContext) (n := 7) (i := 5) (j := 2) (k := 1)
    (by decide) (by decide) (by decide)
  have later := Definable.graphValue (N := N.toSetContext) (n := 7) (i := 5) (j := 3) (k := 0)
    (by decide) (by decide) (by decide)
  have included := Definable.elementaryIncluded (N := N) (n := 7) (w := 6) (a := 1) (b := 0)
    (by decide) (by decide) (by decide)
  have desc := Definable.all (Definable.all (Definable.all
    (before.implies (earlier.implies (later.implies included)))))
  have same (n u v : V) (hu : Internal.At N.mem stages n u) (hv : Internal.At N.mem stages n v) : u = v := by
    obtain ⟨_,_,one⟩ := run.stageSequence.functionOn.1 n
      (SetRecursion.at_domain run.stageSequence.functionOn hu)
    exact (one u hu).trans (one v hv).symm
  apply N.omega_induction omega [stages,w] desc w
  · intro m u v precedes hu hv
    change N.mem m N.empty ∨ m = N.empty at precedes
    rcases precedes with impossible | eq
    · exact (N.empty_mem m impossible).elim
    · subst m
      exact same N.empty u v hu hv ▸ N.elementary_refl w u
  · intro n hw ih m u v precedes hu hv
    change N.mem m (N.succ n) ∨ m = N.succ n at precedes
    rcases precedes with earlier | sameNext
    · obtain ⟨z, hz, _⟩ := run.stageSequence.functionOn.1 n hw
      exact N.elementary_trans (ih m u z ((N.mem_succ n m).mp earlier) hu hz)
        (run.elementary n hw z v hz hv)
    · subst m
      exact same (N.succ n) u v hu hv ▸ N.elementary_refl w u

/-- Rank at the supremum of the iterated heights. Each set in the
limit rank lies in an actual earlier stage of the sequence. -/
theorem CriticalRun.limitRank {w heights stages : V} (run : N.CriticalRun w heights stages)
    (omega : Internal.Omega N.mem w) :
    ∃ limit, N.Rank (N.union (N.range heights)) limit ∧
      (∀ n a, Internal.At N.mem heights n a → N.mem a (N.union (N.range heights))) ∧
      ∀ x, N.mem x limit ↔ ∃ n stage, Internal.At N.mem stages n stage ∧ N.mem x stage := by
  let height := N.union (N.range heights)
  have ordinals (x : V) (hx : N.mem x (N.range heights)) : N.Ordinal x := by
    obtain ⟨n, value⟩ := (N.mem_range _ _).mp hx
    have time := SetRecursion.at_domain run.heightSequence.functionOn value
    obtain ⟨s, hs, _⟩ := run.stageSequence.functionOn.1 n time
    exact (run.ranks n x s value hs).1
  have ho : N.Ordinal height := N.ordinal_union (N.range heights) ordinals
  obtain ⟨limit, hLimit⟩ := N.rank_exists ho
  have below (i a : V) (current : Internal.At N.mem heights i a) : N.mem a height := by
    have inW := SetRecursion.at_domain run.heightSequence.functionOn current
    obtain ⟨b, next, _⟩ := run.heightSequence.functionOn.1 (N.succ i) (N.omega_succ omega inW)
    exact (N.mem_union _ _).mpr ⟨b, (N.mem_range _ _).mpr ⟨N.succ i,next⟩,
      run.increasing i inW a b current next⟩
  refine ⟨limit,hLimit,below,fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨a, stage, ha, hRank, sub⟩ := (N.mem_rank_iff hLimit x).mp hx
    obtain ⟨b, hb, earlier⟩ := (N.mem_union _ _).mp ha
    obtain ⟨i, atHeight⟩ := (N.mem_range _ _).mp hb
    have onW := SetRecursion.at_domain run.heightSequence.functionOn atHeight
    obtain ⟨s, atStage, _⟩ := run.stageSequence.functionOn.1 i onW
    exact ⟨i,s,atStage,(N.mem_rank_iff (run.ranks i b s atHeight atStage) x).mpr
      ⟨a,stage,earlier,hRank,sub⟩⟩
  · rintro ⟨i,s,hStage,hx⟩
    have onW := SetRecursion.at_domain run.stageSequence.functionOn hStage
    obtain ⟨a, atHeight, _⟩ := run.heightSequence.functionOn.1 i onW
    exact N.rank_subset (run.ranks i a s atHeight hStage) hLimit (ho.transitive a (below i a atHeight)) x hx

theorem CriticalRun.limit_inductive {w heights stages limit : V} (run : N.CriticalRun w heights stages)
    (omega : Internal.Omega N.mem w) (rank : N.Rank (N.union (N.range heights)) limit)
    (below : ∀ n a, Internal.At N.mem heights n a → N.mem a (N.union (N.range heights))) :
    Internal.Inductive N.mem (N.union (N.range heights)) := by
  let sup := N.union (N.range heights)
  have ord := rank.1
  obtain ⟨a, ha, _⟩ := run.heightSequence.functionOn.1 N.empty (N.omega_zero omega)
  have nonempty : sup ≠ N.empty := fun h => N.empty_mem a (h ▸ below N.empty a ha)
  have zero : N.mem N.empty sup := ((N.ordinal_subset_iff N.ordinal_empty ord).mp
    (fun x hx => (N.empty_mem x hx).elim)).resolve_right (fun h => nonempty h.symm)
  refine ⟨⟨N.empty,N.empty_mem,zero⟩,fun x hx => ?_⟩
  obtain ⟨a, level, member⟩ := (N.mem_union _ _).mp hx
  obtain ⟨i, value⟩ := (N.mem_range _ _).mp level
  have aIn := below i a value
  have aOrd := ord.of_mem N.toSetContext aIn
  have xOrd := aOrd.of_mem N.toSetContext member
  have sub : N.Subset (N.succ x) a := fun y hy =>
    ((N.mem_succ x y).mp hy).elim (aOrd.transitive x member y) (fun h => h.symm ▸ member)
  have successorIncluded : N.mem (N.succ x) sup :=
    ((N.ordinal_subset_iff (N.ordinal_succ xOrd) aOrd).mp sub).elim
      (ord.transitive a aIn _) (fun h => h.symm ▸ aIn)
  exact ⟨N.succ x, N.mem_succ x,successorIncluded⟩

end PalomarI3380.SquareRepresentation.NamedModel
