module
public import I3_334Support.SetTheory.Classes.ActiveGraphs
public import I3_334Support.Logic.RankSemantics
@[expose] public section

namespace PalomarI3380.SquareRepresentation.NamedModel

open Logic SetContext

variable {A V : Type} {M : Algebra A} (N : NamedModel M V)

theorem ordinal_in_rank {a stage b : V} (rank : N.Rank a stage) (ord : N.Ordinal b) :
    N.mem b stage ↔ N.mem b a := by
  refine ⟨?_, N.rank_contains_ordinal rank b⟩
  let top := N.succ a
  have ordTop := N.ordinal_succ rank.1
  have defn := Definable.all ((Definable.rank (N := N.toSetContext) (n := 3) (i := 1) (j := 0)
    (by decide) (by decide)).implies (Definable.boundedAll (i := 0) (by decide) _
      ((Definable.ordinal (N := N.toSetContext) (n := 4) (i := 0) (by decide)).implies
        (Definable.mem (N := N.toSetContext) (n := 4) (i := 0) (j := 2) (by decide) (by decide)))))
  have induction_ := N.order_induction (a := top) ordTop.ordered [] defn
    (fun h ht ih v hv x hx xOrd => by
      obtain ⟨below, early, bh, eb, sub⟩ := (N.mem_rank_iff hv x).mp hx
      have xSubset : N.Subset x below := fun z hz =>
        ih below (ordTop.transitive h ht below bh) bh early eb z (sub z hz) (xOrd.of_mem N.toSetContext hz)
      rcases (N.ordinal_subset_iff xOrd eb.1).mp xSubset with xb | eq
      · exact hv.1.transitive below bh x xb
      · exact eq.symm ▸ bh)
  exact fun hx => induction_ a ((N.mem_succ _ _).mpr (Or.inr rfl)) stage rank b hx ord

theorem active_rank_value {a stage : V} (ha : N.square.activePoint a) (h : N.Rank a stage) :
    N.square.activePoint stage := by
  obtain ⟨b, v, hr, active, below⟩ := N.active_rank ha
  have rankBound := (N.ordinal_in_rank hr h.1).mp below
  exact active_transitive N.laws active (N.rank_member h hr rankBound)

theorem active_rank_graph {a stage f : V} (h : N.Rank a stage)
    (graph : N.Hierarchy a f) (target : Internal.At N.mem f a stage)
    (active : N.square.activePoint a) : N.square.activePoint f := by
  let cover := N.union₂ (N.succ a) (N.succ stage)
  have both := N.active_union₂ (N.active_succ active) (N.active_succ (N.active_rank_value active h))
  have bounded : N.Subset f (N.power (N.power cover)) := by
    intro p hp
    obtain ⟨k, v, hk, pair⟩ := graph.functionOn.2 p hp
    have code := (N.orderedPair_iff k v p).mp pair
    subst p
    have atV : Internal.At N.mem f k v := ⟨_, hp, pair⟩
    have contents : N.mem v (N.succ stage) := by
      apply (N.mem_succ _ _).mpr
      rcases (N.mem_succ _ _).mp hk with earlier | same
      · have rk := N.hierarchy_value_rank (h.1.of_mem N.toSetContext earlier) h.1
          (h.1.transitive k earlier) graph atV
        exact Or.inl (N.rank_member rk h earlier)
      · subst k
        obtain ⟨_, _, only⟩ := graph.functionOn.1 a hk
        exact Or.inr ((only v atV).trans (only stage target).symm)
    exact N.orderedPair_bound ((N.mem_union₂ _ _ _).mpr (Or.inl hk))
      ((N.mem_union₂ _ _ _).mpr (Or.inr contents))
  exact active_subset N.laws (N.active_canonical_power (N.active_canonical_power both)) bounded

private theorem absolute_stage_members (f b stage : N.Active) :
    (∀ x, N.localMem x stage ↔ ∃ a, N.localMem a b ∧ ∃ earlier,
      Internal.At N.localMem f a earlier ∧ ∀ z, N.localMem z x → N.localMem z earlier) ↔
    (∀ x, N.mem x stage.val ↔ ∃ a, N.mem a b.val ∧ ∃ earlier,
      Internal.At N.mem f.val a earlier ∧ N.Subset x earlier) := by
  constructor
  · intro rel x
    constructor
    · intro hx
      let x' : N.Active := ⟨x, active_transitive N.laws stage.property hx⟩
      obtain ⟨a, ha, earlier, value, inc⟩ := (rel x').mp hx
      exact ⟨a.val, ha, earlier.val, (N.absolute_at f a earlier).mp value, (N.absolute_subset _ _).mp inc⟩
    · rintro ⟨a, ha, earlier, atValue, sub⟩
      let a' : N.Active := ⟨a, active_transitive N.laws b.property ha⟩
      let earlier' : N.Active := ⟨earlier, (N.active_graph_coordinates atValue f.property).2⟩
      let x' : N.Active := ⟨x, active_subset N.laws earlier'.property sub⟩
      exact (rel x').mpr ⟨a', ha, earlier', (N.absolute_at f a' earlier').mpr atValue,
        (N.absolute_subset _ _).mpr sub⟩
  · intro exactness x
    constructor
    · intro hx
      obtain ⟨a, ha, earlier, atValue, sub⟩ := (exactness x.val).mp hx
      let a' : N.Active := ⟨a, active_transitive N.laws b.property ha⟩
      let earlier' : N.Active := ⟨earlier, (N.active_graph_coordinates atValue f.property).2⟩
      exact ⟨a', ha, earlier', (N.absolute_at f a' earlier').mpr atValue, (N.absolute_subset _ _).mpr sub⟩
    · rintro ⟨a, ha, prior, atValue, sub⟩
      exact (exactness x.val).mpr ⟨a.val, ha, prior.val, (N.absolute_at f a prior).mp atValue,
        (N.absolute_subset _ _).mp sub⟩

theorem absolute_rank (a stage : N.Active) :
    Internal.RankLike N.localMem a stage ↔ N.Rank a.val stage.val := by
  constructor
  · rintro ⟨ord, domain, f, next, rules, target⟩
    have hOrd := (N.absolute_ordinal a).mp ord
    have domEq := (N.internal_succ _ _).mp ((N.absolute_successor a domain).mp next)
    have funOn := (N.absolute_functionOn f domain).mp rules.1
    refine ⟨hOrd, f.val, ⟨domEq ▸ funOn, fun t s ht => ?_⟩, (N.absolute_at f a stage).mp target⟩
    have act := N.active_graph_coordinates ht f.property
    let time : N.Active := ⟨t, act.1⟩
    let value : N.Active := ⟨s, act.2⟩
    have within := SetRecursion.at_domain funOn ht
    exact (N.absolute_stage_members f time value).mp (rules.2 time within value ((N.absolute_at _ _ _).mpr ht))
  · intro h
    obtain ⟨ord, f, hf, result⟩ := h
    let dom : N.Active := ⟨N.succ a.val, N.active_succ a.property⟩
    let graph : N.Active := ⟨f, N.active_rank_graph ⟨ord, f, hf, result⟩ hf result a.property⟩
    refine ⟨(N.absolute_ordinal a).mpr ord, dom, graph,
      (N.absolute_successor _ _).mpr (N.mem_succ _),
      ⟨(N.absolute_functionOn _ _).mpr hf.functionOn, fun b _ v hv => ?_⟩,
      (N.absolute_at _ _ _).mpr result⟩
    exact (N.absolute_stage_members graph b v).mpr (hf.members _ _ ((N.absolute_at _ _ _).mp hv))

theorem preserves_rank (a stage : N.Active) :
    N.Rank a.val stage.val ↔ N.Rank (N.embedding a).val (N.embedding stage).val := by
  let p := SetFormula.rank 0 1
  have meaning (x y : N.Active) :
      SetFormula.holds N.localMem p 2 (N.twoValues x y) x ↔ N.Rank x.val y.val := by
    refine Iff.trans ?_ (N.absolute_rank x y)
    simpa [p, twoValues] using (SetFormula.holds_rank (E := N.localMem)
      (env := N.twoValues x y) (default := x) (a := 0) (b := 1) (d := 2) (by decide) (by decide))
  have preserv := N.preserves_builder p 2 (SetFormula.scope_rank (by decide) (by decide)) (N.twoValues a stage) a
  rw [N.map_twoValues] at preserv
  exact (meaning a stage).symm.trans (preserv.trans (meaning _ _))

theorem preserves_ordinal (a : N.Active) : N.Ordinal a.val ↔ N.Ordinal (N.embedding a).val := by
  have meaning (x : N.Active) :
      SetFormula.holds N.localMem (SetFormula.ordinal 0) 1 (fun _ => x) x ↔ N.Ordinal x.val :=
    (SetFormula.holds_ordinal (E := N.localMem) (env := fun _ => x) (default := x) (d := 1)
      (by decide)).trans (N.absolute_ordinal x)
  have h := N.preserves_builder (SetFormula.ordinal 0) 1 (SetFormula.scope_ordinal (by decide)) (fun _ => a) a
  exact (meaning a).symm.trans (h.trans (meaning _))

end PalomarI3380.SquareRepresentation.NamedModel
