module
public import I3_334Support.SetTheory.Rank.LimitElementarity
public import I3_334Support.Logic.Soundness
@[expose] public section

namespace PalomarI3380.SquareRepresentation.NamedModel

open Logic SetContext

variable {A V : Type} {M : Algebra A} (N : NamedModel M V)

theorem rank_to_internal {a stage : V} (rank : N.Rank a stage) : Internal.RankLike N.mem a stage := by
  obtain ⟨ordinal, graph, info, value⟩ := rank
  exact ⟨⟨ordinal.transitive, ordinal.members_transitive⟩, N.succ a, graph, N.mem_succ a,
    ⟨info.functionOn, fun b _ s entry => info.members b s entry⟩, value⟩

theorem limit_graph {w heights stages limit : V} (run : N.CriticalRun w heights stages)
    (omega : Internal.Omega N.mem w)
    (covers : ∀ x, N.mem x limit ↔ ∃ n stage, Internal.At N.mem stages n stage ∧ N.mem x stage) :
    ∃ graph, Internal.FunctionInto N.mem graph limit limit ∧
      ∀ x y, Internal.At N.mem graph x y ↔ N.mem x limit ∧ N.square.rel (M.constant .J) x y := by
  have active (x : V) (hx : N.mem x limit) : N.square.activePoint x := by
    obtain ⟨i,s,atS,hs⟩ := (covers x).mp hx
    exact active_transitive N.laws (run.stageSequence.active i s atS) hs
  have reachable (x : V) (hx : N.mem x limit) :
      ∃ y, N.square.rel (M.constant .J) x y :=
    j_has_image N.laws ⟨x, active x hx⟩
  have defn := Definable.atom (S := N.square) (n := 2) (M.constant .J)
    (i := 0) (j := 1) (by decide) (by decide)
  obtain ⟨graph, function, values⟩ := N.functionOf [] defn
    (fun _ _ _ ha hb => j_single_valued N.laws N.active_closure ha hb) limit reachable
  refine ⟨graph, ⟨function, fun x hx y hy => ?_⟩, values⟩
  have edge := ((values x y).mp hy).2
  obtain ⟨i,stage,atStage,member⟩ := (covers x).mp hx
  have iIn := SetRecursion.at_domain run.stageSequence.functionOn atStage
  obtain ⟨next,atNext,_⟩ := run.stageSequence.functionOn.1 (N.succ i) (N.omega_succ omega iIn)
  let s : N.Active := ⟨stage, run.stageSequence.active i stage atStage⟩
  let t : N.Active := ⟨next, run.stageSequence.active (N.succ i) next atNext⟩
  let p : N.Active := ⟨x,active x hx⟩
  have stageImage := run.stageSequence.image (a := s) (b := t) iIn atStage atNext
  have fact := (N.preserves_membership p s).mp member
  rw [stageImage] at fact
  have value : (N.embedding p).val = y := j_single_valued N.laws N.active_closure (N.embedding_edge p) edge
  exact (covers y).mpr ⟨N.succ i,next,atNext,value ▸ fact⟩

theorem limit_embedding_elementary {w heights stages limit f : V}
    (run : N.CriticalRun w heights stages) (omega : Internal.Omega N.mem w)
    (activeW : N.square.activePoint w)
    (covers : ∀ x, N.mem x limit ↔ ∃ n stage, Internal.At N.mem stages n stage ∧ N.mem x stage)
    (graph : ∀ x y, Internal.At N.mem f x y ↔ N.mem x limit ∧ N.square.rel (M.constant .J) x y) :
    Internal.ElementaryOnRank N.mem w limit f := by
  intro arity count rows code
  obtain ⟨_,sat,_,_,table⟩ := N.truthSet_exists omega code limit
  refine ⟨sat,table,fun i hi source target typedSource typedTarget mapped => ?_⟩
  obtain ⟨n, earlier, hEarlier, sourceIn⟩ := run.bound_assignment omega
    (fun _ hx => (covers _).mp hx) arity code.1 source typedSource
  have nIn := SetRecursion.at_domain run.stageSequence.functionOn hEarlier
  obtain ⟨later,hLater,_⟩ := run.stageSequence.functionOn.1 (N.succ n) (N.omega_succ omega nIn)
  let a : N.Active := ⟨arity,active_transitive N.laws activeW code.1⟩
  let c : N.Active := ⟨count,active_transitive N.laws activeW code.2.1⟩
  let r : N.Active := ⟨rows,N.syntax_active omega activeW code⟩
  let ix : N.Active := ⟨i,active_transitive N.laws c.property hi⟩
  let s : N.Active := ⟨earlier, run.stageSequence.active n earlier hEarlier⟩
  let t : N.Active := ⟨later, run.stageSequence.active (N.succ n) later hLater⟩
  let env : N.Active := ⟨source,N.assignment_active sourceIn a.property s.property⟩
  have jS := run.stageSequence.image (a := s) (b := t) nIn hEarlier hLater
  have fixA := N.fixes_natural omega activeW a code.1
  have newType := (N.preserves_functionInto env a s).mp sourceIn
  rw [jS,fixA] at newType
  have supports (j x : V) (hj : N.mem j arity) (atSource : Internal.At N.mem source j x) :
      ∃ y, Internal.At N.mem (N.embedding env).val j y ∧ Internal.At N.mem target j y := by
    let index : N.Active := ⟨j,active_transitive N.laws a.property hj⟩
    let v : N.Active := ⟨x,active_transitive N.laws s.property (sourceIn.2 j hj x atSource)⟩
    have fixIndex := N.fixes_natural omega activeW index ((N.omega_ordinal omega).transitive arity code.1 j hj)
    have act := (N.preserves_at env index v).mp atSource
    rw [fixIndex] at act
    have member : N.mem x limit := typedSource.2 j hj x atSource
    have value := (graph x (N.embedding v).val).mpr ⟨member,N.embedding_edge v⟩
    exact ⟨(N.embedding v).val,act,mapped j hj x _ atSource value⟩
  have sameTarget : (N.embedding env).val = target := by
    apply N.function_ext newType.1 typedTarget.1
    intro j v hj
    obtain ⟨x, atX, _⟩ := typedSource.1.1 j hj
    obtain ⟨y, new, provided⟩ := supports j x hj atX
    obtain ⟨_,_,one⟩ := newType.1.1 j hj
    obtain ⟨_,_,other⟩ := typedTarget.1.1 j hj
    exact ⟨fun hv => ((one y new).trans (one v hv).symm) ▸ provided,
      fun hv => ((other y provided).trans (other v hv).symm) ▸ new⟩
  have targetIn : Internal.FunctionInto N.mem target arity later := sameTarget ▸ newType
  have sourceElementary := run.elementary_limit omega covers n earlier hEarlier
  have targetElementary := run.elementary_limit omega covers (N.succ n) later hLater
  have transported := N.preserves_satisfiesAt omega activeW a c r s ix env code hi sourceIn
  rw [jS, sameTarget] at transported
  exact (N.satisfiesAt_iff_table omega code table hi typedSource).symm.trans
    ((sourceElementary.2 _ _ _ code i hi source sourceIn).symm.trans
      (transported.trans ((targetElementary.2 _ _ _ code i hi target targetIn).trans
        (N.satisfiesAt_iff_table omega code table hi typedTarget))))

/-- The limit of the internally coded critical sequence carries the
nonidentity elementary embedding required by the literal I3 axiom. -/
theorem recovered_i3 : Internal.HasI3 N.mem := by
  obtain ⟨w,active,omega⟩ := N.active_omega_exists
  obtain ⟨point,stage,crit⟩ := N.critical_exists
  obtain ⟨heights,stages,run,h0,s0⟩ := N.critical_run omega active crit
  obtain ⟨limit,rank,below,covers⟩ := run.limitRank omega
  obtain ⟨graph,into,values⟩ := N.limit_graph run omega covers
  have pointIn := N.rank_contains_ordinal rank point.val (below N.empty point.val h0)
  have edge := (values point.val (N.embedding point).val).mpr ⟨pointIn,N.embedding_edge point⟩
  have otherIn := into.2 point.val pointIn (N.embedding point).val edge
  have different : point.val ≠ (N.embedding point).val := by
    intro eq
    have moved : N.mem point.val (N.embedding point).val := crit.movesUp
    exact crit.rank.1.not_mem_self N.toSetContext (by simpa only [← eq] using moved)
  exact ⟨w, N.union (N.range heights), limit, graph, omega, N.rank_to_internal rank, run.limit_inductive omega rank below, into,
    ⟨point.val, (N.embedding point).val, pointIn, otherIn, edge, different⟩,
    N.limit_embedding_elementary run omega active covers values⟩

theorem recovered_model : ZFCI3Model N.mem := by
  intro p h env
  rcases h with zf | choice | same
  · exact N.recovered_zfc p (Or.inl zf) env
  · exact N.recovered_zfc p (Or.inr choice) env
  · subst p
    exact SetFormula.holds_i3.mpr N.recovered_i3

end PalomarI3380.SquareRepresentation.NamedModel

namespace PalomarI3380

theorem consistency_of_equational_underivability
    (h : ¬Derives Manifest.final (.const .D) (.const .J)) : Logic.ZFCI3Consistent := by
  obtain ⟨_, _, _, ⟨N⟩⟩ := SquareRepresentation.namedModel_of_underivability h
  exact Logic.NDSemantics.consistency_of_model N.mem N.exists_point N.recovered_model

end PalomarI3380
