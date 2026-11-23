module
public import I3_334Support.Equations.RecoveredInfinity
@[expose] public section

namespace PalomarI3380.SquareRepresentation.NamedModel

open Logic SetContext

variable {A V : Type} {M : Algebra A} (N : NamedModel M V)

theorem recovered_zfc (p : Formula) (h : Axiom p ∨ p = choiceAxiom) (env : Nat → V) :
    eval N.mem p env := by
  have basic (h : SquareRepresentation.BaseAxiom p) :=
    N.square.base_axioms N.projections N.laws N.names N.pairs p h env
  rcases h with axiom_ | choice
  · rcases axiom_ with fixed | separation | replacement
    · rcases fixed with h | h | h | h | h | h | h | h | h | h | h
      all_goals subst p
      all_goals first
        | exact N.fixed_omega env
        | exact N.fixed_foundation env
        | exact basic (by simp [SquareRepresentation.BaseAxiom])
    · obtain ⟨n, body, bound, rfl⟩ := separation
      exact separation_schema N.projections N.laws N.names body n bound env
    · obtain ⟨n, body, bound, rfl⟩ := replacement
      exact replacement_schema N.projections N.laws N.names body n bound env
  · exact basic (by simp [SquareRepresentation.BaseAxiom, choice])

theorem active_empty : N.square.activePoint N.empty := by
  obtain ⟨w, hw, _⟩ := N.active_omega_exists
  exact active_subset N.laws hw (fun x hx => (N.empty_mem x hx).elim)

theorem active_pair {a b : V} (ha : N.square.activePoint a) (hb : N.square.activePoint b) :
    N.square.activePoint (N.pair a b) := by
  obtain ⟨p, hp, pair⟩ := N.active_closure.pairs ha hb
  have same := Internal.pair_unique N.ext pair (N.mem_pair a b)
  exact same ▸ hp

theorem active_singleton {a : V} (h : N.square.activePoint a) : N.square.activePoint (N.singleton a) :=
  N.active_pair h h

theorem active_union {a : V} (ha : N.square.activePoint a) : N.square.activePoint (N.union a) := by
  obtain ⟨_, v, ranked, activeV, aIn⟩ := N.active_rank ha
  apply active_subset N.laws activeV
  intro z hz
  obtain ⟨u, uIn, member⟩ := (N.mem_union _ _).mp hz
  have tv := N.rank_transitive ranked
  exact tv u (tv a aIn u uIn) z member

theorem active_union₂ {a b : V} (ha : N.square.activePoint a) (hb : N.square.activePoint b) :
    N.square.activePoint (N.union₂ a b) :=
  N.active_union (N.active_pair ha hb)

theorem active_succ {a : V} (h : N.square.activePoint a) : N.square.activePoint (N.succ a) :=
  N.active_union₂ h (N.active_singleton h)

theorem active_canonical_power {a : V} (h : N.square.activePoint a) : N.square.activePoint (N.power a) :=
  SquareRepresentation.active_power N.laws h (N.mem_power a)

theorem active_orderedPair {a b : V} (ha : N.square.activePoint a) (hb : N.square.activePoint b) :
    N.square.activePoint (N.orderedPair a b) :=
  N.active_pair (N.active_singleton ha) (N.active_pair ha hb)

theorem orderedPair_coordinates {a b p : V} (h : Internal.OrderedPair N.mem a b p)
    (active : N.square.activePoint p) :
    N.square.activePoint a ∧ N.square.activePoint b := by
  obtain ⟨aa, ab, _, hab, pair⟩ := h
  have abActive := active_transitive N.laws active ((pair ab).mpr (Or.inr rfl))
  exact ⟨active_transitive N.laws abActive ((hab a).mpr (Or.inl rfl)),
    active_transitive N.laws abActive ((hab b).mpr (Or.inr rfl))⟩

theorem active_graph_coordinates {f a b : V} (h : Internal.At N.mem f a b)
    (active : N.square.activePoint f) : N.square.activePoint a ∧ N.square.activePoint b := by
  obtain ⟨p, hp, pair⟩ := h
  exact N.orderedPair_coordinates pair (active_transitive N.laws active hp)

theorem absolute_transitive (a : N.Active) :
    (∀ x, N.localMem x a → ∀ y, N.localMem y x → N.localMem y a) ↔ N.Transitive a.val := by
  constructor
  · intro h x hx y hy
    let p : N.Active := ⟨x, active_transitive N.laws a.property hx⟩
    let q : N.Active := ⟨y, active_transitive N.laws p.property hy⟩
    exact h p hx q hy
  · exact fun h x hx y hy => h x.val hx y.val hy

theorem absolute_ordinal (a : N.Active) :
    ((∀ x, N.localMem x a → ∀ y, N.localMem y x → N.localMem y a) ∧
      ∀ x, N.localMem x a → ∀ y, N.localMem y x → ∀ z, N.localMem z y → N.localMem z x) ↔
        N.Ordinal a.val := by
  constructor
  · rintro ⟨h, xTrans⟩
    apply N.ordinal_of_transitives ((N.absolute_transitive a).mp h)
    intro x hx
    let p : N.Active := ⟨x, active_transitive N.laws a.property hx⟩
    exact (N.absolute_transitive p).mp (xTrans p hx)
  · intro h
    exact ⟨(N.absolute_transitive a).mpr h.transitive,
      fun x hx => (N.absolute_transitive x).mpr (h.members_transitive x.val hx)⟩

theorem absolute_successor (a b : N.Active) :
    Internal.Succ N.localMem a b ↔ Internal.Succ N.mem a.val b.val := by
  constructor
  · intro h x
    constructor
    · intro hx
      let z : N.Active := ⟨x, active_transitive N.laws b.property hx⟩
      exact ((h z).mp hx).elim Or.inl (fun same => Or.inr (congrArg Subtype.val same))
    · intro candidate
      have active : N.square.activePoint x := candidate.elim (active_transitive N.laws a.property)
        (fun same => same.symm ▸ a.property)
      let z : N.Active := ⟨x, active⟩
      exact (h z).mpr (candidate.elim Or.inl (fun same => Or.inr (Subtype.ext same)))
  · intro h z
    exact (h z.val).trans (or_congr Iff.rfl Subtype.ext_iff.symm)

theorem preserves_successor (a b : N.Active) :
    Internal.Succ N.mem a.val b.val ↔ Internal.Succ N.mem (N.embedding a).val (N.embedding b).val := by
  let p := SetFormula.successor 0 1
  have meaning (a b : N.Active) :
      SetFormula.holds N.localMem p 2 (N.twoValues a b) a ↔ Internal.Succ N.mem a.val b.val := by
    refine Iff.trans ?_ (N.absolute_successor a b)
    simpa [p, twoValues] using (SetFormula.holds_successor (E := N.localMem)
      (env := N.twoValues a b) (default := a) (a := 0) (b := 1) (d := 2) (by decide) (by decide))
  have h := N.preserves_builder p 2 (SetFormula.scope_successor (by decide) (by decide)) (N.twoValues a b) a
  rw [N.map_twoValues] at h
  exact (meaning a b).symm.trans (h.trans (meaning _ _))

end PalomarI3380.SquareRepresentation.NamedModel
