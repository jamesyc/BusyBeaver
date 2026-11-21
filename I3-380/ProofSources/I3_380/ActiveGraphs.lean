module
public import I3_380.ActiveSets
public import I3_380.OmegaSets
@[expose] public section

namespace PalomarI3380.SquareRepresentation.NamedModel

open Logic SetContext

variable {A V : Type} {M : Algebra A} (N : NamedModel M V)

theorem absolute_pair (a b p : N.Active) :
    Internal.Pair N.localMem a b p ↔ Internal.Pair N.mem a.val b.val p.val := by
  constructor
  · intro h z
    constructor
    · intro hz
      let q : N.Active := ⟨z, active_transitive N.laws p.property hz⟩
      exact ((h q).mp hz).elim (fun eq => Or.inl (congrArg Subtype.val eq))
        (fun eq => Or.inr (congrArg Subtype.val eq))
    · intro hZ
      have active : N.square.activePoint z := hZ.elim (fun eq => eq.symm ▸ a.property)
        (fun eq => eq.symm ▸ b.property)
      exact (h ⟨z, active⟩).mpr (hZ.elim (fun eq => Or.inl (Subtype.ext eq))
        (fun eq => Or.inr (Subtype.ext eq)))
  · intro h z
    exact (h z.val).trans (or_congr Subtype.ext_iff.symm Subtype.ext_iff.symm)

theorem absolute_orderedPair (a b p : N.Active) :
    Internal.OrderedPair N.localMem a b p ↔
      Internal.OrderedPair N.mem a.val b.val p.val := by
  constructor
  · rintro ⟨aa, ab, first, second, pair⟩
    exact ⟨aa.val, ab.val, (N.absolute_pair _ _ _).mp first, (N.absolute_pair _ _ _).mp second,
      (N.absolute_pair _ _ _).mp pair⟩
  · rintro ⟨aa, ab, first, second, pair⟩
    let firstPair : N.Active := ⟨aa, active_transitive N.laws p.property ((pair aa).mpr (Or.inl rfl))⟩
    let secondPair : N.Active := ⟨ab, active_transitive N.laws p.property ((pair ab).mpr (Or.inr rfl))⟩
    exact ⟨firstPair, secondPair, (N.absolute_pair _ _ _).mpr first,
      (N.absolute_pair _ _ _).mpr second, (N.absolute_pair _ _ _).mpr pair⟩

theorem absolute_at (f a b : N.Active) :
    Internal.At N.localMem f a b ↔ Internal.At N.mem f.val a.val b.val := by
  constructor
  · rintro ⟨p, hp, code⟩
    exact ⟨p.val, hp, (N.absolute_orderedPair _ _ _).mp code⟩
  · rintro ⟨p, hp, code⟩
    let point : N.Active := ⟨p, active_transitive N.laws f.property hp⟩
    exact ⟨point, hp, (N.absolute_orderedPair a b point).mpr code⟩

theorem absolute_functionOn (f domain : N.Active) :
    Internal.FunctionOn N.localMem f domain ↔ Internal.FunctionOn N.mem f.val domain.val := by
  constructor
  · rintro ⟨values, shaped⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      let a : N.Active := ⟨x, active_transitive N.laws domain.property hx⟩
      obtain ⟨b, h, one⟩ := values a hx
      refine ⟨b.val, (N.absolute_at f a b).mp h, fun z hz => ?_⟩
      let c : N.Active := ⟨z, (N.active_graph_coordinates hz f.property).2⟩
      exact congrArg Subtype.val (one c ((N.absolute_at f a c).mpr hz))
    · intro p hp
      let v : N.Active := ⟨p, active_transitive N.laws f.property hp⟩
      obtain ⟨a, b, ha, pair⟩ := shaped v hp
      exact ⟨a.val, b.val, ha, (N.absolute_orderedPair _ _ _).mp pair⟩
  · rintro ⟨values, shaped⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, one⟩ := values x.val hx
      let value : N.Active := ⟨y, (N.active_graph_coordinates hy f.property).2⟩
      exact ⟨value, (N.absolute_at f x value).mpr hy,
        fun z hz => Subtype.ext (one z.val ((N.absolute_at f x z).mp hz))⟩
    · intro p hp
      obtain ⟨x, y, hx, code⟩ := shaped p.val hp
      have closed := N.orderedPair_coordinates code p.property
      exact ⟨⟨x, closed.1⟩, ⟨y, closed.2⟩, hx, (N.absolute_orderedPair _ _ _).mpr code⟩

theorem absolute_inductive (a : N.Active) :
    Internal.Inductive N.localMem a ↔ Internal.Inductive N.mem a.val := by
  constructor
  · rintro ⟨⟨zero, empty, contained⟩, closed⟩
    refine ⟨⟨zero.val, (N.absolute_empty zero).mp empty, contained⟩, fun x hx => ?_⟩
    let s : N.Active := ⟨x, active_transitive N.laws a.property hx⟩
    obtain ⟨y, step, hy⟩ := closed s hx
    exact ⟨y.val, (N.absolute_successor s y).mp step, hy⟩
  · rintro ⟨⟨zero, empty, contained⟩, closed⟩
    let z : N.Active := ⟨zero, active_transitive N.laws a.property contained⟩
    refine ⟨⟨z, (N.absolute_empty z).mpr empty, contained⟩, fun x hx => ?_⟩
    obtain ⟨y, step, hy⟩ := closed x.val hx
    let member : N.Active := ⟨y, active_transitive N.laws a.property hy⟩
    exact ⟨member, (N.absolute_successor x member).mpr step, hy⟩


theorem absolute_omega (a : N.Active) :
    Internal.Omega N.localMem a ↔ Internal.Omega N.mem a.val := by
  constructor
  · intro internal
    obtain ⟨w, wh, omega⟩ := N.active_omega_exists
    let member : N.Active := ⟨w, wh⟩
    have aw : N.Subset a.val w := (N.absolute_subset a member).mp
      (internal.2 member ((N.absolute_inductive member).mpr omega.1))
    have wa : N.Subset w a.val := omega.2 a.val ((N.absolute_inductive a).mp internal.1)
    exact (N.subset_antisymm aw wa).symm ▸ omega
  · exact fun h => ⟨(N.absolute_inductive a).mpr h.1, fun x ind y hy =>
      h.2 x.val ((N.absolute_inductive x).mp ind) y.val hy⟩

theorem fixes_omega (a : N.Active) (h : Internal.Omega N.mem a.val) : N.embedding a = a := by
  have description (a : N.Active) :
      SetFormula.holds N.localMem (SetFormula.omegaSet 0) 1 (fun _ => a) a ↔ Internal.Omega N.mem a.val :=
    (SetFormula.holds_omegaSet (E := N.localMem) (d := 1) (env := fun _ => a) (default := a)
      (by decide)).trans (N.absolute_omega a)
  have preserves := N.preserves_builder (SetFormula.omegaSet 0) 1 (SetFormula.scope_omega (by decide))
    (fun _ => a) a
  have omega := (description _).mp (preserves.mp ((description a).mpr h))
  exact Subtype.ext (N.omega_unique omega h)


theorem fixes_natural {w : V} (hw : Internal.Omega N.mem w) (active : N.square.activePoint w)
    (x : N.Active) (hx : N.mem x.val w) : N.embedding x = x := by
  have defn := Definable.atom (S := N.square) (n := 2) (M.constant .J)
    (i := 0) (j := 0) (by decide) (by decide)
  apply (N.fixed_iff_self_edge x).mpr
  apply N.omega_induction hw [] defn w _ _ x.val hx
  · exact (N.fixed_iff_self_edge ⟨N.empty, N.active_empty⟩).mp
      (N.fixes_empty ⟨N.empty, N.active_empty⟩ N.empty_mem)
  · intro z hz inductiveStep
    let a : N.Active := ⟨z, active_transitive N.laws active hz⟩
    let b : N.Active := ⟨N.succ z, N.active_succ a.property⟩
    have fixed := (N.fixed_iff_self_edge a).mpr inductiveStep
    have same := (N.preserves_successor a b).mp (N.mem_succ z)
    rw [fixed] at same
    exact (N.fixed_iff_self_edge b).mp (Subtype.ext ((N.internal_succ _ _).mp same))

end PalomarI3380.SquareRepresentation.NamedModel
