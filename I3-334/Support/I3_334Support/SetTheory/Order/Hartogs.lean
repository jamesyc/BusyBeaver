module
public import I3_334Support.SetTheory.Order.OrdinalInjection
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic

variable {A V : Type} {M : Algebra A} (N : SetContext M V)

/-- The internal Hartogs argument uses the set of relation codes
bounded by powersets. It needs neither Infinity nor Foundation. -/
theorem hartogs (X : V) : ∃ ordinal, N.Ordinal ordinal ∧ ¬N.Injects ordinal X := by
  let bound := N.union₂ (N.power X) (N.power (N.power (N.power X)))
  let catalogue := N.power (N.power bound)
  let predicate := fun s : Nat → V =>
    ∃ a r, Internal.OrderedPair N.mem a r (s 0) ∧
      N.WellOrderOn (Internal.At N.mem r) a ∧ N.OrderType (Internal.At N.mem r) a (s 1)
  have definition : N.square.Definable 2 predicate := by
    have p := Definable.orderedPair (N := N) (n := 4) (i := 1) (j := 0) (k := 2)
      (by decide) (by decide) (by decide)
    have w := Definable.wellOrder (N := N) (R := Internal.At N.mem) (Definable.graph_relation (N := N))
      (n := 4) (i := 0) (j := 1) (by decide) (by decide)
    have t := Definable.orderType (N := N) (R := Internal.At N.mem) (Definable.graph_relation (N := N))
      (n := 4) (i := 0) (j := 1) (k := 3) (by decide) (by decide) (by decide)
    exact Definable.ex (Definable.ex (p.and (w.and t)))
  have one (code x y : V) : predicate (parameterEnv [] code x) → predicate (parameterEnv [] code y) → x = y := by
    rintro ⟨a, r, ha, w, hx⟩ ⟨b, s, hb, _, hy⟩
    obtain ⟨rfl, rfl⟩ := Internal.orderedPair_injective ha hb
    exact N.orderType_unique a r (Definable.graph_relation (N := N)) w hx hy
  obtain ⟨types, covers⟩ := N.image [] definition one catalogue
  have ordinals : ∀ x, N.mem x types → N.Ordinal x := by
    intro x hx
    obtain ⟨p, _, a, r, _, _, iso, h⟩ := (covers x).mp hx
    exact h.ordinal
  let sup := N.union types
  have supOrd : N.Ordinal sup := N.ordinal_union types ordinals
  refine ⟨N.succ sup, N.ordinal_succ supOrd, ?_⟩
  rintro ⟨f, injection⟩
  obtain ⟨r, small, ordered, typ⟩ := N.ordinal_order_image (N.ordinal_succ supOrd) injection
  have rangeSubset : N.Subset (N.range f) X := by
    intro y hy
    obtain ⟨x, h⟩ := (N.mem_range f y).mp hy
    exact injection.into x y h
  have first : N.mem (N.range f) bound := (N.mem_union₂ _ _ _).mpr
    (Or.inl ((N.mem_power _ _).mpr rangeSubset))
  have second : N.mem r bound := (N.mem_union₂ _ _ _).mpr (Or.inr ((N.mem_power _ _).mpr small))
  have above : N.mem (N.succ sup) types := (covers _).mpr
    ⟨N.orderedPair (N.range f) r, N.orderedPair_bound first second,
      N.range f, r, N.orderedPair_intro _ _, ordered, typ⟩
  exact supOrd.not_mem_self N ((N.mem_union _ _).mpr ⟨N.succ sup, above, (N.mem_succ _ _).mpr (Or.inr rfl)⟩)

end PalomarI3380.SquareRepresentation.SetContext
