module
public import I3_380.GraphRestriction
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Logic

variable {A V : Type} {M : Algebra A}

namespace SetContext

variable (N : SetContext M V)

/-- Two powersets of a common cover bound all pair codes with both
coordinates in the cover. -/
theorem orderedPair_bound {a b cover : V} (ha : N.mem a cover) (hb : N.mem b cover) :
    N.mem (N.orderedPair a b) (N.power (N.power cover)) := by
  apply (N.mem_power _ _).mpr
  intro u hu
  rcases (N.mem_pair _ _ _).mp hu with rfl | rfl <;>
    apply (N.mem_power _ _).mpr
  · intro x hx
    exact ((N.mem_singleton _ _).mp hx).symm ▸ ha
  · intro x hx
    rcases (N.mem_pair _ _ _).mp hx with rfl | rfl
    · exact ha
    · exact hb

def IsRange (graph set : V) : Prop :=
  ∀ y, N.mem y set ↔ ∃ x, Internal.At N.mem graph x y

theorem range_exists (graph : V) : ∃ set, N.IsRange graph set := by
  let pred := fun s : Nat → V => ∃ x, Internal.OrderedPair N.mem x (s 1) (s 0)
  have describable : N.square.Definable 2 pred :=
    Definable.ex (Definable.orderedPair (N := N) (n := 3) (i := 0) (j := 2) (k := 1)
      (by decide) (by decide) (by decide))
  have functional (p x y : V) : pred (parameterEnv [] p x) → pred (parameterEnv [] p y) → x = y := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    exact (Internal.orderedPair_injective ha hb).2
  obtain ⟨set, meaning⟩ := N.image [] describable functional graph
  refine ⟨set, fun y => (meaning y).trans ?_⟩
  constructor
  · rintro ⟨p, hp, x, pair⟩
    exact ⟨x, p, hp, pair⟩
  · rintro ⟨x, p, hp, pair⟩
    exact ⟨p, hp, x, pair⟩

noncomputable def range (graph : V) : V := Classical.choose (N.range_exists graph)

theorem mem_range (graph y : V) : N.mem y (N.range graph) ↔ ∃ x, Internal.At N.mem graph x y :=
  Classical.choose_spec (N.range_exists graph) y

theorem range_unique {graph a b : V} (ha : N.IsRange graph a) (hb : N.IsRange graph b) : a = b :=
  N.ext a b fun y => (ha y).trans (hb y).symm

end SetContext

namespace Definable

variable {N : SetContext M V} {n i j : Nat}

theorem range (hi : i < n) (hj : j < n) :
    N.square.Definable n (fun env => N.IsRange (env i) (env j)) :=
  all (iff (mem (i := 0) (j := j + 1) (by omega) (by omega))
    (ex (graphValue (i := i + 2) (j := 0) (k := 1) (by omega) (by omega) (by omega))))

theorem powerset (hi : i < n) (hj : j < n) :
    N.square.Definable n (fun env => ∀ x, N.mem x (env j) ↔ N.Subset x (env i)) :=
  all (iff (mem (i := 0) (j := j + 1) (by omega) (by omega))
    (subset (i := 0) (j := i + 1) (by omega) (by omega)))

end Definable
end PalomarI3380.SquareRepresentation
