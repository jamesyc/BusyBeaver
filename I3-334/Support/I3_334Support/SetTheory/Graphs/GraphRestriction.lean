module
public import I3_334Support.SetTheory.Order.DefinableOrder
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Logic

variable {A V : Type} {M : Algebra A}

namespace SetContext

variable (N : SetContext M V)

def Restricts (original domain result : V) : Prop :=
  ∀ p, N.mem p result ↔ N.mem p original ∧
    ∃ x, N.mem x domain ∧ ∃ y, Internal.OrderedPair N.mem x y p

theorem restriction_exists (original domain : V) :
    ∃ result, N.Restricts original domain result :=
  N.separate [] (Definable.boundedEx (S := N.square) (n := 2) (i := 1) (by decide) _
    (Definable.ex (Definable.orderedPair (N := N) (n := 4) (i := 1) (j := 0) (k := 2)
      (by decide) (by decide) (by decide)))) original domain

noncomputable def restrictGraph (original domain : V) : V :=
  Classical.choose (N.restriction_exists original domain)

theorem restricts_canonical (original domain : V) : N.Restricts original domain (N.restrictGraph original domain) :=
  Classical.choose_spec (N.restriction_exists original domain)

theorem restricts_unique {original domain a b : V} (ha : N.Restricts original domain a)
    (hb : N.Restricts original domain b) : a = b :=
  N.ext a b fun p => (ha p).trans (hb p).symm

theorem restricts_value {f domain g x y : V} (restriction : N.Restricts f domain g) :
    Internal.At N.mem g x y ↔ N.mem x domain ∧ Internal.At N.mem f x y := by
  rw [N.at_pair, restriction, N.at_pair]
  constructor
  · rintro ⟨member, a, ha, b, pair⟩
    have ⟨same, _⟩ := Internal.orderedPair_injective pair (N.orderedPair_intro x y)
    exact ⟨same ▸ ha, member⟩
  · rintro ⟨hx, hv⟩
    exact ⟨hv, x, hx, y, N.orderedPair_intro x y⟩

theorem restricts_function {f domain cut g : V} (hf : Internal.FunctionOn N.mem f domain)
    (sub : N.Subset cut domain) (restriction : N.Restricts f cut g) :
    Internal.FunctionOn N.mem g cut := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, unique⟩ := hf.1 x (sub x hx)
    exact ⟨y, (N.restricts_value restriction).mpr ⟨hx, hy⟩, fun z hz =>
      unique z ((N.restricts_value restriction).mp hz).2⟩
  · intro p hp
    obtain ⟨_, x, hx, y, pair⟩ := (restriction p).mp hp
    exact ⟨x, y, hx, pair⟩

theorem restricts_nested {f a b g h : V} (sub : N.Subset b a)
    (first : N.Restricts f a g) (second : N.Restricts g b h) :
    N.Restricts f b h := by
  intro p
  rw [second, first]
  constructor
  · rintro ⟨⟨orig, _⟩, parts⟩
    exact ⟨orig, parts⟩
  · rintro ⟨orig, x, hx, y, pxy⟩
    exact ⟨⟨orig, x, sub x hx, y, pxy⟩, x, hx, y, pxy⟩

theorem restricts_identical {f g dom : V} (hf : Internal.FunctionOn N.mem f dom)
    (restriction : N.Restricts f dom g) : f = g := by
  apply N.ext
  intro p
  refine ⟨fun h => (restriction p).mpr ?_, fun h => ((restriction p).mp h).1⟩
  obtain ⟨x, y, hx, pair⟩ := hf.2 p h
  exact ⟨h, x, hx, y, pair⟩

end SetContext

namespace Definable

variable {N : SetContext M V} {n i j k : Nat}

theorem restricts (hi : i < n) (hj : j < n) (hk : k < n) :
    N.square.Definable n (fun s => N.Restricts (s i) (s j) (s k)) :=
  all (iff (mem (i := 0) (j := k + 1) (by omega) (by omega))
    ((mem (i := 0) (j := i + 1) (by omega) (by omega)).and
      (boundedEx (i := j + 1) (by omega) _
        (ex (orderedPair (i := 1) (j := 0) (k := 2) (by omega) (by omega) (by omega))))))

end Definable
end PalomarI3380.SquareRepresentation
