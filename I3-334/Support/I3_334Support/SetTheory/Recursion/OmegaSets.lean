module
public import I3_334Support.SetTheory.Rank.RankRelations
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Logic
variable {A V : Type} {M : Algebra A}

namespace Definable

variable {N : SetContext M V}

theorem inductiveSet {n i : Nat} (hi : i < n) :
    N.square.Definable n (fun s => Internal.Inductive N.mem (s i)) := by
  let j := n - (i + 1)
  have hj : j < n := by dsimp [j]; omega
  have result := of_levels (S := N.square) (body := SetFormula.inductiveSet j)
    (SetFormula.scope_inductiveSet hj) (p := fun env => Internal.Inductive N.mem (env j))
    (fun _ _ => SetFormula.holds_inductiveSet hj)
  have index : n - (j + 1) = i := by dsimp [j]; omega
  simpa only [index] using result

end Definable


namespace SetContext

variable (N : SetContext M V)

theorem omega_unique {w z : V} (hw : Internal.Omega N.mem w) (hz : Internal.Omega N.mem z) : w = z :=
  N.subset_antisymm (hw.2 z hz.1) (hz.2 w hw.1)

theorem omega_zero {w : V} (omega : Internal.Omega N.mem w) : N.mem N.empty w :=
  by
    obtain ⟨z,empty,has⟩ := omega.1.1
    exact ((N.empty_unique _).mp empty) ▸ has

theorem omega_succ {w x : V} (omega : Internal.Omega N.mem w) (hx : N.mem x w) :
    N.mem (N.succ x) w := by
  obtain ⟨y, step, contained⟩ := omega.1.2 x hx
  exact ((N.internal_succ x y).mp step) ▸ contained

/-- The expanded membership model supports induction on its own naturals,
including predicates that use the embedding graph. -/
theorem omega_induction {w : V} (hw : Internal.Omega N.mem w) (params : List V) {P : (Nat → V) → Prop}
    (definable : N.square.Definable (params.length + 2) P) (anchor : V)
    (zero : P (parameterEnv params N.empty anchor))
    (next : ∀ x, N.mem x w → P (parameterEnv params x anchor) → P (parameterEnv params (N.succ x) anchor)) :
    ∀ x, N.mem x w → P (parameterEnv params x anchor) := by
  obtain ⟨cut, spec⟩ := N.separate params definable w anchor
  have hasZero : N.mem N.empty w := by
    obtain ⟨z, hz, contained⟩ := hw.1.1
    exact ((N.empty_unique z).mp hz) ▸ contained
  have closed (x : V) (hx : N.mem x w) : N.mem (N.succ x) w := by
    obtain ⟨y, succ, inside⟩ := hw.1.2 x hx
    exact ((N.internal_succ x y).mp succ) ▸ inside
  have inductiveSet : Internal.Inductive N.mem cut :=
    ⟨⟨N.empty, N.empty_mem, (spec _).mpr ⟨hasZero, zero⟩⟩, fun x hx => by
      have h := (spec x).mp hx
      exact ⟨N.succ x, N.mem_succ x, (spec _).mpr ⟨closed x h.1, next x h.1 h.2⟩⟩⟩
  exact fun x hx => ((spec x).mp (hw.2 cut inductiveSet x hx)).2

theorem omega_ordinal {w : V} (hw : Internal.Omega N.mem w) : N.Ordinal w := by
  have definable := (Definable.ordinal (N := N) (n := 2) (i := 0) (by decide)).and
    (Definable.subset (N := N) (n := 2) (i := 0) (j := 1) (by decide) (by decide))
  have all := N.omega_induction hw [] definable w ⟨N.ordinal_empty, fun x hx => (N.empty_mem x hx).elim⟩
    (fun x hx prev => ⟨N.ordinal_succ prev.1, fun y hy =>
      ((N.mem_succ x y).mp hy).elim (prev.2 y) (fun same => same.symm ▸ hx)⟩)
  exact N.ordinal_of_transitive_members (fun x hx => (all x hx).2) (fun x hx => (all x hx).1)


end SetContext
end PalomarI3380.SquareRepresentation
