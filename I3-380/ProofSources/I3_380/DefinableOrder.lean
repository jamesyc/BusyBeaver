module
public import I3_380.SetGraphs
@[expose] public section

namespace PalomarI3380.SquareRepresentation

open Logic

variable {A V : Type} {M : Algebra A} {N : SetContext M V}

namespace Definable

/-- A ternary relation available with any index assignment. In an order
formula the first argument carries the parameter defining the relation. -/
def Relation3 (N : SetContext M V) (R : V → V → V → Prop) : Prop :=
  ∀ {n i j k : Nat}, i < n → j < n → k < n →
    N.square.Definable n (fun env => R (env i) (env j) (env k))

theorem membership_relation : Relation3 N (fun (_ : V) x y => N.mem x y) :=
  fun _ h₁ h₂ => mem h₁ h₂

theorem graph_relation : Relation3 N (Internal.At N.mem) :=
  fun h₁ h₂ h₃ => graphValue h₁ h₂ h₃

variable {R : V → V → V → Prop} {n i j k : Nat}

theorem least (D : Relation3 N R) (hi : i < n) (hj : j < n) (hk : k < n) :
    N.square.Definable n (fun env => N.Least (R (env i)) (env j) (env k)) :=
  (mem hk hj).and
    (boundedAll hj _ ((eq (i := k + 1) (j := 0) (by omega) (by omega)).or
      (D (i := i + 1) (j := k + 1) (k := 0) (by omega) (by omega) (by omega))))

theorem wellOrder (D : Relation3 N R) (hi : i < n) (hj : j < n) :
    N.square.Definable n (fun env => N.WellOrderOn (R (env i)) (env j)) := by
  let irreflexive := fun (s : Nat → V) => ∀ x, N.mem x (s j) → ¬R (s i) x x
  let transitive := fun (s : Nat → V) => ∀ x, N.mem x (s j) → ∀ y, N.mem y (s j) →
    ∀ z, N.mem z (s j) → R (s i) x y → R (s i) y z → R (s i) x z
  let comparison := fun (s : Nat → V) => ∀ x, N.mem x (s j) → ∀ y, N.mem y (s j) →
    R (s i) x y ∨ x = y ∨ R (s i) y x
  let minimization := fun (s : Nat → V) => ∀ b, N.Subset b (s j) → N.NonemptySet b →
    ∃ x, N.Least (R (s i)) b x
  have hirr : N.square.Definable n irreflexive :=
    boundedAll hj _ (not (D (i := i + 1) (j := 0) (k := 0) (by omega) (by omega) (by omega)))
  have htrans : N.square.Definable n transitive :=
    boundedAll hj _ (boundedAll (i := j + 1) (by omega) _
      (boundedAll (i := j + 2) (by omega) _
        ((D (i := i + 3) (j := 2) (k := 1) (by omega) (by omega) (by omega)).implies
          ((D (i := i + 3) (j := 1) (k := 0) (by omega) (by omega) (by omega)).implies
            (D (i := i + 3) (j := 2) (k := 0) (by omega) (by omega) (by omega))))))
  have hcmp : N.square.Definable n comparison :=
    boundedAll hj _ (boundedAll (i := j + 1) (by omega) _
      ((D (i := i + 2) (j := 1) (k := 0) (by omega) (by omega) (by omega)).or
        ((eq (i := 1) (j := 0) (by omega) (by omega)).or
          (D (i := i + 2) (j := 0) (k := 1) (by omega) (by omega) (by omega)))))
  have hleast : N.square.Definable n minimization :=
    all ((subset (i := 0) (j := j + 1) (by omega) (by omega)).implies
      ((nonempty (i := 0) (by omega)).implies (ex
        (least D (i := i + 2) (j := 1) (k := 0) (by omega) (by omega) (by omega)))))
  refine (hirr.and (htrans.and (hcmp.and hleast))).congr fun s => ?_
  exact ⟨fun ⟨a, b, c, d⟩ => ⟨a, fun x y z hx hy hz => b x hx y hy z hz,
    fun x y hx hy => c x hx y hy, d⟩,
    fun h => ⟨h.irrefl, fun x hx y hy z hz => h.trans x y z hx hy hz,
      fun x hx y hy => h.compare x y hx hy, h.least⟩⟩

theorem ordinal (hi : i < n) :
    N.square.Definable n (fun env => N.Ordinal (env i)) := by
  have ht : N.square.Definable n (fun env => ∀ x, N.mem x (env i) → N.Transitive x) :=
    boundedAll hi _ (transitive (i := 0) (by omega))
  refine ((transitive hi).and (ht.and (wellOrder (R := fun (_ : V) => N.mem) (membership_relation (N := N)) hi hi))).congr fun _ => ?_
  exact ⟨fun ⟨h, h', h''⟩ => ⟨h, h', h''⟩, fun h => ⟨h.transitive, h.members_transitive, h.ordered⟩⟩

theorem functionOn (hi : i < n) (hj : j < n) :
    N.square.Definable n (fun env => Internal.FunctionOn N.mem (env i) (env j)) := by
  let body := SetFormula.functionOn (n - (i + 1)) (n - (j + 1))
  have h₁ : n - (i + 1) < n := by omega
  have h₂ : n - (j + 1) < n := by omega
  have result := of_levels (S := N.square) (body := body) (SetFormula.scope_functionOn h₁ h₂)
    (p := fun env => Internal.FunctionOn N.mem (env (n - (i + 1))) (env (n - (j + 1))))
    (fun env default => SetFormula.holds_functionOn h₁ h₂)
  simpa only [show n - (n - (i + 1) + 1) = i by omega, show n - (n - (j + 1) + 1) = j by omega]
    using result

theorem functionInto (hi : i < n) (hj : j < n) (hk : k < n) :
    N.square.Definable n (fun env => Internal.FunctionOn N.mem (env i) (env j) ∧
      ∀ x, N.mem x (env j) → ∀ y, Internal.At N.mem (env i) x y → N.mem y (env k)) :=
  (functionOn hi hj).and (boundedAll hj _ (all
    ((graphValue (i := i + 2) (j := 1) (k := 0) (by omega) (by omega) (by omega)).implies
      (mem (i := 0) (j := k + 2) (by omega) (by omega)))))

end Definable
end PalomarI3380.SquareRepresentation
