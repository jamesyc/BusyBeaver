module
public import I3_334Support.SetTheory.Classes.ModelSyntax
@[expose] public section

namespace PalomarI3380.SquareRepresentation.Definable

open Logic SetContext

variable {A V : Type} {M : Algebra A} {N : SetContext M V}

theorem numeral (value : Nat) {n i : Nat} (hi : i < n) :
    N.square.Definable n (fun env => Internal.Numeral N.mem value (env i)) := by
  let level := n - (i + 1)
  have hl : level < n := by dsimp [level]; omega
  have result := of_levels (S := N.square) (body := SetFormula.numeral value level)
    (SetFormula.scope_numeral value hl) (p := fun env => Internal.Numeral N.mem value (env level))
    (fun _ _ => SetFormula.holds_numeral value hl)
  have index : n - (level + 1) = i := by dsimp [level]; omega
  simpa only [index] using result

theorem rowAt {n r i t a b : Nat} (hr : r < n) (hi : i < n) (ht : t < n) (ha : a < n) (hb : b < n) :
    N.square.Definable n (fun env => Internal.RowAt N.mem (env r) (env i) (env t) (env a) (env b)) := by
  have row := graphValue (N := N) (n := n + 2) (i := r + 2) (j := i + 2) (k := 1)
    (by omega) (by omega) (by omega)
  have tagged := orderedPair (N := N) (n := n + 2) (i := t + 2) (j := 0) (k := 1)
    (by omega) (by omega) (by omega)
  have args := orderedPair (N := N) (n := n + 2) (i := a + 2) (j := b + 2) (k := 0)
    (by omega) (by omega) (by omega)
  exact ex (ex (row.and (tagged.and args)))

theorem agreesAway {n a f g i : Nat} (ha : a < n) (hf : f < n) (hg : g < n) (hi : i < n) :
    N.square.Definable n (fun env => Internal.AgreesAway N.mem (env a) (env f) (env g) (env i)) := by
  have skip := (eq (S := N.square) (n := n + 1) (i := 0) (j := i + 1) (by omega) (by omega)).not
  have orig := graphValue (N := N) (n := n + 2) (i := f + 2) (j := 1) (k := 0)
    (by omega) (by omega) (by omega)
  have goal := graphValue (N := N) (n := n + 2) (i := g + 2) (j := 1) (k := 0)
    (by omega) (by omega) (by omega)
  exact boundedAll ha _ (skip.implies (all (orig.iff goal)))

theorem atomicTruth {R : V → V → V → Prop} (defn : Relation3 N R)
    {n p e a b : Nat} (hp : p < n) (he : e < n) (ha : a < n) (hb : b < n) :
    N.square.Definable n (fun env => Internal.AtomicTruth N.mem (R (env p)) (env e) (env a) (env b)) := by
  have x := graphValue (N := N) (n := n + 2) (i := e + 2) (j := a + 2) (k := 1)
    (by omega) (by omega) (by omega)
  have y := graphValue (N := N) (n := n + 2) (i := e + 2) (j := b + 2) (k := 0)
    (by omega) (by omega) (by omega)
  have rel := defn (n := n + 2) (i := p + 2) (j := 1) (k := 0) (by omega) (by omega) (by omega)
  exact ex (ex (x.and (y.and rel)))

theorem rowTruth {T : V → V → V → Prop} (defn : Relation3 N T)
    {n p a s e t x y : Nat} (hp : p < n) (ha : a < n) (hs : s < n) (he : e < n)
    (ht : t < n) (hx : x < n) (hy : y < n) :
    N.square.Definable n (fun env =>
      Internal.RowTruth N.mem (T (env p)) (env a) (env s) (env e) (env t) (env x) (env y)) := by
  have equal := atomicTruth (N := N) (R := fun (_ : V) x y => x = y) (fun _ h₁ h₂ => eq h₁ h₂) hp he hx hy
  have member := atomicTruth (N := N) (R := fun (_ : V) => N.mem) (membership_relation (N := N)) hp he hx hy
  have aTruth := defn hp hx he
  have bTruth := defn hp hy he
  have amends := functionInto (N := N) (n := n + 1) (i := 0) (j := a + 1) (k := s + 1)
    (by omega) (by omega) (by omega)
  have agrees := agreesAway (N := N) (n := n + 1) (a := a + 1) (f := e + 1) (g := 0) (i := x + 1)
    (by omega) (by omega) (by omega) (by omega)
  have succeeds := defn (n := n + 1) (i := p + 1) (j := y + 1) (k := 0)
    (by omega) (by omega) (by omega)
  exact ((numeral 0 ht).and equal).or (((numeral 1 ht).and member).or
    (((numeral 2 ht).and aTruth.not).or (((numeral 3 ht).and (aTruth.and bTruth)).or
      ((numeral 4 ht).and (ex (amends.and (agrees.and succeeds)))))))

end PalomarI3380.SquareRepresentation.Definable
