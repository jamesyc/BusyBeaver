module
public import I3_334Support.SetTheory.Order.OrderType
@[expose] public section

namespace PalomarI3380.SquareRepresentation.Definable

open Logic

variable {A V : Type} {M : Algebra A} {N : SetContext M V}

theorem orderType {R : V → V → V → Prop} (definition : Relation3 N R)
    {n i j k : Nat} (hi : i < n) (hj : j < n) (hk : k < n) :
    N.square.Definable n (fun s => N.OrderType (R (s i)) (s j) (s k)) := by
  have rightType := ordinal (N := N) hk
  have isFunction := functionOn (N := N) (n := n + 1) (i := 0) (j := j + 1) (by omega) (by omega)
  have isOnto := range (N := N) (n := n + 1) (i := 0) (j := k + 1) (by omega) (by omega)
  have firstValue := graphValue (N := N) (n := n + 5) (i := 4) (j := 3) (k := 1)
    (by omega) (by omega) (by omega)
  have secondValue := graphValue (N := N) (n := n + 5) (i := 4) (j := 2) (k := 0)
    (by omega) (by omega) (by omega)
  have original := definition (n := n + 5) (i := i + 5) (j := 3) (k := 2)
    (by omega) (by omega) (by omega)
  have image := mem (N := N) (n := n + 5) (i := 1) (j := 0) (by omega) (by omega)
  have preserves := all (all (all (all (firstValue.implies (secondValue.implies (original.iff image))))))
  refine (rightType.and (ex (isFunction.and (isOnto.and preserves)))).congr fun s => ?_
  exact ⟨fun ⟨ordinal, f, hf, ran, exactness⟩ => ⟨f, ordinal, hf, ran, exactness⟩,
    fun ⟨f, spec⟩ => ⟨spec.ordinal, f, spec.functionOn, spec.onto, spec.order⟩⟩

end PalomarI3380.SquareRepresentation.Definable
