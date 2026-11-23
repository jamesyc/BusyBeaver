module
public import I3_334Support.Calibration.TruthLayer
import Mathlib.Tactic.FinCases
@[expose] public section

namespace PalomarI3380.Calibration.CodedGraph

open Logic Logic.Expanded SquareRepresentation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {V : Type} {E G : V → V → Prop}
variable {L : ClassAxioms E G} {inhabited : Nonempty V}

set_option maxHeartbeats 65000 in
theorem binaryLayer_formula (laws : ClassAxioms E G) (inhabited : Nonempty V) {n w i f e : Nat}
    (hw : w<n) (hi : i<n) (hf : f<n) (he : e<n)
    (conjunctive : Bool) :
    (laws.context inhabited).square.Definable n (fun v => BinaryLayer conjunctive (laws.context inhabited) ⟨v w,v w,v w,v w⟩ (v i) (v f) (v e)) := by
  let N := laws.context inhabited
  have decode := arithmeticOn_definable (E := E) (G := G) (binaryInputDef (if conjunctive then 4 else 5)).val
    (scope := n+2) (omega := w+2) (arg := ![i+2,1,0]) (by omega)
    (by intro j; fin_cases j <;> simp <;> omega)
  have decoded : N.square.Definable (n+2) _ := decode
  have left := N.familyTruth_definable (n := n+2) (i := f+2) (j := 1) (k := e+2)
    (by omega) (by omega) (by omega)
  have right := N.familyTruth_definable (n := n+2) (i := f+2) (j := 0) (k := e+2)
    (by omega) (by omega) (by omega)
  have decode' : N.square.Definable (n+2) (fun v => arith (E := E) (G := G)
      (binaryInputDef (if conjunctive then 4 else 5)).val (v (w+2)) ![v (i+2),v 1,v 0]) :=
    decoded.congr (fun v => by
      have values : (fun j => v ((![i+2,1,0] : Fin 3 → Nat) j)) =
          ![v (i+2),v 1,v 0] := by funext j; fin_cases j <;> rfl
      rw [values])
  cases conjunctive
  · exact (Definable.ex (Definable.ex (decode'.and (left.or right)))).congr (fun _ => Iff.rfl)
  · exact (Definable.ex (Definable.ex (decode'.and (left.and right)))).congr (fun _ => Iff.rfl)


end PalomarI3380.Calibration.CodedGraph
