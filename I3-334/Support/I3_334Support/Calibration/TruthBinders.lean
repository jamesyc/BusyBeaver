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
theorem binderLayer_formula (laws : ClassAxioms E G) (inhabited : Nonempty V) {n w d i f e : Nat}
    (hw : w<n) (hd : d<n) (hi : i<n) (hf : f<n) (he : e<n)
    (universal : Bool) :
    (laws.context inhabited).square.Definable n (fun v => BinderLayer universal (laws.context inhabited) ⟨v w,v d,v w,v w⟩ (v i) (v f) (v e)) := by
  let N := laws.context inhabited
  have decode := arithmeticOn_definable (E := E) (G := G) (unaryInputDef (if universal then 6 else 7)).val
    (scope := n+1) (omega := w+1) (arg := ![i+1,0]) (by omega)
    (by intro j; fin_cases j <;> simp <;> omega)
  have decoded : N.square.Definable (n+1) _ := decode
  have update := arithmeticOn_definable (E := E) (G := G) pushInputDef.val
    (scope := n+3) (omega := w+3) (arg := ![0,1,e+3]) (by omega)
    (by intro j; fin_cases j <;> simp <;> omega)
  have encoded : N.square.Definable (n+3) _ := update
  have row := N.familyTruth_definable (n := n+3) (i := f+3) (j := 2) (k := 0)
    (by omega) (by omega) (by omega)
  have decode' : N.square.Definable (n+1) (fun v => arith (E := E) (G := G)
      (unaryInputDef (if universal then 6 else 7)).val (v (w+1)) ![v (i+1),v 0]) :=
    decoded.congr (fun v => by
      have values : (fun j => v ((![i+1,0] : Fin 2 → Nat) j)) =
          ![v (i+1),v 0] := by funext j; fin_cases j <;> rfl
      rw [values])
  have updated : N.square.Definable (n+3) (fun v => arith (E := E) (G := G)
      pushInputDef.val (v (w+3)) ![v 0,v 1,v (e+3)]) :=
    encoded.congr (fun v => by
      have values : (fun j => v ((![0,1,e+3] : Fin 3 → Nat) j)) =
          ![v 0,v 1,v (e+3)] := by funext j; fin_cases j <;> rfl
      rw [values])
  have body := Definable.ex (updated.and row)
  have member := Definable.mem (N := N) (n := n+2) (i := 0) (j := d+2) (by omega) (by omega)
  have mem : N.square.Definable (n+2) (fun v => E (v 0) (v (d+2))) :=
    member
  cases universal
  · exact Definable.ex (decode'.and (Definable.ex (mem.and body)))
  · exact Definable.ex (decode'.and (Definable.all (mem.implies body)))


end PalomarI3380.Calibration.CodedGraph
