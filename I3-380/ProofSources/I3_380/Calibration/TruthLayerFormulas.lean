module
public import I3_380.Calibration.TruthBinary
public import I3_380.Calibration.TruthBinders
import Mathlib.Tactic.FinCases
@[expose] public section

namespace PalomarI3380.Calibration.CodedGraph

open Logic Logic.Expanded SquareRepresentation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {V : Type} {E G : V → V → Prop}
variable {L : ClassAxioms E G} {inhabited : Nonempty V}

set_option maxHeartbeats 150000 in
theorem formulaLayer_formula (laws : ClassAxioms E G) (inhabited : Nonempty V) {n w d t u i f e : Nat}
    (hw : w<n) (hd : d<n) (ht : t<n) (hu : u<n) (hi : i<n) (hf : f<n) (he : e<n) :
    (laws.context inhabited).square.Definable n
      (fun v => FormulaLayer (laws.context inhabited) ⟨v w,v d,v t,v u⟩ (v i) (v f) (v e)) := by
  let N := laws.context inhabited
  have truth := arithmeticOn_definable (E := E) (G := G) truthInputDef.val hw
    (arg := ![i]) (by intro j; fin_cases j; exact hi)

  have atom := atomLayer_formula laws inhabited hw ht hu hi he
  have binary := binaryLayer_formula laws inhabited hw hi hf he
  have binder := binderLayer_formula laws inhabited hw hd hi hf he
  have top : N.square.Definable n (fun v => arith (E := E) (G := G) truthInputDef.val (v w) ![v i]) :=
    truth.congr (fun v => by
      have args : (fun j => v ((![i] : Fin 1 → Nat) j)) = ![v i] := by
        funext j
        have eq : j=0 := Subsingleton.elim _ _
        subst j
        rfl
      rw [args])
  exact top.or ((atom false).or ((atom true).or ((binary true).or ((binary false).or ((binder true).or (binder false))))))


end PalomarI3380.Calibration.CodedGraph
