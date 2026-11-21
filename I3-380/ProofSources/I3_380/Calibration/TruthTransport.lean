module
public import I3_380.Calibration.TruthClauses
import Mathlib.Tactic.FinCases
@[expose] public section

namespace PalomarI3380.Calibration.CodedGraph

open Logic Logic.Expanded SquareRepresentation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type} {E G : V → V → Prop} {L : ClassAxioms E G} {inhabited : Nonempty V}
variable (D : OmegaDomain L inhabited) {P : Presentation D} (T : TruthTable D P)

/-- The arithmetic guard describes a syntactic transformation and the
corresponding assignment change. The truth table is a set parameter. -/
def TruthTable.AgreesAt (guard : Semisentence ℒₒᵣ 5) (p : D.Points) : Prop :=
  ∀ q original modified : D.Points, guard.Evalb ![p,q,original,modified,P.fallback] →
    (T.holds D p original ↔ T.holds D q modified)

theorem transport_definable (guard : Semisentence ℒₒᵣ 5) :
    ∃ pred : (Nat → V) → Prop, (context D).square.Definable 5 pred ∧
      ∀ p : D.Points, pred (parameterEnv [D.omega,T.family,P.fallback.val] p.val D.omega) ↔
        T.AgreesAt D guard p := by
  let N := context D
  have raw := arithmeticOn_definable (E := E) (G := G) guard (scope := 8) (omega := 5)
    (arg := ![3,2,1,0,7]) (by decide) (by intro i; fin_cases i <;> decide)
  have typed : N.square.Definable 8
      (fun v => arith (E := E) (G := G) guard (v 5) ![v 3,v 2,v 1,v 0,v 7]) :=
    raw.congr (fun v => by
      have eq : (fun i => v ((![3,2,1,0,7] : Fin 5 → Nat) i)) =
          ![v 3,v 2,v 1,v 0,v 7] := by funext i; fin_cases i <;> rfl
      rw [eq])
  have before := N.familyTruth_definable (n := 8) (i := 6) (j := 3) (k := 1) (by decide) (by decide) (by decide)
  have after := N.familyTruth_definable (n := 8) (i := 6) (j := 2) (k := 0) (by decide) (by decide) (by decide)
  have finished := Definable.all (Definable.all (Definable.all (typed.implies (before.iff after))))
  refine ⟨_,finished,fun p => ?_⟩
  change (∀ q original modified : V,
    arith (E := E) (G := G) guard D.omega ![p.val,q,original,modified,P.fallback.val] →
      (N.FamilyTruth T.family p.val original ↔ N.FamilyTruth T.family q modified)) ↔ _
  constructor
  · intro h q a b checked
    exact h q.val a.val b.val (by
      have uses := (arith_args D guard ![p,q,a,b,P.fallback]).mpr checked
      simpa only [pointValues_cons,pointValues_nil] using uses)
  · intro h q a b checked
    obtain ⟨points,same,proof⟩ := (arithmeticOn_eval D guard _).mp checked
    have first : points 0=p := Subtype.ext (same 0)
    have last : points 4=P.fallback := Subtype.ext (same 4)
    have vector : points = ![p,points 1,points 2,points 3,P.fallback] := by
      funext i
      fin_cases i <;> simp [first,last]
    rw [vector] at proof
    have result := h (points 1) (points 2) (points 3) proof
    change N.FamilyTruth T.family p.val (points 2).val ↔ N.FamilyTruth T.family (points 1).val (points 3).val at result
    rwa [same 1,same 2,same 3] at result

theorem TruthTable.transport_induction (guard : Semisentence ℒₒᵣ 5)
    (step : ∀ p : D.Points, (∀ q : D.Points, q<p → T.AgreesAt D guard q) → T.AgreesAt D guard p) :
    ∀ p : D.Points, T.AgreesAt D guard p := by
  obtain ⟨_,formula,meaning⟩ := transport_definable D T guard
  exact D.setOrderInduction [D.omega,T.family,P.fallback.val] D.omega _ formula meaning step

end PalomarI3380.Calibration.CodedGraph
