module
public import I3_380.Calibration.TruthClauses
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Functions
import Mathlib.Tactic.FinCases
@[expose] public section

namespace PalomarI3380.Calibration.CodedGraph

open Logic Logic.Expanded SquareRepresentation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type} {E G : V → V → Prop} {L : ClassAxioms E G} {inhabited : Nonempty V}
variable (D : OmegaDomain L inhabited) {P : Presentation D} (T : TruthTable D P)

def TruthTable.NegationAt (p : D.Points) : Prop :=
  IsUFormula GraphLanguage p →
    ∀ env : D.Points, T.holds D (Bootstrapping.neg GraphLanguage p) env ↔ ¬T.holds D p env

theorem setNegation_definable :
    ∃ pred : (Nat → V) → Prop, (context D).square.Definable 4 pred ∧
      ∀ p : D.Points, pred (parameterEnv [D.omega,T.family] p.val D.omega) ↔ T.NegationAt D p := by
  let N := context D
  let valid := (isUFormula GraphLanguage).sigma.val
  let graph := (negGraph GraphLanguage).val
  have wellFormed := arithmeticOn_definable (E := E) (G := G) valid
    (scope := 4) (omega := 2) (arg := ![0]) (by decide) (by intro i; fin_cases i; decide)
  have negated :=
    arithmeticOn_definable (E := E) (G := G) graph (scope := 6) (omega := 4) (arg := ![0,2])
      (by decide) (by intro i; fin_cases i <;> decide)
  simp only [Matrix.comp_vecCons',Matrix.empty_eq] at wellFormed negated
  have pos := N.familyTruth_definable (n := 6) (i := 5) (j := 2) (k := 1)
    (by decide) (by decide) (by decide)
  have negative := N.familyTruth_definable (n := 6) (i := 5) (j := 0) (k := 1)
    (by decide) (by decide) (by decide)
  have check := Definable.all (Definable.implies (S := N.square) negated (negative.iff pos.not))
  have formula := Definable.implies (S := N.square) wellFormed (Definable.boundedAll (i := 2) (by decide) _ check)
  refine ⟨_,formula,fun p => ?_⟩
  have valid' :
      arith (E := E) (G := G) valid D.omega ![p.val] ↔ IsUFormula GraphLanguage p := by
    have meaning := arith_args D valid ![p]
    have checked : valid.Evalb ![p] ↔ IsUFormula GraphLanguage p := by
      change (isUFormula GraphLanguage).sigma.val.Evalb ![p] ↔ _
      rw [Bounding.HierarchySymbol.Semiformula.val_sigma]
      exact IsUFormula.defined.iff
    exact (by simpa only [pointValues_cons,pointValues_nil] using meaning.trans checked)
  have relation (q : D.Points) :
      arith (E := E) (G := G) graph D.omega ![q.val,p.val] ↔ q=Bootstrapping.neg GraphLanguage p := by
    have meaning := arith_args D graph ![q,p]
    have checked : graph.Evalb ![q,p] ↔ q=Bootstrapping.neg GraphLanguage p := neg.defined.iff
    exact (by simpa only [pointValues_cons,pointValues_nil] using meaning.trans checked)
  change (arith (E := E) (G := G) valid D.omega ![p.val] →
    ∀ env, E env D.omega → ∀ q, arith (E := E) (G := G) graph D.omega ![q,p.val] →
      (N.FamilyTruth T.family q env ↔ ¬N.FamilyTruth T.family p.val env)) ↔ _
  rw [valid']
  apply imp_congr_right
  intro _
  constructor
  · intro h env
    exact h env.val env.property _ ((relation _).mpr rfl)
  · intro h env natural q code
    let e : D.Points := ⟨env,natural⟩
    obtain ⟨points,rep,_⟩ := (arithmeticOn_eval D graph _).mp code
    have eq : (points 0).val=q := rep 0
    have same := (relation _).mp (eq.symm ▸ code)
    simpa only [TruthTable.holds,← eq,same] using h e

theorem TruthTable.holds_negation (p : D.Points) (valid : IsUFormula GraphLanguage p) (env : D.Points) :
    T.holds D (Bootstrapping.neg GraphLanguage p) env ↔ ¬T.holds D p env := by
  obtain ⟨predicate,described,meaning⟩ := setNegation_definable D T
  have induction := D.setOrderInduction [D.omega,T.family] D.omega (T.NegationAt D)
    described meaning (fun p ih => by
      intro checked e
      rcases checked.case with ⟨k,r,v,symbol,terms,rfl⟩ | ⟨k,r,v,symbol,terms,rfl⟩ |
        rfl | rfl | ⟨a,b,ha,hb,rfl⟩ | ⟨a,b,ha,hb,rfl⟩ | ⟨a,ha,rfl⟩ | ⟨a,ha,rfl⟩
      · rw [neg_rel symbol terms,T.holds_nrel,T.holds_rel]
      · rw [neg_nrel symbol terms,T.holds_rel,T.holds_nrel,not_not]
      · simp only [neg_verum,T.holds_true,T.holds_false,not_true_eq_false,iff_false]
      · simp [neg_falsum,T.holds_true,T.holds_false]
      · rw [neg_and ha hb,T.holds_or,T.holds_and,
          ih a (show a<a ^⋏ b from by simp) ha e,ih b (show b<a ^⋏ b from by simp) hb e]
        exact not_and_or.symm
      · rw [neg_or ha hb,T.holds_and,T.holds_or,
          ih a (show a<a ^⋎ b from by simp) ha e,ih b (show b<a ^⋎ b from by simp) hb e]
        exact not_or.symm
      · rw [neg_all ha,T.holds_exs,T.holds_all,not_forall]
        exact exists_congr fun x => ih a (show a < ^∀ a from by simp) ha (pushBound x.val e)
      · rw [neg_ex ha,T.holds_all,T.holds_exs,not_exists]
        exact forall_congr' fun x => ih a (show a < ^∃ a from by simp) ha (pushBound x.val e))
  exact induction p valid env

end PalomarI3380.Calibration.CodedGraph
