module
public import I3_334Support.Calibration.FilterTheory
public import I3_334Support.RelationAlgebra.Witness
@[expose] public section

namespace PalomarI3380.Calibration

open FFL FFL.FirstOrder Manifest RelationLaws SquareRepresentation
open Term

def supportTerm {V : Type} (r : Term V) : Term V :=
  meet (const .I) (product r topTerm)

def witnessTerm {V : Type} (r f g : Term V) : Term V :=
  meet (const .I) (product (product f r) (converse g))

def chosenTerm {n : Nat} (t : Term (Fin n)) : Semiformula.Operator FilterLanguage n :=
  ⟨Semiformula.rel RelationSymbol.chosen ![embedTerm Semiterm.bvar t]⟩

def representedOp : Semiformula.Operator FilterLanguage 3 :=
  chosenTerm (witnessTerm (.var 0) (.var 1) (.var 2))

def membershipOp : Semiformula.Operator FilterLanguage 2 :=
  chosenTerm (witnessTerm (.const .E) (.var 0) (.var 1))

def agreementOp : Semiformula.Operator FilterLanguage 2 :=
  chosenTerm (supportTerm (meet (.var 0) (.var 1)))

def localFunctionOp : Semiformula.Operator FilterLanguage 1 :=
  let composite : Semiterm.Operator FilterLanguage 1 :=
    ⟨embedTerm Semiterm.bvar (product (converse (.var 0)) (.var 0))⟩
  let selected : Semiformula.Operator FilterLanguage 1 := chosenTerm (supportTerm (.var 0))
  ⟨“x. !inclusionOp.sentence (!composite.term x) (!unitOp.term) ∧ !selected.sentence x”⟩

/-- A local function names an actual point in the represented square
precisely when there is a represented singleton diagonal at that point. -/
def namedPointOp : Semiformula.Operator FilterLanguage 1 :=
  ⟨“a. !localFunctionOp.sentence a ∧ ∃ d, ∀ x y,
    (!localFunctionOp.sentence x ∧ !localFunctionOp.sentence y) →
      (!representedOp.sentence d x y ↔ !agreementOp.sentence x a ∧ !agreementOp.sentence y a)”⟩

section Meaning

variable {A : Type} [Tarski.Structure FilterLanguage A] [Tarski.Structure.Eq FilterLanguage A]

local notation "M" => algebraOf A

theorem chosenTerm_eval {n : Nat} (t : Term (Fin n)) (v : Fin n → A) :
    (chosenTerm t).sentence.Evalb v ↔ chosenOf A ((M).eval v t) := by
  change Tarski.Structure.rel (L := FilterLanguage) RelationSymbol.chosen _ ↔ _
  simp [chosenOf,embedTerm_eval,Matrix.constant_eq_singleton,Function.comp_def]

theorem representedOp_eval (r a b : A) :
    representedOp.sentence.Evalb ![r,a,b] ↔ chosenOf A (witness (M) r a b) := by
  simpa [representedOp,witnessTerm,Manifest.meet,Algebra.eval,Algebra.inf,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,witness] using
      chosenTerm_eval (witnessTerm (.var 0) (.var 1) (.var 2)) ![r,a,b]

theorem membershipOp_eval (a b : A) :
    membershipOp.sentence.Evalb ![a,b] ↔ chosenOf A (witness (M) ((M).constant .E) a b) := by
  simpa only [membershipOp,witnessTerm,Manifest.meet,Algebra.eval,Algebra.inf,
    Matrix.cons_val_zero,Matrix.cons_val_one,witness] using
      chosenTerm_eval (witnessTerm (.const .E) (.var 0) (.var 1)) ![a,b]

theorem agreementOp_eval (a b : A) :
    agreementOp.sentence.Evalb ![a,b] ↔ chosenOf A (support (M) ((M).inf a b)) := by
  simpa only [agreementOp,supportTerm,topTerm,Manifest.meet,Algebra.eval,Algebra.inf,MeredithLaws.top,
    MeredithLaws.sup,Matrix.cons_val_zero,Matrix.cons_val_one,support] using
      chosenTerm_eval (supportTerm (meet (.var 0) (.var 1))) ![a,b]

theorem localFunctionOp_eval (a : A) :
    localFunctionOp.sentence.Evalb ![a] ↔ Functional (M) a ∧ chosenOf A (support (M) a) := by
  simp [localFunctionOp,inclusionOp,meetOp,unitOp,Semiterm.fn,symbol_value,embedTerm_eval,
    Semiformula.eval_rew,Semiterm.val_rew,Semiterm.Operator.operator,Semiformula.Operator.operator,
    Semiformula.Operator.Eq.sentence_eq,Semiformula.eval_rel',Tarski.Structure.eq_iff_eq,
    Function.comp_def,Empty.eq_elim,Matrix.comp_vecCons',Matrix.empty_eq,Matrix.constant_eq_singleton,
    chosenTerm_eval,Functional,support,supportTerm,topTerm,Manifest.meet,
    MeredithLaws.Le,MeredithLaws.top,MeredithLaws.sup,Algebra.eval,Algebra.inf,algebraOf]

theorem namedPointOp_eval (a : A) :
    namedPointOp.sentence.Evalb ![a] ↔
      (Functional (M) a ∧ chosenOf A (support (M) a)) ∧
      ∃ diagonal, ∀ x y,
        (Functional (M) x ∧ chosenOf A (support (M) x)) ∧
        (Functional (M) y ∧ chosenOf A (support (M) y)) →
        (chosenOf A (witness (M) diagonal x y) ↔
          chosenOf A (support (M) ((M).inf x a)) ∧ chosenOf A (support (M) ((M).inf y a))) := by
  simp [namedPointOp,localFunctionOp_eval,representedOp_eval,agreementOp_eval,Semiformula.eval_rew,
    Function.comp_def,Empty.eq_elim,Matrix.comp_vecCons',Matrix.empty_eq,Matrix.constant_eq_singleton,
    -and_imp,-exists_and_left,-exists_and_right]

end Meaning
end PalomarI3380.Calibration
