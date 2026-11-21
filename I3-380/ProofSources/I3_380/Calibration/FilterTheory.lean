module
public import I3_380.Calibration.FilterLanguage
public import I3_380.RelationAlgebra.Ultrafilter
@[expose] public section

namespace PalomarI3380.Calibration

open FFL FFL.FirstOrder Manifest RelationLaws
open Term

def unitOp : Semiterm.Const FilterLanguage :=
  Semiterm.fn (FunctionSymbol.constant .I)

def meetOp : Semiterm.Operator FilterLanguage 2 :=
  ⟨embedTerm Semiterm.bvar (meet (.var 0) (.var 1))⟩

def complementOp : Semiterm.Operator FilterLanguage 1 :=
  Semiterm.fn FunctionSymbol.complement

def chosenOp : Semiformula.Operator FilterLanguage 1 :=
  ⟨Semiformula.rel RelationSymbol.chosen Semiterm.bvar⟩

def inclusionOp : Semiformula.Operator FilterLanguage 2 :=
  ⟨“a b. !meetOp.term a b = a”⟩

def topTerm {V : Type} : Term V :=
  neg (meet (neg (const .I)) (neg (neg (const .I))))

def zeroOp : Semiterm.Const FilterLanguage :=
  ⟨embedTerm Semiterm.bvar (neg topTerm)⟩

def supportedDifference (a b : Constant) : FFL.FirstOrder.Sentence FilterLanguage :=
  let t : Term Empty := meet (const .I) (product (meet (const a) (neg (const b))) topTerm)
  chosenOp.operator ![embedTerm Empty.elim t]

/-- The six ultrafilter laws and the support of a separating edge. -/
def filterSentence : FFL.FirstOrder.Sentence FilterLanguage :=
  (“(∀ x, !chosenOp.sentence x → !inclusionOp.sentence x (!unitOp)) ∧ !chosenOp.sentence (!unitOp) ∧ ¬!chosenOp.sentence (!zeroOp) ∧
    (∀ x y, !chosenOp.sentence x → !inclusionOp.sentence x y → !inclusionOp.sentence y (!unitOp) → !chosenOp.sentence y) ∧
    (∀ x y, !chosenOp.sentence x → !chosenOp.sentence y → !chosenOp.sentence (!meetOp.term x y)) ∧
    (∀ x, !inclusionOp.sentence x (!unitOp) → !chosenOp.sentence x ∨ !chosenOp.sentence (!meetOp.term (!unitOp) (!complementOp.term x))) ∧
    (!(supportedDifference .D .J) ∨ !(supportedDifference .J .D))” : FFL.FirstOrder.Sentence FilterLanguage)

/-- The finite auxiliary theory. Its language supplies no additional
set-theoretic axioms. -/
def filterTheory : FFL.FirstOrder.Theory FilterLanguage :=
  𝗘𝗤 FilterLanguage ∪ {φ | φ ∈ filterSentence :: preceding.map equationSentence}

section Meaning

variable {A : Type} [Tarski.Structure FilterLanguage A] [Nonempty A] [Tarski.Structure.Eq FilterLanguage A]

local notation "M" => algebraOf A

omit [Nonempty A] [Tarski.Structure.Eq FilterLanguage A] in
private theorem chosenSentence_eval (values : Fin 1 → A) :
    chosenOp.sentence.Evalb values ↔ chosenOf A (values 0) := by
  change Tarski.Structure.rel (L := FilterLanguage) RelationSymbol.chosen values ↔ _
  rw [Matrix.fun_eq_vec_one values]
  rfl

private theorem equalitySentence_eval (values : Fin 2 → A) :
    (Semiformula.Operator.Eq.eq (L := FilterLanguage)).sentence.Evalb values ↔ values 0 = values 1 :=
  Tarski.Structure.eq_iff_eq

theorem supportedDifference_eval (a b : Constant) :
    A↓[FilterLanguage] ⊧ supportedDifference a b ↔
      chosenOf A (support (M) ((M).inf ((M).constant a) ((M).neg ((M).constant b)))) := by
  simp [supportedDifference,models_iff,chosenOf,chosenSentence_eval,Semiformula.Operator.val,Semiformula.eval_rew,
    Function.comp_def,Matrix.comp_vecCons',Empty.eq_elim,Matrix.empty_eq,Matrix.constant_eq_singleton,
    embedTerm_eval,support,topTerm,MeredithLaws.top,MeredithLaws.sup,Manifest.meet,Algebra.eval,Algebra.inf]

private theorem supportedDifference_at (a b : Constant) (v : Fin 0 → A) :
    (supportedDifference a b).Evalb v ↔
      chosenOf A (support (M) ((M).inf ((M).constant a) ((M).neg ((M).constant b)))) := by
  have equal : v = ![] := funext fun i => i.elim0
  rw [equal]
  exact supportedDifference_eval a b

theorem filterSentence_eval :
    A↓[FilterLanguage] ⊧ filterSentence ↔
      ∃ F : SubidentityUltrafilter (M), F.member = chosenOf A ∧
      (F.member (support (M) ((M).inf ((M).constant .D) ((M).neg ((M).constant .J)))) ∨
       F.member (support (M) ((M).inf ((M).constant .J) ((M).neg ((M).constant .D))))) := by
  have laws : A↓[FilterLanguage] ⊧ filterSentence ↔
      (∀ x, chosenOf A x → (M).le x ((M).constant .I)) ∧
      chosenOf A ((M).constant .I) ∧ ¬chosenOf A (M).zero ∧
      (∀ x y, chosenOf A x → (M).le x y → (M).le y ((M).constant .I) → chosenOf A y) ∧
      (∀ x y, chosenOf A x → chosenOf A y → chosenOf A ((M).inf x y)) ∧
      (∀ x, (M).le x ((M).constant .I) → chosenOf A x ∨
        chosenOf A ((M).inf ((M).constant .I) ((M).neg x))) ∧
      (chosenOf A (support (M) ((M).inf ((M).constant .D) ((M).neg ((M).constant .J)))) ∨
       chosenOf A (support (M) ((M).inf ((M).constant .J) ((M).neg ((M).constant .D))))) := by
    simp [filterSentence,models_iff,chosenSentence_eval,zeroOp,unitOp,meetOp,complementOp,inclusionOp,
      equalitySentence_eval,Semiformula.eval_rew,Semiformula.eval_rel',Semiterm.val_rew,Semiterm.Operator.operator,Semiformula.Operator.operator,
      Function.comp_def,Empty.eq_elim,Matrix.comp_vecCons',Matrix.empty_eq,Matrix.constant_eq_singleton,
      Semiterm.fn,symbol_value,embedTerm_eval,Manifest.meet,MeredithLaws.Le,MeredithLaws.bottom,MeredithLaws.top,
      MeredithLaws.sup,topTerm,Algebra.eval,Algebra.inf,chosenOf,algebraOf,support,supportedDifference_at]
  rw [laws]
  constructor
  · rintro ⟨sub,unit,nozero,up,closed,split,hit⟩
    exact ⟨⟨chosenOf A,fun {_} h => sub _ h,unit,nozero,
      fun {_ _} => up _ _,fun {_ _} => closed _ _,split⟩,rfl,hit⟩
  · rintro ⟨F,he,hit⟩
    rw [← he]
    exact ⟨fun _ h => F.subunit h,F.unit_mem,F.zero_not_mem,
      fun _ _ => F.filter_up,fun _ _ => F.filter_inf,F.decide_piece,hit⟩

theorem equations_of_filter_model (model : A↓[FilterLanguage] ⊧* filterTheory) :
    (M).Models preceding := by
  intro e he
  have ax : equationSentence e ∈ filterTheory := Or.inr
    (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨e,he,rfl⟩))
  exact (equationSentence_eval e).mp (models_theory_iff.mp model _ ax)

theorem ultrafilter_of_filter_model (model : A↓[FilterLanguage] ⊧* filterTheory) :
    ∃ F : SubidentityUltrafilter (M), F.member = chosenOf A ∧
      (F.member (support (M) ((M).inf ((M).constant .D) ((M).neg ((M).constant .J)))) ∨
        F.member (support (M) ((M).inf ((M).constant .J) ((M).neg ((M).constant .D))))) :=
  filterSentence_eval.mp (models_theory_iff.mp model filterSentence (Or.inr List.mem_cons_self))

end Meaning
end PalomarI3380.Calibration
