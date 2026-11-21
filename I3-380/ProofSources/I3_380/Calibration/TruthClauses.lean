module
public import I3_380.Calibration.TruthLayerEval
@[expose] public section

namespace PalomarI3380.Calibration.CodedGraph

open Logic Logic.Expanded SquareRepresentation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type} {E G : V → V → Prop} {L : ClassAxioms E G} {inhabited : Nonempty V}
variable (D : OmegaDomain L inhabited) {P : Presentation D} (T : TruthTable D P)

def TruthTable.Decoded (p env : D.Points) : Prop :=
  p = (^⊤ : D.Points) ∨
    (∃ k r terms, p = ^rel k r terms ∧ TableRelation D P k r terms env) ∨
    (∃ k r terms, p = ^nrel k r terms ∧ ¬TableRelation D P k r terms env) ∨
    (∃ a b, p = a ^⋏ b ∧ T.holds D a env ∧ T.holds D b env) ∨
    (∃ a b, p = a ^⋎ b ∧ (T.holds D a env ∨ T.holds D b env)) ∨
    (∃ a, p = ^∀ a ∧ ∀ x : P.Carrier D, T.holds D a (pushBound x.val env)) ∨
    (∃ a, p = ^∃ a ∧ ∃ x : P.Carrier D, T.holds D a (pushBound x.val env))

set_option maxHeartbeats 800000 in
theorem TruthTable.decode (p env : D.Points) (positive : 0<p) :
    T.holds D p env ↔ T.Decoded D p env := by
  obtain ⟨prior,restricted,values⟩ := T.row p
  have top : arith (E := E) (G := G) truthInputDef.val (P.data D).omega ![p.val] ↔
      p=(^⊤ : D.Points) := by
    simpa only [Presentation.data,pointValues_cons,pointValues_nil,truthInput_eval]
      using arith_args D truthInputDef.val ![p]
  have pRel := atomLayer_eval D P false p env positive
  have nRel := atomLayer_eval D P true p env positive
  have conj := binaryLayer_eval D P true p env prior
  have disj := binaryLayer_eval D P false p env prior
  have forall' := binderLayer_eval D P true p env prior
  have exists' := binderLayer_eval D P false p env prior
  refine (values env).trans ?_
  unfold FormulaLayer TruthTable.Decoded
  refine or_congr top (or_congr ?_ (or_congr ?_ (or_congr ?_ (or_congr ?_ (or_congr ?_ ?_)))))
  · simpa [qqRel] using pRel
  · simpa [qqNRel] using nRel
  · refine conj.trans ?_
    apply exists_congr
    intro a
    apply exists_congr
    intro b
    change (p=a ^⋏ b ∧ _) ↔ _
    exact and_congr_right fun shape =>
      and_congr (T.prior_holds D restricted (by rw [shape]; simp))
        (T.prior_holds D restricted (by rw [shape]; simp))
  · refine disj.trans ?_
    apply exists_congr
    intro a
    apply exists_congr
    intro b
    change (p=a ^⋎ b ∧ _) ↔ _
    exact and_congr_right fun shape =>
      or_congr (T.prior_holds D restricted (by rw [shape]; simp))
        (T.prior_holds D restricted (by rw [shape]; simp))
  · refine forall'.trans ?_
    apply exists_congr
    intro a
    change (p = ^∀ a ∧ _) ↔ _
    exact and_congr_right fun shape =>
      forall_congr' fun x : P.Carrier D => T.prior_holds D restricted (by rw [shape]; simp)
  · refine exists'.trans ?_
    apply exists_congr
    intro a
    change (p = ^∃ a ∧ _) ↔ _
    exact and_congr_right fun shape =>
      exists_congr fun x : P.Carrier D => T.prior_holds D restricted (by rw [shape]; simp)

theorem TruthTable.holds_true (env : D.Points) : T.holds D (^⊤) env := by
  rw [T.decode D _ _ (by unfold qqVerum; simp)]
  exact Or.inl rfl

theorem TruthTable.holds_false (env : D.Points) : ¬T.holds D (^⊥) env := by
  rw [T.decode D _ _ (by unfold qqFalsum; simp)]
  simp [TruthTable.Decoded,qqFalsum,qqVerum,qqRel,qqNRel,qqAnd,qqOr,qqAll,qqExs]

theorem TruthTable.holds_rel (k r terms env : D.Points) :
    T.holds D (^rel k r terms) env ↔ TableRelation D P k r terms env := by
  rw [T.decode D _ _ (by unfold qqRel; simp)]
  simp [TruthTable.Decoded,qqRel,qqVerum,qqNRel,qqAnd,qqOr,qqAll,qqExs]

theorem TruthTable.holds_nrel (k r terms env : D.Points) :
    T.holds D (^nrel k r terms) env ↔ ¬TableRelation D P k r terms env := by
  rw [T.decode D _ _ (by unfold qqNRel; simp)]
  simp [TruthTable.Decoded,qqRel,qqVerum,qqNRel,qqAnd,qqOr,qqAll,qqExs]

theorem TruthTable.holds_and (p q env : D.Points) :
    T.holds D (p ^⋏ q) env ↔ T.holds D p env ∧ T.holds D q env := by
  rw [T.decode D _ _ (by unfold qqAnd; simp)]
  simp [TruthTable.Decoded,qqRel,qqVerum,qqNRel,qqAnd,qqOr,qqAll,qqExs]

theorem TruthTable.holds_or (p q env : D.Points) :
    T.holds D (p ^⋎ q) env ↔ T.holds D p env ∨ T.holds D q env := by
  rw [T.decode D _ _ (by unfold qqOr; simp)]
  simp [TruthTable.Decoded,qqRel,qqVerum,qqNRel,qqAnd,qqOr,qqAll,qqExs]

theorem TruthTable.holds_all (p env : D.Points) :
    T.holds D (^∀ p) env ↔ ∀ x : P.Carrier D, T.holds D p (pushBound x.val env) := by
  rw [T.decode D _ _ (by unfold qqAll; simp)]
  simp [TruthTable.Decoded,qqRel,qqVerum,qqNRel,qqAnd,qqOr,qqAll,qqExs]

theorem TruthTable.holds_exs (p env : D.Points) :
    T.holds D (^∃ p) env ↔ ∃ x : P.Carrier D, T.holds D p (pushBound x.val env) := by
  rw [T.decode D _ _ (by unfold qqExs; simp)]
  simp [TruthTable.Decoded,qqRel,qqVerum,qqNRel,qqAnd,qqOr,qqAll,qqExs]

end PalomarI3380.Calibration.CodedGraph
