module
public import I3_380.Calibration.TruthClauses
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Formula.Coding
@[expose] public section

namespace PalomarI3380.Calibration.CodedGraph

open Logic.Expanded
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic

variable {V : Type} {E G : V → V → Prop} {L : ClassAxioms E G} {inhabited : Nonempty V}
variable (D : OmegaDomain L inhabited) {P : Presentation D} (T : TruthTable D P)

noncomputable def boundVector {n : Nat} (assign : Fin n → P.Carrier D) : D.Points :=
  matrixToVec fun i => (assign i).val

theorem boundVector_cons {n : Nat} (a : P.Carrier D) (v : Fin n → P.Carrier D) :
    boundVector D (a :> v) = a.val ∷ boundVector D v := by
  rw [boundVector,matrixToVec_succ]
  rfl

theorem quote_term_value {n : Nat} (t : ClosedSemiterm GraphLanguage n) (v : Fin n → P.Carrier D)
    (f : D.Points) : letI := P.interpret D
    variableValue (⌜t⌝ : D.Points) ⟪boundVector D v,f⟫ P.fallback =
      (t.val v Empty.elim).val := by
  letI := P.interpret D
  cases t with
  | bvar i =>
    simp only [FFL.FirstOrder.Semiterm.empty_quote_bvar,variableValue_bound,Semiterm.val_bvar,lookup]
    have fit : (i.val : D.Points) < len (boundVector D v) := by
      simpa [boundVector,matrixToVec_len] using (show (i.val : D.Points) < (n : D.Points) from by exact_mod_cast i.isLt)
    rw [if_pos fit]
    exact matrixToVec_nth _ _
  | fvar i => exact i.elim
  | func symbol _ => exact symbol.elim

theorem tableRelation_quote {k n : Nat} (symbol : GraphLanguage.Rel k)
    (terms : Fin k → ClosedSemiterm GraphLanguage n) (v : Fin n → P.Carrier D) (f : D.Points) :
    letI := P.interpret D
    TableRelation D P (k : D.Points) (⌜symbol⌝ : D.Points)
      (matrixToVec fun i => ⌜terms i⌝) ⟪boundVector D v,f⟫ ↔
        Tarski.Structure.rel (L := GraphLanguage) symbol (fun i => (terms i).val v Empty.elim) := by
  letI := P.interpret D
  let t : Fin k → D.Points := fun i => ⌜terms i⌝
  let val : Fin k → D.Points := fun i => ((terms i).val v Empty.elim).val
  have value : Values (matrixToVec val) (matrixToVec t) ⟪boundVector D v,f⟫ P.fallback := by
    have eq : (fun i => variableValue (t i) ⟪boundVector D v,f⟫ P.fallback) = val :=
      funext fun i => quote_term_value D (terms i) v f
    simpa only [eq] using values_matrix t ⟪boundVector D v,f⟫ P.fallback
  obtain ⟨x,read,one⟩ := values_exist (matrixToVec t) ⟪boundVector D v,f⟫ P.fallback
  change (∃ vals, Values vals (matrixToVec t) ⟪boundVector D v,f⟫ P.fallback ∧
    E (⟪(k : D.Points),(⌜symbol⌝ : D.Points),vals⟫ : D.Points).val P.atoms) ↔
    E (⟪(k : D.Points),(⌜symbol⌝ : D.Points),matrixToVec val⟫ : D.Points).val P.atoms
  exact ⟨fun ⟨y,verified,truth⟩ => ((one y verified).trans (one _ value).symm) ▸ truth,
    fun h => ⟨_,value,h⟩⟩

theorem TruthTable.holds_quote {n : Nat} (φ : Semisentence GraphLanguage n)
    (v : Fin n → P.Carrier D) (f : D.Points) :
    letI := P.interpret D
    T.holds D (⌜φ⌝ : D.Points) ⟪boundVector D v,f⟫ ↔ φ.Evalb v := by
  letI := P.interpret D
  induction φ with
  | rel symbol terms =>
    change T.holds D (^rel _ (⌜symbol⌝ : D.Points) (matrixToVec fun i => ⌜terms i⌝)) _ ↔ _
    rw [T.holds_rel]
    exact tableRelation_quote D symbol terms v f
  | nrel symbol terms =>
    change T.holds D (^nrel _ (⌜symbol⌝ : D.Points) (matrixToVec fun i => ⌜terms i⌝)) _ ↔ _
    rw [T.holds_nrel]
    exact not_congr (tableRelation_quote D symbol terms v f)
  | verum =>
    exact ⟨fun _ => trivial,fun _ => T.holds_true D _⟩
  | falsum =>
    exact ⟨T.holds_false D _,False.elim⟩
  | and a b ha hb =>
    have code : (⌜a.and b⌝ : D.Points) = ⌜a⌝ ^⋏ ⌜b⌝ := rfl
    rw [code,T.holds_and]
    exact and_congr (ha v) (hb v)
  | or a b ha hb =>
    have code : (⌜a.or b⌝ : D.Points) = ⌜a⌝ ^⋎ ⌜b⌝ := rfl
    rw [code,T.holds_or]
    exact or_congr (ha v) (hb v)
  | all a ha =>
    have code : (⌜a.all⌝ : D.Points) = ^∀ ⌜a⌝ := FFL.FirstOrder.Sentence.quote_all (V := D.Points) a
    rw [code,T.holds_all]
    apply forall_congr'
    intro x
    have assignment : pushBound x.val ⟪boundVector D v,f⟫ = ⟪boundVector D (x :> v),f⟫ := by
      simp only [pushBound,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair,boundVector_cons]
    rw [assignment]
    exact ha (x :> v)
  | exs a ha =>
    have code : (⌜a.exs⌝ : D.Points) = ^∃ ⌜a⌝ := FFL.FirstOrder.Sentence.quote_ex (V := D.Points) a
    rw [code,T.holds_exs]
    apply exists_congr
    intro x
    have assignment : pushBound x.val ⟪boundVector D v,f⟫ = ⟪boundVector D (x :> v),f⟫ := by
      simp only [pushBound,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair,boundVector_cons]
    rw [assignment]
    exact ha (x :> v)

end PalomarI3380.Calibration.CodedGraph
