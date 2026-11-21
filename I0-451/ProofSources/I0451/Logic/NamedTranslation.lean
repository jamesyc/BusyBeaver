module
public import I0451.Logic.NamedProofs
public import I0451.Logic.Tait.Native

/-! Match named native formulas with Foundation formulas and the
native lowering of their Gödel codes. Quantifier naming is kept
separate from the propositional normalization. -/
@[expose] public section
namespace I0451.Logic.NamedFormula

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open I0451.Arithmetization I0451.Runtime I0451.Logic.Tait
open ZF207.CKernel.Generic

local notation "K" => calculus.toLogic

def fromNative : I0451.Logic.Formula → NamedFormula
  | .truth => .truth
  | .imp a b => .imp (fromNative a) (fromNative b)
  | .mem 0 0 => .falsity
  | .mem a b => .mem a b
  | .equal a b => .equal a b
  | .all a b => .all a (fromNative b)

theorem fromNative_code (f : I0451.Logic.Formula) : (fromNative f).code = f.code := by
  induction f with
  | truth => rfl
  | mem a b =>
    cases a <;> cases b <;> simp [fromNative, code, I0451.Logic.Formula.code,
      modelTag, modelImp, cantor_nat_pair, I0451.Logic.mem] <;> rfl
  | equal a b =>
    simp [fromNative, code, I0451.Logic.Formula.code, modelTag, modelImp, cantor_nat_pair, I0451.Logic.equal]
  | all a b hb =>
    simp [fromNative, code, I0451.Logic.Formula.code, modelTag, modelImp, cantor_nat_pair, I0451.Logic.all, hb]
  | imp a b ha hb =>
    simp [fromNative, code, I0451.Logic.Formula.code, modelImp, cantor_nat_pair, I0451.Logic.imp, ha, hb]

def toSet {ξ : Type} {n : Nat} (terms : Nat → Semiterm ℒₛₑₜ ξ n) :
    NamedFormula → Semiformula ℒₛₑₜ ξ n
  | .truth => ⊤
  | .falsity => ⊥
  | .mem a b => .rel Language.Set.Rel.mem ![terms a,terms b]
  | .equal a b => .rel Language.Set.Rel.eq ![terms a,terms b]
  | .imp a b => toSet terms a 🡒 toSet terms b
  | .all a b => ∀¹ toSet (SetSyntax.bindTerms terms a) b

private theorem truth_equiv :
    (K).Prov ((K).iff (cneg (1 : Nat)) (0 : Nat)) := by
  apply Logic.Ctx.empty
  exact Logic.Ctx.iffIntro (.thm NativeDerivable.truth) (.thm ((K).identity 1))

private theorem negNeg_equiv (a : Nat) : (K).Prov ((K).iff (cneg (cneg a)) a) := by
  have first : (K).Ctx [cneg (cneg a)] a := .dne .head
  have second : (K).Ctx [a] (cneg (cneg a)) := by
    apply Logic.Ctx.deduction
    exact .mp (.hyp (by simp)) .head
  exact (Logic.Ctx.iffIntro first second).empty

private theorem implication_equiv (a b : Nat) :
    (K).Prov ((K).iff ((K).neg ((K).and a ((K).neg b))) ((K).imp a b)) := by
  apply Logic.Ctx.empty
  apply Logic.Ctx.iffIntro
  · apply Logic.Ctx.deduction
    apply Logic.Ctx.byCases b
    · exact .head
    · have noAnd : (K).Ctx [(K).neg b, a, (K).neg ((K).and a ((K).neg b))]
          ((K).neg ((K).and a ((K).neg b))) := .hyp (by simp)
      have combined : (K).Ctx [(K).neg b, a, (K).neg ((K).and a ((K).neg b))]
          ((K).and a ((K).neg b)) := .andIntro (.hyp (by simp)) .head
      exact (.mp combined noAnd : (K).Ctx _ (1 : Nat)).explosion b
  · apply Logic.Ctx.deduction
    have combined : (K).Ctx [(K).and a ((K).neg b), (K).imp a b] ((K).and a ((K).neg b)) := .head
    have applied : (K).Ctx [(K).and a ((K).neg b), (K).imp a b] b :=
      .mp combined.andLeft (.hyp (by simp))
    exact .mp applied combined.andRight

private theorem negative_equiv {q : Nat} (wf : IsUFormula ℒₛₑₜ q) (param : Nat) :
    (K).Prov ((K).iff (π₂ (tr param q)) (cneg (π₁ (tr param q)))) := by
  rcases tr_pair wf param with same | same
  · rw [same]
    exact (Logic.Ctx.iffRefl _).empty
  · rw [same]
    exact (Logic.Ctx.iffSymm (.thm (negNeg_equiv _))).empty

private theorem lower_imp (a b : SetTheorySemiproposition n) (param : Nat) :
    (K).Prov ((K).iff (π₁ (tr param (⌜a 🡒 b⌝ : Nat)))
      ((K).imp (π₁ (tr param (⌜a⌝ : Nat))) (π₁ (tr param (⌜b⌝ : Nat))))) := by
  have wa : IsUFormula ℒₛₑₜ (⌜a⌝ : Nat) := (Semiformula.quote_isSemiformula (V := Nat) a).isUFormula
  have wb : IsUFormula ℒₛₑₜ (⌜b⌝ : Nat) := (Semiformula.quote_isSemiformula (V := Nat) b).isUFormula
  rw [Semiformula.imp_eq, Semiformula.quote_or, quoteSetNeg]
  rw [tr_or wa.neg wb, negPair, pi₁_pair, (tr_neg wa param).2]
  have congr := Logic.Ctx.negCongr (S := (K)) (Γ := [])
    (Logic.Ctx.andCongr (Logic.Ctx.iffRefl (π₁ (tr param (⌜a⌝ : Nat))))
      (.thm (negative_equiv wb param)))
  exact (congr.iffTrans (.thm (implication_equiv _ _))).empty
where
  quoteSetNeg (f : SetTheorySemiproposition n) :
      (⌜∼f⌝ : Nat) = Bootstrapping.neg ℒₛₑₜ (⌜f⌝ : Nat) := by
    simp [Semiformula.quote_def]

/-- The name assigned by the internal compiler to a standard term. -/
noncomputable def termLabel {n : Nat} (bound offset : Nat) (term : SyntacticSemiterm ℒₛₑₜ n) : Nat :=
  vlab bound offset (⌜term⌝ : Nat)

private theorem termLabel_bind {n : Nat} (terms : Nat → SyntacticSemiterm ℒₛₑₜ n)
    (bound offset label name : Nat) :
    termLabel (name ∷ bound) offset ∘ SetSyntax.bindTerms terms label =
      assign (termLabel bound offset ∘ terms) label name := by
  funext i
  by_cases selected : i = label
  · simp [termLabel, SetSyntax.bindTerms, assign, selected]
  · simp only [Function.comp_def, termLabel, SetSyntax.bindTerms, assign, selected, ite_false]
    have quoted : (⌜Rew.bShift (terms i)⌝ : Nat) = termBShift ℒₛₑₜ (⌜terms i⌝ : Nat) := by
      simp [Semiterm.quote_def, Semiterm.typed_quote_bShift, Bootstrapping.Semiterm.bShift]
    rw [quoted]
    have codeTerm : IsUTerm ℒₛₑₜ (⌜terms i⌝ : Nat) := by
      change IsUTerm ℒₛₑₜ ((⌜terms i⌝ : Bootstrapping.Semiterm Nat ℒₛₑₜ n).val)
      exact (⌜terms i⌝ : Bootstrapping.Semiterm Nat ℒₛₑₜ n).isSemiterm.isUTerm
    exact vlab_termBShift codeTerm name bound offset

private theorem tr_relation {n : Nat} (r : (ℒₛₑₜ).Rel 2) (a b : SyntacticSemiterm ℒₛₑₜ n)
    (bound offset depth family : Nat) :
    π₁ (tr ⟪bound, depth, offset, family⟫ (⌜(.rel r ![a,b] : SetTheorySemiproposition n)⌝ : Nat)) =
      atomL (Encodable.encode r) (termLabel bound offset a) (termLabel bound offset b) := by
  let terms : Fin 2 → SyntacticSemiterm ℒₛₑₜ n := ![a,b]
  let packed : SemitermVec Nat ℒₛₑₜ 2 n := fun i => ⌜terms i⌝
  have atomRule := tr_rel (param := ⟪bound, depth, offset, family⟫)
    (codeIn_rel_quote (V := Nat) (L := ℒₛₑₜ) r) packed.isUTermVec
  rw [Semiformula.quote_rel, atomRule, posPair, pi₁_pair]
  have at0 := SemitermVec.val_nth_eq packed 0
  have at1 := SemitermVec.val_nth_eq packed 1
  simp only [natCast_nat, Fin.val_zero, Fin.val_one] at at0 at1
  unfold atom
  rw [at0, at1]
  have sameQuoting := quote_rel_def (V := Nat) (L := ℒₛₑₜ) r
  simp only [natCast_nat] at sameQuoting
  rw [sameQuoting, penv_mk, poff_mk]
  rfl

set_option maxHeartbeats 1500000 in
theorem native_lowering (f : NamedFormula) {n : Nat} (terms : Nat → SyntacticSemiterm ℒₛₑₜ n)
    (bound offset depth family : Nat) :
    (K).Prov ((K).iff
      (π₁ (tr ⟪bound,depth,offset,family⟫ (⌜f.toSet terms⌝ : Nat)))
      (f.relabel (xlab family) depth (termLabel bound offset ∘ terms)).code) := by
  induction f generalizing n terms bound depth with
  | truth =>
    simpa only [toSet, relabel, code, Semiformula.quote_verum, tr_verum, posPair, pi₁_pair] using truth_equiv
  | falsity =>
    simpa only [toSet, relabel, code, Semiformula.quote_falsum, tr_falsum, negPair, pi₁_pair] using negNeg_equiv 1
  | mem x y =>
    rw [toSet, tr_relation]
    have rel : Encodable.encode Language.Set.Rel.mem = 1 := rfl
    rw [rel]
    change (K).Prov ((K).iff (atomL 1 _ _) _)
    rw [atomL, if_neg (by decide : (1 : Nat) ≠ 0)]
    exact (Logic.Ctx.iffRefl _).empty
  | equal x y =>
    rw [toSet, tr_relation]
    have rel : Encodable.encode Language.Set.Rel.eq = 0 := rfl
    rw [rel, atomL, if_pos rfl]
    exact (Logic.Ctx.iffRefl _).empty
  | imp a b ihA ihB =>
    have base := lower_imp (a.toSet terms) (b.toSet terms) ⟪bound,depth,offset,family⟫
    exact ((Logic.Ctx.thm base).iffTrans
      (Logic.Ctx.impCongr (.thm (ihA terms bound depth)) (.thm (ihB terms bound depth)))).empty
  | all x p ih =>
    let names : Nat → Nat := xlab family
    let name := names depth
    have good := (Semiformula.quote_isSemiformula (V := Nat) (p.toSet (SetSyntax.bindTerms terms x))).isUFormula
    have body := ih (SetSyntax.bindTerms terms x) (name ∷ bound) (depth+1)
    rw [termLabel_bind] at body
    rw [toSet, Semiformula.quote_all, tr_all good, posPair, pi₁_pair, step_mk]
    simpa only [pfam_mk, pdep_mk, relabel, code, calculus_all, name, names] using
      (Logic.Ctx.allCongr name (fun _ h => (List.not_mem_nil h).elim) (.thm body)).empty

end I0451.Logic.NamedFormula
