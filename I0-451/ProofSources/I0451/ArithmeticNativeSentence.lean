module
public import I0451.ArithmeticNativeProof
public import Foundation.FirstOrder.Arithmetic.Basic.Model

/-! A fixed arithmetic sentence for refutability in the native proof
calculus. The axiom schema formulas use the shared counter-expression
encoding, rather than a second set of hand-written constructor formulas. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Runtime

def headSlots : Fin 10 → Fin 5 := ![0,1,2,3,4,1,1,1,1,1]
def bundleSlots : Fin 10 → Fin 4 := ![0,1,2,3,1,1,1,1,1,1]

def headGraphs : List CounterExpr → 𝚺ᴬ₁.Semisentence 5
  | [] => .mkSigma “out a b c x. ⊥”
  | expr :: rest =>
    let graph := expr.graphOn headSlots
    let others := headGraphs rest
    .mkSigma (graph.val ⋎ others.val)

def nativeHeadsDef : 𝚺ᴬ₁.Semisentence 5 :=
  headGraphs (symbolicEncoding.heads (.input 0) (.input 1) (.input 2) (.input 3))

abbrev nativeBundleDef : 𝚺ᴬ₁.Semisentence 4 :=
  (symbolicEncoding.bundle (.input 0) (.input 1) (.input 2)).graphOn bundleSlots

def taggedFormulaDef (tag : Nat) : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “out a b. ∃ p, !cantorDef p a b ∧ out = 4 * p + ↑(tag)”

def closedExpressionDef (expr : CounterExpr) : 𝚺ᴬ₁.Semisentence 1 :=
  expr.graphOn (fun _ => 0)

def nativeLineDef : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “f book line.
    f = ↑(0 : Nat) ∨ !(closedExpressionDef literalFoundationTerm) f ∨
    !(closedExpressionDef literalBerkeleyTerm) f ∨
    (∃ a b c x, !nativeHeadsDef f a b c x) ∨
    (∃ a b c, c ≠ a ∧ c ≠ b ∧ !nativeBundleDef f a b c) ∨
    (∃ label, ∃ prior < line, ∃ a, !znthDef a book prior ∧ !(taggedFormulaDef 2) f label a) ∨
    (∃ i < line, ∃ j < line, ∃ a p, !znthDef a book i ∧ !znthDef p book j ∧ !(taggedFormulaDef 0) p a f)”

def nativeDerivableDef : 𝚺ᴬ₁.Semisentence 1 :=
  .mkSigma “formula. ∃ book length, :Seq book ∧ !lhDef length book ∧
    (∃ line < length, !znthDef formula book line) ∧
    ∀ line < length, ∃ f, !znthDef f book line ∧ !nativeLineDef f book line”

def nativeRefutable : 𝚺ᴬ₁.Sentence :=
  Bounding.HierarchySymbol.Semiformula.rew (Rew.subst ![(↑(1 : Nat) : ArithmeticSemiterm Empty 0)]) nativeDerivableDef

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem headGraphs_eval (exprs : List CounterExpr) (args : Fin 5 → V) :
    (headGraphs exprs).val.Evalb args ↔
      ∃ expr ∈ exprs, args 0 = expr.modelEval (fun i => args (headSlots i.succ)) := by
  induction exprs with
  | nil => simp [headGraphs]
  | cons expr rest ih =>
    have expanded : (headGraphs (expr :: rest)).val =
        (expr.graphOn headSlots).val ⋎ (headGraphs rest).val := rfl
    simp only [expanded, LogicalConnective.HomClass.map_or, expr.graphOn_eval, ih]
    simp only [List.mem_cons, exists_eq_or_imp, show headSlots 0 = 0 from rfl]
    rfl

theorem nativeHeads_eval (out a b c x : V) :
    nativeHeadsDef.val.Evalb ![out,a,b,c,x] ↔ out ∈ modelEncoding.heads a b c x := by
  let args : Fin 5 → V := ![out,a,b,c,x]
  let input (i : Fin 9) := args (headSlots i.succ)
  have evaluated : (symbolicEncoding.heads (.input 0) (.input 1) (.input 2) (.input 3)).map
      (CounterExpr.modelEval input) = modelEncoding.heads a b c x := by
    rw [modelEval_heads]
    rfl
  change nativeHeadsDef.val.Evalb args ↔ _
  rw [nativeHeadsDef, headGraphs_eval, ← evaluated]
  simp only [List.mem_map]
  exact ⟨fun ⟨expr, present, eq⟩ => ⟨expr, present, eq.symm⟩,
    fun ⟨expr, present, eq⟩ => ⟨expr, present, eq.symm⟩⟩

theorem nativeBundle_eval (out a b c : V) :
    nativeBundleDef.val.Evalb ![out,a,b,c] ↔ out = modelEncoding.bundle a b c := by
  rw [CounterExpr.graphOn_eval, modelEval_bundle]
  rfl

theorem taggedFormula_eval (tag : Nat) (out a b : V) :
    (taggedFormulaDef tag).val.Evalb ![out,a,b] ↔ out = modelTag tag a b := by
  simp [taggedFormulaDef, modelTag, modelImp, cantor_defined.iff, numeral_eq_natCast]

theorem closedExpression_eval (expr : CounterExpr) (closed : expr.closed = true) (out : V) :
    (closedExpressionDef expr).val.Evalb (fun _ : Fin 1 => out) ↔ out = (expr.eval (fun _ => 0) : V) := by
  rw [closedExpressionDef, expr.graphOn_eval]
  have value (s : Fin 9 → V) : expr.modelEval s = (expr.eval (fun _ => 0) : V) :=
    (expr.modelEval_closed closed s (fun _ => ((0 : Nat) : V))).trans (expr.modelEval_cast (fun _ => 0))
  rw [value]

attribute [local irreducible] literalFoundationCode literalBerkeleyCode

private theorem closedExpression_code (expr : CounterExpr) (code : Nat)
    (eq : code = expr.eval (fun _ => 0)) (closed : expr.closed = true) (out : V) :
    (closedExpressionDef expr).val.Eval (fun _ : Fin 1 => out) Empty.elim ↔ out = (code : V) := by
  rw [eq]
  exact closedExpression_eval expr closed out

private theorem foundationTerm_eval (f : V) :
    (closedExpressionDef literalFoundationTerm).val.Eval (fun _ : Fin 1 => f) Empty.elim ↔
      f = (literalFoundationCode : V) :=
  closedExpression_code _ _ literalFoundationCode_eq literalFoundationTerm_closed f

private theorem berkeleyTerm_eval (f : V) :
    (closedExpressionDef literalBerkeleyTerm).val.Eval (fun _ : Fin 1 => f) Empty.elim ↔
      f = (literalBerkeleyCode : V) :=
  closedExpression_code _ _ literalBerkeleyCode_eq literalBerkeleyTerm_closed f

@[simp] private theorem arithmetic_operator_numeral (args : Fin 0 → V) (n : Nat) :
    (Semiterm.Operator.numeral ℒₒᵣ n).val args = (n : V) := by
  have noArgs : args = (![] : Fin 0 → V) := by funext i; exact i.elim0
  rw [noArgs, Tarski.Structure.numeral_eq_numeral, numeral_eq_natCast]

theorem nativeLine_eval (f book line : V) :
    nativeLineDef.val.Evalb ![f,book,line] ↔ NativeLine book line f := by
  have heads (f a b c x : V) :
      nativeHeadsDef.val.Eval (f :> a :> b :> c :> fun _ : Fin 1 => x) Empty.elim ↔
        f ∈ modelEncoding.heads a b c x := by
    simpa only [Matrix.vec_single_eq_const] using nativeHeads_eval f a b c x
  have bundle (f a b c : V) :
      nativeBundleDef.val.Eval (f :> a :> b :> fun _ : Fin 1 => c) Empty.elim ↔
        f = modelEncoding.bundle a b c := by
    simpa only [Matrix.vec_single_eq_const] using nativeBundle_eval f a b c
  have tag (k : Nat) (f a b : V) :
      (taggedFormulaDef k).val.Eval (f :> a :> fun _ : Fin 1 => b) Empty.elim ↔
        f = modelTag k a b := by
    simpa only [Matrix.vec_single_eq_const] using taggedFormula_eval k f a b
  have applies (a b : V) : modelTag 0 a b = modelImp a b := by simp [modelTag]
  have general (a b : V) : modelTag 2 a b = modelEncoding.all a b := rfl
  simp [nativeLineDef, foundationTerm_eval, berkeleyTerm_eval, heads, bundle, tag,
    znth_defined.iff, applies, general, Matrix.comp_vecCons', Function.comp_def]
  constructor
  · rintro (rfl | rfl | rfl | ⟨a, b, c, x, member⟩ | ⟨a, b, c, fa, fb, rfl⟩ |
      ⟨label, prior, before, rfl⟩ | ⟨i, hi, j, hj, conditional⟩)
    · exact .truth
    · exact .foundation
    · exact .berkeley
    · exact .head a b c x f member
    · exact .bundle a b c fa fb
    · exact .generalize label prior before
    · exact .detach _ _ i j hi hj rfl conditional
  · intro proof
    cases proof with
    | truth => exact .inl rfl
    | foundation => exact .inr (.inl rfl)
    | berkeley => exact .inr (.inr (.inl rfl))
    | head a b c x f member => exact .inr (.inr (.inr (.inl ⟨a,b,c,x,member⟩)))
    | bundle a b c freshA freshB => exact .inr (.inr (.inr (.inr (.inl ⟨a,b,c,freshA,freshB,rfl⟩))))
    | generalize label prior earlier =>
      exact .inr (.inr (.inr (.inr (.inr (.inl ⟨label,prior,earlier,rfl⟩)))))
    | detach a b i j beforeI beforeJ left right =>
      exact .inr (.inr (.inr (.inr (.inr (.inr ⟨i,beforeI,j,beforeJ,by rw [left,right]⟩)))))

theorem nativeDerivable_eval (formula : V) :
    nativeDerivableDef.val.Evalb ![formula] ↔ ∃ book : V, NativeProof book formula := by
  have eval (f book line : V) :
      nativeLineDef.val.Eval (f :> book :> fun _ : Fin 1 => line) Empty.elim ↔ NativeLine book line f := by
    simpa only [Matrix.vec_single_eq_const] using nativeLine_eval f book line
  simp [nativeDerivableDef, lh_defined.iff, znth_defined.iff, eval, NativeProof,
    Matrix.comp_vecCons', Function.comp_def, eq_comm]

attribute [local irreducible] nativeDerivableDef

theorem nativeRefutable_eval :
    nativeRefutable.val.Evalb (![] : Fin 0 → V) ↔ ∃ book : V, NativeProof book 1 := by
  have evaluated : nativeRefutable.val.Evalb (![] : Fin 0 → V) ↔
      nativeDerivableDef.val.Evalb ![(1 : V)] := by
    simp [nativeRefutable, Semiformula.eval_substs, Function.comp_def, Matrix.vec_single_eq_const, numeral_eq_natCast]
  exact evaluated.trans (nativeDerivable_eval (1 : V))

attribute [local irreducible] nativeRefutable

theorem native_refutation_implies_halt [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (refutes : nativeRefutable.val.Evalb (![] : Fin 0 → V)) :
    (haltsDef literal).val.Evalb (![] : Fin 0 → V) := by
  obtain ⟨_, proof⟩ := nativeRefutable_eval.mp refutes
  exact literal_halts_of_native_refutation proof

/-- Nonhalting entails consistency of the coded native calculus in PA. -/
theorem native_nonhalting_implies_consistency :
    𝗣𝗔 ⊢ (∼(haltsDef literal).val) 🡒 ∼nativeRefutable.val := by
  apply Arithmetic.complete.{0} 𝗣𝗔 _
  intro M _ _
  have h : ¬ (haltsDef literal).val.Evalb (![] : Fin 0 → M) →
      ¬ nativeRefutable.val.Evalb (![] : Fin 0 → M) :=
    fun never proof => never (native_refutation_implies_halt proof)
  simpa only [models_iff, Semiformula.Realize, LogicalConnective.HomClass.map_imply,
    LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.arrow_eq, LogicalConnective.Prop.neg_eq] using h

end I0451.Arithmetization
