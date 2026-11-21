module
public import I0451.ArithmeticFormulaBlocks
public import I0451.Commands.ExtraCommand

/-! Exact AX and EXTRA register updates. The latter emits the standard
numerals for the two closed expressions in the original machine. -/
@[expose] public section
namespace I0451.Runtime

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Arithmetization I0451.Logic

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def modelNeg (a : V) : V := modelImp a 1

noncomputable def modelEncoding : AxiomEncoding V :=
  ⟨modelImp, modelTag 1, modelTag 2, modelTag 3,
    fun a b => modelNeg (modelTag 2 a (modelNeg b)),
    fun a b => modelNeg (modelImp a (modelNeg b))⟩

noncomputable def modelAxiomResult (s : Fin 9 → V) : Fin 9 → V :=
  let a := s parameterOne
  let b := s parameterTwo + cantorLeft (s proofList)
  let c := s axiomIndex
  let more := cantorRight (s proofList)
  let heads := modelEncoding.heads a b c (cantorLeft more)
  let saved := cantor (s topWff) (s wffStack)
  let stack := heads.foldr cantor (cantor (modelEncoding.all a (s parameterTwo)) saved)
  let guarded := if c = a ∨ c = b then 0 else modelEncoding.bundle a b c
  putRegister (putRegister (putRegister (putRegister (putRegister
    (putRegister s topWff guarded) wffStack stack) proofList (cantorRight more))
    parameterOne 0) parameterTwo 0) axiomIndex 0

private theorem CounterExpr.modelEval_fold_pairs (s : Fin 9 → V) (forms : List CounterExpr) (tail : CounterExpr) :
    (forms.foldr CounterExpr.pairWith tail).modelEval s =
      (forms.map (CounterExpr.modelEval s)).foldr cantor (tail.modelEval s) := by
  induction forms with
  | nil => rfl
  | cons f fs ih => simp [ih]

private theorem CounterExpr.modelEval_negation (s : Fin 9 → V) (a : CounterExpr) :
    (symbolicNeg a).modelEval s = modelNeg (a.modelEval s) := by
  simp [symbolicNeg, modelNeg, modelTag, modelEval]

private theorem modelEval_symbolicEncoding (s : Fin 9 → V) (a b : CounterExpr) :
    (symbolicEncoding.imp a b).modelEval s = modelEncoding.imp (a.modelEval s) (b.modelEval s) ∧
    (symbolicEncoding.mem a b).modelEval s = modelEncoding.mem (a.modelEval s) (b.modelEval s) ∧
    (symbolicEncoding.all a b).modelEval s = modelEncoding.all (a.modelEval s) (b.modelEval s) ∧
    (symbolicEncoding.equal a b).modelEval s = modelEncoding.equal (a.modelEval s) (b.modelEval s) ∧
    (symbolicEncoding.ex a b).modelEval s = modelEncoding.ex (a.modelEval s) (b.modelEval s) ∧
    (symbolicEncoding.and a b).modelEval s = modelEncoding.and (a.modelEval s) (b.modelEval s) := by
  simp [symbolicEncoding, modelEncoding, CounterExpr.modelEval_negation, modelTag]

theorem modelEval_heads (s : Fin 9 → V) (a b c x : CounterExpr) :
    (symbolicEncoding.heads a b c x).map (CounterExpr.modelEval s) =
      modelEncoding.heads (a.modelEval s) (b.modelEval s) (c.modelEval s) (x.modelEval s) := by
  simp only [AxiomEncoding.heads, List.map_cons, List.map_nil,
    (modelEval_symbolicEncoding s _ _).1, (modelEval_symbolicEncoding s _ _).2.1,
    (modelEval_symbolicEncoding s _ _).2.2.1, (modelEval_symbolicEncoding s _ _).2.2.2.1,
    (modelEval_symbolicEncoding s _ _).2.2.2.2.1]

theorem modelEval_bundle (s : Fin 9 → V) (a b c : CounterExpr) :
    (symbolicEncoding.bundle a b c).modelEval s =
      modelEncoding.bundle (a.modelEval s) (b.modelEval s) (c.modelEval s) := by
  simp only [AxiomEncoding.bundle, AxiomEncoding.containerCode, AxiomEncoding.extensionalityCode,
    AxiomEncoding.collectionCode, AxiomEncoding.subset, (modelEval_symbolicEncoding s _ _).1,
    (modelEval_symbolicEncoding s _ _).2.1, (modelEval_symbolicEncoding s _ _).2.2.1,
    (modelEval_symbolicEncoding s _ _).2.2.2.1, (modelEval_symbolicEncoding s _ _).2.2.2.2.1,
    (modelEval_symbolicEncoding s _ _).2.2.2.2.2]

theorem modelEval_axiomPost (sym : SymbolicRegisters) (s : Fin 9 → V) :
    (axiomPost sym).modelEval s = modelAxiomResult (sym.modelEval s) := by
  simp only [axiomPost, modelAxiomResult, SymbolicRegisters.modelEval_set,
    CounterExpr.modelEval_fold_pairs, modelEval_heads, modelEval_bundle,
    (modelEval_symbolicEncoding s _ _).2.2.1,
    CounterExpr.modelEval_pairWith, CounterExpr.modelEval_left, CounterExpr.modelEval_right,
    CounterExpr.modelEval_plus, CounterExpr.modelEval]
  by_cases first : (sym axiomIndex).modelEval s = (sym parameterOne).modelEval s <;>
    by_cases second : (sym axiomIndex).modelEval s =
      (sym parameterTwo).modelEval s + cantorLeft ((sym proofList).modelEval s) <;>
    simp [SymbolicRegisters.modelEval, first, second]

theorem model_axiom (s : Fin 9 → V) (oneZero : s scratchOne = 0) (twoZero : s scratchTwo = 0) :
    ModelEffect (.branch axCursor) s .normal (modelAxiomResult s) := by
  have eq := modelEval_axiomPost (symbolicInput true) s
  rw [modelEval_symbolicInput s oneZero twoZero] at eq
  simpa only [eq] using model_axiom_expression s oneZero twoZero

theorem CounterExpr.modelEval_cast (e : CounterExpr) (s : Registers) :
    e.modelEval (fun j => (s j : V)) = (e.eval s : V) := by
  induction e with
  | input r | number n => rfl
  | add a b ha hb => simp [modelEval, eval, ha, hb, Nat.cast_add]
  | pair a b ha hb => simp [modelEval, eval, ha, hb, cantor_cast]
  | first p ih => simp [modelEval, eval, ih, cantorLeft_cast]
  | second p ih => simp [modelEval, eval, ih, cantorRight_cast]
  | scaled x ih => simp [modelEval, eval, ih, Nat.cast_mul]
  | ifEqual a b y n ha hb hy hn =>
    by_cases same : a.eval s = b.eval s <;>
      simp [modelEval, eval, ha, hb, hy, hn, same]

theorem CounterExpr.modelEval_closed (e : CounterExpr) (closed : e.closed = true) (s t : Fin 9 → V) :
    e.modelEval s = e.modelEval t := by
  induction e with
  | input i => simp [CounterExpr.closed] at closed
  | number n => rfl
  | add a b ha hb | pair a b ha hb =>
    simp only [CounterExpr.closed, Bool.and_eq_true] at closed
    simp only [modelEval, ha closed.1, hb closed.2]
  | first a ih | second a ih | scaled a ih =>
    simp only [modelEval, ih closed]
  | ifEqual a b y n ha hb hy hn =>
    simp only [CounterExpr.closed, Bool.and_eq_true] at closed
    simp only [modelEval, ha closed.1.1.1, hb closed.1.1.2, hy closed.1.2, hn closed.2]

noncomputable def modelExtraResult (s : Fin 9 → V) : Fin 9 → V :=
  putRegister (putRegister (putRegister (putRegister
    (putRegister s topWff (literalBerkeleyCode : V)) wffStack
      (cantor (literalFoundationCode : V) (cantor (s topWff) (s wffStack))))
    parameterOne 0) parameterTwo 0) axiomIndex 0

private theorem modelEval_extraPost (r : SymbolicRegisters) (checked : ExtraPost r) (s : Fin 9 → V)
    (oneZero : s scratchOne = 0) (twoZero : s scratchTwo = 0) :
    r.modelEval s =
      putRegister (putRegister (putRegister (putRegister
        (putRegister s topWff ((r topWff).eval (fun _ => 0) : V)) wffStack
          (cantor ((r wffStack).left.eval (fun _ => 0) : V) (cantor (s topWff) (s wffStack))))
        parameterOne 0) parameterTwo 0) axiomIndex 0 := by
  obtain ⟨topClosed, headClosed, retained, next, queue, a, b, ax, sa, sb⟩ := checked
  have tail : (r wffStack).right.modelEval s = cantor (s topWff) (s wffStack) := by
    rw [retained]
    rfl
  have fs := ((r wffStack).left.modelEval_closed headClosed s (fun j => ((0 : Nat) : V))).trans
    (CounterExpr.modelEval_cast _ _)
  have bs := ((r topWff).modelEval_closed topClosed s (fun j => ((0 : Nat) : V))).trans
    (CounterExpr.modelEval_cast _ _)
  have stack : (r wffStack).modelEval s =
      cantor ((r wffStack).left.eval (fun _ => 0) : V) (cantor (s topWff) (s wffStack)) := by
    rw [← tail, ← fs]
    simp only [CounterExpr.modelEval_left, CounterExpr.modelEval_right]
    exact (cantor_encode_decode ((r wffStack).modelEval s)).symm
  funext j
  rcases index_cases j with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · change (r nextProof).modelEval s = s nextProof
    rw [next]
    rfl
  · exact bs
  · exact stack
  · change (r axiomIndex).modelEval s = 0
    rw [ax]
    rfl
  · change (r parameterOne).modelEval s = 0
    rw [a]
    rfl
  · change (r parameterTwo).modelEval s = 0
    rw [b]
    rfl
  · change (r scratchOne).modelEval s = s scratchOne
    rw [sa, oneZero]
    rfl
  · change (r scratchTwo).modelEval s = s scratchTwo
    rw [sb, twoZero]
    rfl
  · change (r proofList).modelEval s = s proofList
    rw [queue]
    rfl

theorem model_extra (s : Fin 9 → V) (modeZero : s axiomIndex = 0)
    (oneZero : s scratchOne = 0) (twoZero : s scratchTwo = 0) :
    ModelEffect (.branch extraCursor) s .normal (modelExtraResult s) := by
  have resolved : ((assembleWith extraBlocks 140 (.branch extraCursor)).bind
      (symbolicRun · extraInput)) = some extraSymbols := extra_lookup.1
  obtain ⟨ops, plan, proof⟩ := Option.bind_eq_some_iff.mp resolved
  have ran := model_assemble_sound (fun _ found => model_extraBlocks found) plan proof s
  simp only [extraInput, SymbolicRegisters.modelEval_set, modelEval_symbolicInput s oneZero twoZero,
    CounterExpr.modelEval, Nat.cast_zero] at ran
  rw [← modeZero, putRegister_read] at ran
  have result : extraSymbols.modelEval s = modelExtraResult s :=
    modelEval_extraPost extraSymbols extra_lookup.2 s oneZero twoZero
  rwa [result] at ran

end I0451.Runtime
