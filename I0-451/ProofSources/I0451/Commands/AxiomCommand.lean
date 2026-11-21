module
public import I0451.Commands.Symbolic
public import I0451.Logic.AxiomBundle

/-! AX's symbolic postcondition uses the same formula constructors as
the semantic proof. The audit checks the postcondition against the
literal graph with arbitrary inputs. -/
@[expose] public section
namespace I0451.Runtime

open I0451.Logic M6.Source.Cantor

def symbolicNeg (x : CounterExpr) : CounterExpr := CounterExpr.tag 0 x (.number 1)

def symbolicEncoding : AxiomEncoding CounterExpr :=
  ⟨CounterExpr.tag 0, CounterExpr.tag 1, CounterExpr.tag 2, CounterExpr.tag 3,
    fun a b => symbolicNeg (CounterExpr.tag 2 a (symbolicNeg b)),
    fun a b => symbolicNeg (CounterExpr.tag 0 a (symbolicNeg b))⟩

def axiomPost (s : SymbolicRegisters) : SymbolicRegisters :=
  let a := s parameterOne
  let c := s axiomIndex
  let y := (s proofList).left
  let x := (s proofList).right.left
  let remainder := (s proofList).right.right
  let b := (s parameterTwo).plus y
  let saved := (s topWff).pairWith (s wffStack)
  let generalization := symbolicEncoding.all a (s parameterTwo)
  let heads := symbolicEncoding.heads a b c x
  let stack := heads.foldr CounterExpr.pairWith (generalization.pairWith saved)
  let compound := symbolicEncoding.bundle a b c
  let guarded := CounterExpr.ifEqual c a (.number 0)
    (.ifEqual c b (.number 0) compound)
  ((((s.set topWff guarded).set wffStack stack).set proofList remainder).set parameterOne (.number 0))
    |>.set parameterTwo (.number 0) |>.set axiomIndex (.number 0)

theorem CounterExpr.eval_fold_pairs (s : Registers) (forms : List CounterExpr) (tail : CounterExpr) :
    (forms.foldr CounterExpr.pairWith tail).eval s =
      (forms.map (CounterExpr.eval s)).foldr M6.Source.Cantor.pair (tail.eval s) := by
  induction forms with
  | nil => rfl
  | cons f fs ih => simp [ih]

def storeOf (s : Registers) : ProofStore :=
  ⟨s topWff, s wffStack, s parameterOne, s parameterTwo⟩

def axiomResult (s : Registers) : Registers :=
  let y := decode (s proofList)
  let x := decode y.2
  let after := runAxioms (s axiomIndex) y.1 x.1 (storeOf s)
  putRegister (putRegister (putRegister (putRegister
    (putRegister (putRegister s topWff after.top) wffStack after.stack) proofList x.2)
      parameterOne after.operand) parameterTwo after.cache) axiomIndex 0

private theorem encoding_imp (s : Registers) (a b : CounterExpr) :
    (symbolicEncoding.imp a b).eval s = imp (a.eval s) (b.eval s) := by
  simp only [symbolicEncoding, CounterExpr.eval_tag, numericTag, Nat.add_zero, imp]

private theorem encoding_mem (s : Registers) (a b : CounterExpr) :
    (symbolicEncoding.mem a b).eval s = mem (a.eval s) (b.eval s) :=
  CounterExpr.eval_tag 1 a b s

private theorem encoding_equal (s : Registers) (a b : CounterExpr) :
    (symbolicEncoding.equal a b).eval s = equal (a.eval s) (b.eval s) :=
  CounterExpr.eval_tag 3 a b s

private theorem encoding_all (s : Registers) (a b : CounterExpr) :
    (symbolicEncoding.all a b).eval s = all (a.eval s) (b.eval s) :=
  CounterExpr.eval_tag 2 a b s

private theorem eval_negation (s : Registers) (a : CounterExpr) :
    (symbolicNeg a).eval s = neg (a.eval s) := by
  simp only [symbolicNeg, CounterExpr.eval_tag, numericTag, Nat.add_zero, neg, imp, CounterExpr.eval]

private theorem encoding_ex (s : Registers) (a b : CounterExpr) :
    (symbolicEncoding.ex a b).eval s = ex (a.eval s) (b.eval s) := by
  change (symbolicNeg (symbolicEncoding.all a (symbolicNeg b))).eval s = _
  simp only [eval_negation, encoding_all, ex]

private theorem encoding_and (s : Registers) (a b : CounterExpr) :
    (symbolicEncoding.and a b).eval s = Logic.and (a.eval s) (b.eval s) := by
  change (symbolicNeg (symbolicEncoding.imp a (symbolicNeg b))).eval s = _
  simp only [eval_negation, encoding_imp, Logic.and]

private theorem eval_heads (s : Registers) (a b c x : CounterExpr) :
    (symbolicEncoding.heads a b c x).map (CounterExpr.eval s) =
      heads (a.eval s) (b.eval s) (c.eval s) (x.eval s) := by
  simp only [AxiomEncoding.heads, heads, List.map_cons, List.map_nil,
    encoding_imp, encoding_mem, encoding_equal, encoding_ex, encoding_all]

private theorem eval_bundle (s : Registers) (a b c : CounterExpr) :
    (symbolicEncoding.bundle a b c).eval s = bundle (a.eval s) (b.eval s) (c.eval s) := by
  simp only [AxiomEncoding.bundle, AxiomEncoding.containerCode, AxiomEncoding.extensionalityCode,
    AxiomEncoding.collectionCode, AxiomEncoding.subset, bundle, containerCode, extensionalityCode,
    collectionCode, subset, encoding_imp, encoding_mem, encoding_equal, encoding_ex,
    encoding_all, encoding_and]

private theorem eval_number (s : Registers) (n : Nat) : (CounterExpr.number n).eval s = n := rfl

private theorem eval_conditional (s : Registers) (a b y n : CounterExpr) :
    (CounterExpr.ifEqual a b y n).eval s =
      if a.eval s = b.eval s then y.eval s else n.eval s := rfl

private theorem check_guard (a b c n : Nat) :
    (if c = a then 0 else if c = b then 0 else n) =
      if c = a ∨ c = b then 0 else n := by
  by_cases x : c = a <;> by_cases y : c = b <;> simp [x, y]

theorem eval_axiomPost (sym : SymbolicRegisters) (input : Registers) :
    (axiomPost sym).eval input = axiomResult (sym.eval input) := by
  simp only [axiomPost, axiomResult, SymbolicRegisters.eval_set,
    CounterExpr.eval_fold_pairs, eval_heads, eval_bundle, encoding_all, eval_conditional,
    eval_number, check_guard, CounterExpr.eval_pairWith, CounterExpr.eval_left,
    CounterExpr.eval_right, CounterExpr.eval_plus, storeOf, runAxioms]
  rfl

end I0451.Runtime
