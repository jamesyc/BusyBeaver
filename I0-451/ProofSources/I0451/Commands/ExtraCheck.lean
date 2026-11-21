module
public import I0451.Commands.FunctionValue

/-! EXTRA has no formula operands. Its two emitted codes are recovered
symbolically and the stack effect is checked on arbitrary inputs. -/
@[expose] public section
namespace I0451.Runtime

open M6.Source.Cantor

def CounterExpr.closed : CounterExpr → Bool
  | .input _ => false
  | .number _ => true
  | .add a b | .pair a b => a.closed && b.closed
  | .first x | .second x | .scaled x => x.closed
  | .ifEqual a b y n => a.closed && b.closed && y.closed && n.closed

theorem CounterExpr.eval_closed (e : CounterExpr) (closed : e.closed = true) (s t : Registers) :
    e.eval s = e.eval t := by
  induction e with
  | input i => simp [CounterExpr.closed] at closed
  | number n => rfl
  | add a b ha hb | pair a b ha hb =>
    simp only [CounterExpr.closed, Bool.and_eq_true] at closed
    simp only [CounterExpr.eval, ha closed.1, hb closed.2]
  | first a ih | second a ih | scaled a ih =>
    simp only [CounterExpr.eval, ih closed]
  | ifEqual a b y n ha hb hy hn =>
    simp only [CounterExpr.closed, Bool.and_eq_true] at closed
    simp only [CounterExpr.eval, ha closed.1.1.1, hb closed.1.1.2, hy closed.1.2, hn closed.2]

def extraInput : SymbolicRegisters := (symbolicInput true).set axiomIndex (.number 0)

def extraResolved : Option SymbolicRegisters :=
  (assembleWith extraBlocks 140 (.branch extraCursor)).bind fun ops =>
    symbolicRun ops extraInput

def extraSymbols : SymbolicRegisters := extraResolved.getD (symbolicInput true)
def literalFoundationTerm : CounterExpr := (extraSymbols wffStack).left
def literalBerkeleyTerm : CounterExpr := extraSymbols topWff

def ExtraPost (r : SymbolicRegisters) : Prop :=
  (r topWff).closed = true ∧ (r wffStack).left.closed = true ∧
  (r wffStack).right = CounterExpr.pair (.input topWff) (.input wffStack) ∧
  r nextProof = .input nextProof ∧ r proofList = .input proofList ∧
  r parameterOne = .number 0 ∧ r parameterTwo = .number 0 ∧ r axiomIndex = .number 0 ∧
  r scratchOne = .number 0 ∧ r scratchTwo = .number 0

instance (r : SymbolicRegisters) : Decidable (ExtraPost r) := by
  unfold ExtraPost
  infer_instance

set_option maxRecDepth 16000 in
set_option maxHeartbeats 14000000 in
theorem extraBlock_checked : extraResolved.any (fun r => decide (ExtraPost r)) = true := by
  decide +kernel

end I0451.Runtime
