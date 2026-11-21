module
public import I0451.Commands.ExtraCheck

/-! The checked EXTRA result determines both closed axiom codes and the
register contract for the command boundary. -/
@[expose] public section
namespace I0451.Runtime

open M6.Source.Cantor

private theorem option_contract {S : Type} (valid : S → Prop) [∀ x, Decidable (valid x)]
    (answer : Option S) (fallback : S)
    (check : answer.any (fun r => decide (valid r)) = true) :
    answer = some (answer.getD fallback) ∧ valid (answer.getD fallback) := by
  cases answer with
  | none => contradiction
  | some r => exact ⟨rfl, of_decide_eq_true check⟩

theorem extra_lookup : extraResolved = some extraSymbols ∧ ExtraPost extraSymbols :=
  option_contract ExtraPost extraResolved (symbolicInput true) extraBlock_checked

def literalFoundationCode : Nat := literalFoundationTerm.eval (fun _ => 0)
def literalBerkeleyCode : Nat := literalBerkeleyTerm.eval (fun _ => 0)

theorem literalFoundationCode_eq :
    literalFoundationCode = literalFoundationTerm.eval (fun _ => 0) := rfl

theorem literalBerkeleyCode_eq :
    literalBerkeleyCode = literalBerkeleyTerm.eval (fun _ => 0) := rfl

theorem literalFoundationTerm_closed : literalFoundationTerm.closed = true := extra_lookup.2.2.1

theorem literalBerkeleyTerm_closed : literalBerkeleyTerm.closed = true := extra_lookup.2.1

def extraResult (s : Registers) : Registers :=
  putRegister (putRegister (putRegister (putRegister
    (putRegister s topWff literalBerkeleyCode) wffStack
      (pair literalFoundationCode (pair (s topWff) (s wffStack)))) parameterOne 0)
    parameterTwo 0) axiomIndex 0

private theorem exec_of_resolution {r initial : SymbolicRegisters} {blocks : List ClosedBlock}
    {fuel : Nat} {entry : Cursor}
    (check : (assembleWith blocks fuel (.branch entry)).bind (symbolicRun · initial) = some r)
    (s : Registers) : Executes (.branch entry) (initial.eval s) .normal (r.eval s) := by
  obtain ⟨ops, plan, ran⟩ := Option.bind_eq_some_iff.mp check
  exact assemble_sound plan (symbolicRun_sound ran s)

theorem extraSymbolic_exec (s : Registers) :
    Executes (.branch extraCursor) (extraInput.eval s) .normal (extraSymbols.eval s) :=
  exec_of_resolution (blocks := extraBlocks) (fuel := 140) extra_lookup.1 s

private theorem extraPost_eval (r : SymbolicRegisters) (checked : ExtraPost r) (s : Registers)
    (firstZero : s scratchOne = 0) (secondZero : s scratchTwo = 0) :
    r.eval s =
      putRegister (putRegister (putRegister (putRegister
        (putRegister s topWff ((r topWff).eval (fun _ => 0))) wffStack
          (pair ((r wffStack).left.eval (fun _ => 0)) (pair (s topWff) (s wffStack))))
        parameterOne 0) parameterTwo 0) axiomIndex 0 := by
  obtain ⟨topClosed, headClosed, retained, next, queue, a, b, ax, sa, sb⟩ := checked
  have tail : (r wffStack).right.eval s = pair (s topWff) (s wffStack) := by
    rw [retained]
    rfl
  have fs := (r wffStack).left.eval_closed headClosed s (fun _ => 0)
  have bs := (r topWff).eval_closed topClosed s (fun _ => 0)
  have stack : (r wffStack).eval s =
      pair ((r wffStack).left.eval (fun _ => 0)) (pair (s topWff) (s wffStack)) := by
    rw [← tail, ← fs]
    simp only [CounterExpr.eval_left, CounterExpr.eval_right, pair_decode]
  funext j
  have indexes : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega
  rcases indexes with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (r nextProof).eval s = s nextProof
    rw [next]
    rfl
  · exact bs
  · exact stack
  · change (r axiomIndex).eval s = 0
    rw [ax]
    rfl
  · change (r parameterOne).eval s = 0
    rw [a]
    rfl
  · change (r parameterTwo).eval s = 0
    rw [b]
    rfl
  · change (r scratchOne).eval s = s scratchOne
    rw [sa, firstZero]
    rfl
  · change (r scratchTwo).eval s = s scratchTwo
    rw [sb, secondZero]
    rfl
  · change (r proofList).eval s = s proofList
    rw [queue]
    rfl

theorem literal_extra (s : Registers) (axiomZero : s axiomIndex = 0)
    (firstZero : s scratchOne = 0) (secondZero : s scratchTwo = 0) :
    Executes (.branch extraCursor) s .normal (extraResult s) := by
  have ran := extraSymbolic_exec s
  simp only [extraInput, SymbolicRegisters.eval_set, eval_symbolicInput s firstZero secondZero, CounterExpr.eval] at ran
  rw [← axiomZero, putRegister_read] at ran
  have eq : extraSymbols.eval s = extraResult s :=
    extraPost_eval extraSymbols extra_lookup.2 s firstZero secondZero
  rw [eq] at ran
  exact ran

end I0451.Runtime
