module
public import I3_380.Logic.ExpandedSubstitution
public import I3_380.Logic.SetScope
@[expose] public section

namespace PalomarI3380.Logic.Expanded

variable {V : Type} {E G : V → V → Prop}

/-- Include a formula of the membership language in the named language. -/
def Formula.membership : Logic.Formula → Formula V
  | .bot => .bot
  | .mem i j => .mem (.variable i) (.variable j)
  | .eq i j => .eq (.variable i) (.variable j)
  | .and a b => .and (membership a) (membership b)
  | .or a b => .or (membership a) (membership b)
  | .imp a b => .imp (membership a) (membership b)
  | .all a => .all (membership a)
  | .ex a => .ex (membership a)

theorem membership_scope (p : Logic.Formula) {n : Nat} (h : Logic.Bound p n) :
    Bound (Formula.membership (V := V) p) n := by
  induction p generalizing n with
  | bot => trivial
  | mem | eq => exact h
  | and p q ip iq | or p q ip iq | imp p q ip iq => exact ⟨ip h.1,iq h.2⟩
  | all p ih | ex p ih => exact ih h

theorem membership_eval (p : Logic.Formula) (s : Nat → V) :
    eval E G (Formula.membership p) s ↔ Logic.eval E p s := by
  induction p generalizing s <;> simp only [Formula.membership,eval,Logic.eval,Argument.value, *]

/-- Instantiate a builder template at arbitrary named or bound arguments. -/
def applyTemplate (body : SetFormula) (arity : Nat) (args : Nat → Argument V) : Formula V :=
  (Formula.membership (body arity)).substitute (fun i => args (arity - (i+1)))

theorem applyTemplate_scope (body : SetFormula) {arity n : Nat}
    (scope : SetFormula.Scoped arity body) (args : Nat → Argument V)
    (bounded : ∀ i, i < arity → (args i).bound n) :
    Bound (applyTemplate body arity args) n :=
  substitute_bound _ (membership_scope _ scope) (fun i hi => bounded _ (by omega))

theorem applyTemplate_eval (body : SetFormula) {arity : Nat}
    (scope : SetFormula.Scoped arity body) (args : Nat → Argument V) (env : Nat → V) :
    eval E G (applyTemplate body arity args) env ↔
      SetFormula.holds E body arity (fun i => (args i).value env) (env 0) := by
  rw [applyTemplate,eval_substitute,membership_eval]
  apply Logic.eval_congr_bound _ scope
  intro i hi
  simp [SetFormula.assignment,hi]

theorem Argument.bound_shift {a : Argument V} {n : Nat} (h : a.bound n) :
    (a.rename Nat.succ).bound (n+1) :=
  arg_rename_bound h (fun _ h => Nat.succ_lt_succ h)

theorem Argument.value_shift (a : Argument V) (env : Nat → V) (x : V) :
    (a.rename Nat.succ).value (pushValue env x) = a.value env := by
  cases a <;> rfl

end PalomarI3380.Logic.Expanded
