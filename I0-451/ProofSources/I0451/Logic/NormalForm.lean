module
public import I0451.Logic.Formula

/-! A small, sound check for equality of first-order formulas up to
capture-free renaming, negation normal form, and reassociation.
Irreflexivity lets a self-membership serve as false. -/
@[expose] public section
namespace I0451.Logic

inductive Variable where
  | bound (index : Nat)
  | free (label : Nat)
  deriving DecidableEq, Repr

def Variable.raise : Variable → Variable
  | .bound i => .bound (i + 1)
  | .free n => .free n

def Variable.locate : List Nat → Nat → Variable
  | [], n => .free n
  | x :: rest, n => if n = x then .bound 0 else (locate rest n).raise

def Variable.value {V : Type} (free bound : Nat → V) : Variable → V
  | .bound i => bound i
  | .free n => free n

def pushValue {V : Type} (value : V) (rest : Nat → V) : Nat → V
  | 0 => value
  | i + 1 => rest i

theorem Variable.value_raise {V : Type} (free bound : Nat → V) (v : V) (x : Variable) :
    x.raise.value free (pushValue v bound) = x.value free bound := by
  cases x <;> rfl

def namedEnvironment {V : Type} (scope : List Nat) (free bound : Nat → V) : Nat → V :=
  fun i => (Variable.locate scope i).value free bound

theorem namedEnvironment_cons {V : Type} (scope : List Nat) (free bound : Nat → V)
    (x : Nat) (v : V) :
    namedEnvironment (x :: scope) free (pushValue v bound) =
      assign (namedEnvironment scope free bound) x v := by
  funext i
  by_cases h : i = x
  · simp [namedEnvironment, Variable.locate, Variable.value, assign, pushValue, h]
  · simp [namedEnvironment, Variable.locate, assign, h, Variable.value_raise]

inductive NormalForm where
  | constant (value : Bool)
  | member (positive : Bool) (x y : Variable)
  | equal (positive : Bool) (x y : Variable)
  | quantify (universal : Bool) (body : NormalForm)
  | conjunction (a b : NormalForm)
  | disjunction (a b : NormalForm)
  deriving DecidableEq, Repr

def signed (positive : Bool) (p : Prop) : Prop := if positive then p else ¬ p

def NormalForm.eval {V : Type} (E : V → V → Prop) (free bound : Nat → V) : NormalForm → Prop
  | .constant truth => truth = true
  | .member positive x y => signed positive (E (x.value free bound) (y.value free bound))
  | .equal positive x y => signed positive (x.value free bound = y.value free bound)
  | .quantify true body => ∀ v, body.eval E free (pushValue v bound)
  | .quantify false body => ∃ v, body.eval E free (pushValue v bound)
  | .conjunction a b => a.eval E free bound ∧ b.eval E free bound
  | .disjunction a b => a.eval E free bound ∨ b.eval E free bound

def NormalForm.joinAnd : NormalForm → NormalForm → NormalForm
  | .constant p, right => if p then right else .constant false
  | left, .constant p => if p then left else .constant false
  | .conjunction left right, last => .conjunction left (joinAnd right last)
  | left, right => .conjunction left right

def NormalForm.joinOr : NormalForm → NormalForm → NormalForm
  | .constant p, right => if p then .constant true else right
  | left, .constant p => if p then .constant true else left
  | .disjunction left right, last => .disjunction left (joinOr right last)
  | left, right => .disjunction left right

theorem NormalForm.eval_joinAnd {V : Type} (E : V → V → Prop) (free bound : Nat → V)
    (a b : NormalForm) :
    (a.joinAnd b).eval E free bound ↔ a.eval E free bound ∧ b.eval E free bound := by
  induction a generalizing b <;> cases b <;> simp [joinAnd, eval, *, and_assoc]
  all_goals split <;> simp_all [eval]

theorem NormalForm.eval_joinOr {V : Type} (E : V → V → Prop) (free bound : Nat → V)
    (a b : NormalForm) :
    (a.joinOr b).eval E free bound ↔ a.eval E free bound ∨ b.eval E free bound := by
  induction a generalizing b <;> cases b <;> simp [joinOr, eval, *, or_assoc]
  all_goals split <;> simp_all [eval]

def Formula.normalize (scope : List Nat) (positive : Bool) : Formula → NormalForm
  | .truth => .constant positive
  | .mem a b =>
    if a = b then .constant (!positive)
    else .member positive (Variable.locate scope a) (Variable.locate scope b)
  | .equal a b => .equal positive (Variable.locate scope a) (Variable.locate scope b)
  | .all x body => .quantify positive (body.normalize (x :: scope) positive)
  | .imp a b =>
    if positive then (a.normalize scope false).joinOr (b.normalize scope true)
    else (a.normalize scope true).joinAnd (b.normalize scope false)

theorem Formula.eval_normalize {V : Type} (E : V → V → Prop) (irrefl : ∀ x, ¬ E x x)
    (f : Formula) (scope : List Nat) (positive : Bool) (free bound : Nat → V) :
    (f.normalize scope positive).eval E free bound ↔ signed positive (f.eval E (namedEnvironment scope free bound)) := by
  induction f generalizing scope positive bound with
  | truth => cases positive <;> simp [Formula.normalize, Formula.eval, NormalForm.eval, signed]
  | imp a b ia ib =>
    cases positive <;>
      simp only [Formula.normalize, Bool.false_eq_true, ite_false, ite_true, NormalForm.eval_joinAnd,
        NormalForm.eval_joinOr, ia, ib, Formula.eval, signed] <;>
      apply Classical.byCases (p := a.eval E (namedEnvironment scope free bound)) <;>
      intro h <;> simp [h]
  | mem a b =>
    by_cases same : a = b
    · subst b
      cases positive <;>
        simp [Formula.normalize, Formula.eval, NormalForm.eval, signed, irrefl]
    · simp [Formula.normalize, Formula.eval, NormalForm.eval, same, namedEnvironment]
  | equal a b => rfl
  | all x body ih =>
    cases positive
    · simp only [Formula.normalize, Formula.eval, NormalForm.eval, signed, Bool.false_eq_true,
        ite_false, Classical.not_forall]
      exact exists_congr fun v => by
        rw [ih, namedEnvironment_cons]
        rfl
    · simp only [Formula.normalize, Formula.eval, NormalForm.eval, signed, ite_true]
      exact forall_congr' fun v => by
        rw [ih, namedEnvironment_cons]
        rfl

theorem Formula.equiv_of_normalize {a b : Formula}
    (same : a.normalize [] true = b.normalize [] true)
    {V : Type} (E : V → V → Prop) (irrefl : ∀ x, ¬ E x x) (s : Nat → V) :
    a.eval E s ↔ b.eval E s := by
  have ax := a.eval_normalize E irrefl [] true s s
  have bx := b.eval_normalize E irrefl [] true s s
  change _ ↔ a.eval E s at ax
  change _ ↔ b.eval E s at bx
  exact ax.symm.trans (same ▸ bx)

end I0451.Logic
