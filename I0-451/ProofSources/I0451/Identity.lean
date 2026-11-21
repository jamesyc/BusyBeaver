module
public import Std

/-! First-order formulas on a decoded membership domain.
An assignment can also vary in a single coordinate. -/

@[expose] public section
namespace I0451.Identity

abbrev Assignment (D : Type) := D → D

def replace {D : Type} [DecidableEq D] (s : Assignment D) (i x : D) : Assignment D :=
  fun k => if k = i then x else s k

/-- First-order membership and equality formulas with `n` free variable slots. The head slot in an
existential body is the newly bound variable. -/
inductive Formula : Nat → Type where
  | mem {n} (i k : Fin n) : Formula n
  | eq {n} (i k : Fin n) : Formula n
  | bot {n} : Formula n
  | imp {n} (a b : Formula n) : Formula n
  | ex {n} (a : Formula (n + 1)) : Formula n

def Formula.eval {D : Type} (E : D → D → Prop) :
    {n : Nat} → Formula n → (Fin n → D) → Prop
  | _, .mem i k, v => E (v i) (v k)
  | _, .eq i k, v => v i = v k
  | _, .bot, _ => False
  | _, .imp a b, v => a.eval E v → b.eval E v
  | _, .ex a, v => ∃ x, a.eval E (Fin.cases x v)

def Formula.negation {n : Nat} (p : Formula n) : Formula n := .imp p .bot

def Formula.conjunction {n : Nat} (p q : Formula n) : Formula n :=
  (Formula.imp p q.negation).negation

def Formula.universal {n : Nat} (p : Formula (n + 1)) : Formula n :=
  (Formula.ex p.negation).negation

@[simp] theorem Formula.eval_negation {D : Type} (E : D → D → Prop) {n : Nat}
    (p : Formula n) (v : Fin n → D) : p.negation.eval E v ↔ ¬p.eval E v :=
  Iff.rfl

@[simp] theorem Formula.eval_conjunction {D : Type} (E : D → D → Prop) {n : Nat}
    (p q : Formula n) (v : Fin n → D) :
    (p.conjunction q).eval E v ↔ p.eval E v ∧ q.eval E v := by
  classical
  simp [conjunction, eval]

@[simp] theorem Formula.eval_universal {D : Type} (E : D → D → Prop) {n : Nat}
    (p : Formula (n + 1)) (v : Fin n → D) :
    p.universal.eval E v ↔ ∀ x, p.eval E (Fin.cases x v) := by
  classical
  simp [universal, eval]

end I0451.Identity
