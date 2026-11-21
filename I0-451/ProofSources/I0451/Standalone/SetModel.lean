module
public import I0451.Logic.NamedProofs
public import I0451.Standalone.ArithmeticSyntax

/-! The membership-model presentation of the Challenge theory.
It uses the full separation and replacement schemata with parameters. -/
@[expose] public section
namespace I0451.Standalone

open I0451.Logic (NamedFormula)

/-- Update the value assigned to a single variable label. -/
def assign {V : Type} (s : Nat → V) (label : Nat) (x : V) : Nat → V :=
  fun i => if i = label then x else s i

/-- Truth of a membership formula with labeled variables. -/
def eval {V : Type} (E : V → V → Prop) (s : Nat → V) (p : NamedFormula) : Prop :=
  NamedFormula.rec (motive := fun _ => (Nat → V) → Prop)
    (fun _ => True) (fun _ => False)
    (fun a b env => E (env a) (env b)) (fun a b env => env a = env b)
    (fun _ _ a b env => a env → b env)
    (fun x _ a env => ∀ v, a (assign env x v)) p s

/-- ZF interpreted over a carrier and a binary membership relation. -/
structure Model {V : Type} (E : V → V → Prop) : Prop where
  empty : ∃ z : V, ∀ a : V, ¬ E a z
  extensionality : ∀ a b : V, (∀ x : V, E x a ↔ E x b) → a = b
  pairing : ∀ a b : V, ∃ z : V, ∀ x : V, E x z ↔ x = a ∨ x = b
  union : ∀ a : V, ∃ z : V, ∀ x : V, E x z ↔ ∃ y, E y a ∧ E x y
  power : ∀ a : V, ∃ z : V, ∀ x : V, E x z ↔ ∀ u : V, E u x → E u a
  infinity : ∃ I : V, (∀ z : V, (∀ x : V, ¬ E x z) → E z I) ∧
    ∀ x : V, E x I → ∀ y : V, (∀ z : V, E z y ↔ z = x ∨ E z x) → E y I
  foundation : ∀ a : V, (∃ x : V, E x a) → ∃ x : V, E x a ∧ ∀ y : V, E y x → ¬ E y a
  separation : ∀ (p : NamedFormula) (s : Nat → V) (label : Nat) (A : V),
    ∃ B : V, ∀ y : V, E y B ↔ E y A ∧ eval E (assign s label y) p
  replacement : ∀ (p : NamedFormula) (s : Nat → V) (i j : Nat),
    let R (x y : V) := eval E (assign (assign s i x) j y) p
    (∀ x : V, ∃ y : V, R x y ∧ ∀ z : V, R x z → z = y) →
      ∀ A : V, ∃ B : V, ∀ y : V, E y B ↔ ∃ x : V, E x A ∧ R x y

/-- Choice as existence of a selector set for every set of disjoint nonempty sets. -/
def Choice {V : Type} (E : V → V → Prop) : Prop :=
  ∀ F : V, (∀ A : V, E A F → ∃ x, E x A) →
    (∀ A B : V, E A F → E B F → (∃ x, E x A ∧ E x B) → A = B) →
      ∃ C : V, ∀ A : V, E A F → ∃ x : V, E x C ∧ E x A ∧
        ∀ y : V, E y C → E y A → y = x

end I0451.Standalone
