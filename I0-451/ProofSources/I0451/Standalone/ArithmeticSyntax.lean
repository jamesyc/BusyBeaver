module
public import Std

/-! Standalone arithmetic syntax and its relational interpretation
in an arbitrary membership model. Adapted from ZF207's generic
arithmetic definitions. -/
@[expose] public section
namespace I0451.Standalone

def pushValue {V : Type} (s : Nat → V) (x : V) (i : Nat) : V :=
  Nat.casesOn i x s

section InternalSets
variable {V : Type} (E : V → V → Prop)
def Empty (a : V) : Prop := ∀ x, ¬ E x a
def Succ (a b : V) : Prop := ∀ x, E x b ↔ E x a ∨ x = a
def Pair (a b p : V) : Prop := ∀ x, E x p ↔ x = a ∨ x = b
def OrderedPair (a b p : V) : Prop :=
 ∃ aa ab, Pair E a a aa ∧ Pair E a b ab ∧ Pair E aa ab p
def At (f x y : V) : Prop := ∃ p, E p f ∧ OrderedPair E x y p
/-- The function and its domain are elements of the model, not external maps. -/
def FunctionOn (f domain : V) : Prop :=
 (∀ x, E x domain → ∃ y, At E f x y ∧ ∀ z, At E f x z → z = y) ∧
 (∀ p, E p f → ∃ x y, E x domain ∧ OrderedPair E x y p)
def Inductive (a : V) : Prop :=
 (∃ z, Empty E z ∧ E z a) ∧ ∀ x, E x a → ∃ y, Succ E x y ∧ E y a
def Omega (w : V) : Prop :=
 Inductive E w ∧ ∀ a, Inductive E a → ∀ x, E x w → E x a
/-- Meaningful on actual ZF models, where a unique omega exists. -/
def NatObject (x : V) : Prop := ∃ w, Omega E w ∧ E x w
def Numeral (n : Nat) : V → Prop :=
  Nat.rec (motive := fun _ => V → Prop) (Empty E)
    (fun _ previous x => ∃ y, previous y ∧ Succ E y x) n

/-- Internal finite recursion, including nonstandard finite lengths. -/
def Add (a b c : V) : Prop :=
 NatObject E a ∧ NatObject E b ∧ NatObject E c ∧
 ∃ z domain f, Empty E z ∧ Succ E b domain ∧ FunctionOn E f domain ∧
 At E f z a ∧ At E f b c ∧
 (∀ i x, E i domain → At E f i x → NatObject E x) ∧
 ∀ i, E i b → ∃ j x y, Succ E i j ∧ At E f i x ∧ At E f j y ∧ Succ E x y
def Mul (a b c : V) : Prop :=
 NatObject E a ∧ NatObject E b ∧ NatObject E c ∧
 ∃ z domain f, Empty E z ∧ Succ E b domain ∧ FunctionOn E f domain ∧
 At E f z z ∧ At E f b c ∧
 (∀ i x, E i domain → At E f i x → NatObject E x) ∧
 ∀ i, E i b → ∃ j x y, Succ E i j ∧ At E f i x ∧ At E f j y ∧ Add E x a y
end InternalSets
inductive ArithTerm where
 | zero | one
 | var (index:Nat)
 | add (left right:ArithTerm)
 | mul (left right:ArithTerm)
inductive SigmaFormula where
 | atom (left right:ArithTerm) (equality positive:Bool)
 | conj (left right:SigmaFormula)
 | disj (left right:SigmaFormula)
 | exists_ (body:SigmaFormula)
 | forallLt (bound:ArithTerm) (body:SigmaFormula)
def ArithTerm.bound (t : ArithTerm) : Nat → Prop :=
  ArithTerm.rec (motive := fun _ => Nat → Prop) (fun _ => True) (fun _ => True)
    (fun i n => i < n) (fun _ _ a b n => a n ∧ b n) (fun _ _ a b n => a n ∧ b n) t

def SigmaFormula.bound (p : SigmaFormula) : Nat → Prop :=
  SigmaFormula.rec (motive := fun _ => Nat → Prop)
    (fun a b _ _ n => a.bound n ∧ b.bound n)
    (fun _ _ a b n => a n ∧ b n) (fun _ _ a b n => a n ∧ b n)
    (fun _ a n => a (n + 1)) (fun t _ a n => t.bound n ∧ a (n + 1)) p

noncomputable def ArithTerm.natValue (t : ArithTerm) : (Nat → Nat) → Nat :=
  ArithTerm.rec (motive := fun _ => (Nat → Nat) → Nat)
    (fun _ => 0) (fun _ => 1) (fun i s => s i)
    (fun _ _ a b s => a s + b s) (fun _ _ a b s => a s * b s) t

def SigmaFormula.natEval (p : SigmaFormula) : (Nat → Nat) → Prop :=
  SigmaFormula.rec (motive := fun _ => (Nat → Nat) → Prop)
    (fun a b eq pos s =>
      let P := if eq then a.natValue s = b.natValue s else a.natValue s < b.natValue s
      if pos then P else ¬ P)
    (fun _ _ a b s => a s ∧ b s) (fun _ _ a b s => a s ∨ b s)
    (fun _ a s => ∃ x : Nat, a (pushValue s x))
    (fun t _ a s => ∀ x : Nat, x < t.natValue s → a (pushValue s x)) p

/-- Relational arithmetic over an arbitrary membership model. -/
def ArithTerm.graph {V : Type} (E : V → V → Prop) (t : ArithTerm) : (Nat → V) → V → Prop :=
  ArithTerm.rec (motive := fun _ => (Nat → V) → V → Prop)
    (fun _ z => Numeral E 0 z) (fun _ z => Numeral E 1 z)
    (fun i s z => NatObject E z ∧ z = s i)
    (fun _ _ a b s z => ∃ x y, a s x ∧ b s y ∧ Add E x y z)
    (fun _ _ a b s z => ∃ x y, a s x ∧ b s y ∧ Mul E x y z) t

def SigmaFormula.internalEval {V : Type} (E : V → V → Prop) (p : SigmaFormula) : (Nat → V) → Prop :=
  SigmaFormula.rec (motive := fun _ => (Nat → V) → Prop)
    (fun a b eq pos s => ∃ x y, a.graph E s x ∧ b.graph E s y ∧
      (if pos then (if eq then x = y else E x y) else ¬ (if eq then x = y else E x y)))
    (fun _ _ a b s => a s ∧ b s) (fun _ _ a b s => a s ∨ b s)
    (fun _ a s => ∃ x : V, NatObject E x ∧ a (pushValue s x))
    (fun t _ a s => ∃ bound, t.graph E s bound ∧
      ∀ x : V, NatObject E x → E x bound → a (pushValue s x)) p

end I0451.Standalone
