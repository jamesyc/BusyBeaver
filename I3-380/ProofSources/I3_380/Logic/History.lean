module
public import I3_380.Literal
@[expose] public section

namespace PalomarI3380.Logic.Internal

/-! A run is a function graph indexed by the model's finite ordinals. -/

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
def Numeral : Nat → V → Prop
 | 0, x => Empty E x
 | n + 1, x => ∃ y, Numeral n y ∧ Succ E y x
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
/-- y = bit + 2*x, using arithmetic internal to the set model. -/
def BitCons (bit : Bool) (x y : V) : Prop :=
 ∃ b two twice, Numeral E (if bit then 1 else 0) b ∧ Numeral E 2 two ∧
 Mul E two x twice ∧ Add E b twice y
structure Configuration (V : Type) where
  state : V
  left : V
  right : V

/-- Triple `(state, (left, right))` of internal natural numbers. -/
def ConfigurationCode (c : Configuration V) (code : V) : Prop :=
  NatObject E c.state ∧ NatObject E c.left ∧ NatObject E c.right ∧
    ∃ tapes, OrderedPair E c.left c.right tapes ∧ OrderedPair E c.state tapes code

def Move (read write right : Bool) (next : Nat) (s t : Configuration V) : Prop :=
  ∃ tail, BitCons E read tail s.right ∧ Numeral E next t.state ∧
    if right then BitCons E write s.left t.left ∧ t.right = tail
    else ∃ left head middle, BitCons E head left s.left ∧ t.left = left ∧
      BitCons E write tail middle ∧ BitCons E head middle t.right

def LiteralStep (s t : Configuration V) : Prop :=
  ∃ q : Fin 380, Numeral E q.val s.state ∧ ∃ read : Bool,
    let row := literal[2 * q.val + (if read then 1 else 0)]?.getD 0
    Move E read (row / 2 % 2 == 1) (row % 2 == 1) (row / 4) s t

/-- A model-internal finite history of the exact table from blank to halt.
The length, all indices, and every tape value belong to the model's `ω`. -/
def Halts : Prop :=
  ∃ n domain history zero start finish,
    NatObject E n ∧ Succ E n domain ∧ FunctionOn E history domain ∧ Empty E zero ∧
      ConfigurationCode E ⟨zero, zero, zero⟩ start ∧ At E history zero start ∧
      At E history n finish ∧
      (∃ final, ConfigurationCode E final finish ∧ Numeral E 380 final.state) ∧
      ∀ i, E i n → ∃ next s t before after, Succ E i next ∧
        At E history i before ∧ At E history next after ∧
        ConfigurationCode E s before ∧ ConfigurationCode E t after ∧ LiteralStep E s t

end InternalSets
end PalomarI3380.Logic.Internal
