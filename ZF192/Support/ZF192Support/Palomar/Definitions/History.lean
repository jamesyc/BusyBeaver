module
public import Std
@[expose] public section
/-! Shared syntax for arithmetic and finite coding in ZF models. -/
namespace PalomarZF192Arithmetic
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
structure Conf (V : Type) where
 q : V
 left : V
 right : V
def Valid (s : Conf V) : Prop := NatObject E s.q ∧ NatObject E s.left ∧ NatObject E s.right
/-- Literal table movement. true means right; false means left. -/
def Move (read write direction : Bool) (next : Nat) (s t : Conf V) : Prop :=
 ∃ r, BitCons E read r s.right ∧ Numeral E next t.q ∧
 if direction then BitCons E write s.left t.left ∧ t.right = r
 else ∃ l bit middle, BitCons E bit l s.left ∧ t.left = l ∧
   BitCons E write r middle ∧ BitCons E bit middle t.right
/-- Cantor graph, matching the production equation
2*z=(a+b)*(a+b+1)+2*b. All witnesses are model objects. -/
def Cantor (a b z : V) : Prop :=
 NatObject E a ∧ NatObject E b ∧ NatObject E z ∧
 ∃ two sum next product twiceB twiceZ total,
 Numeral E 2 two ∧ Add E a b sum ∧ Succ E sum next ∧
 Mul E sum next product ∧ Mul E two b twiceB ∧
 Mul E two z twiceZ ∧ Add E product twiceB total ∧ twiceZ = total
def ListCons (a b c : V) : Prop := ∃ p, Cantor E a b p ∧ Succ E p c
def ListHead (x a : V) : Prop :=
 (Empty E x ∧ Empty E a) ∨ ∃ b, ListCons E a b x
def ListTail (x b : V) : Prop :=
 (Empty E x ∧ Empty E b) ∨ ∃ a, ListCons E a b x
def NumericConfCode (s : Conf V) (code : V) : Prop :=
 ∃ lr, Cantor E s.left s.right lr ∧ Cantor E s.q lr code
end InternalSets
end PalomarZF192Arithmetic
