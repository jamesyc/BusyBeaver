module
public import Std
@[expose] public section
/-! Standalone exact209 mathematical definitions. The corresponding completed
Solution proves PalomarZF209.exact209Claim. This file and Solution are compiled
in separate environments; Solution must not import Challenge. -/
namespace PalomarZF209History
abbrev Row := Option (Bool × Bool × Nat)
def literalRows : List (Row × Row) := [
  (some (true, true, 1), some (true, true, 60)),
  (some (true, true, 81), some (true, true, 1)),
  (some (false, false, 2), some (true, false, 3)),
  (some (false, false, 4), some (true, false, 3)),
  (some (false, false, 6), some (true, false, 3)),
  (some (true, true, 7), some (false, false, 5)),
  (some (false, false, 9), some (true, false, 3)),
  (some (false, true, 7), some (false, true, 10)),
  (some (false, true, 13), some (true, true, 12)),
  (some (false, false, 14), some (true, false, 3)),
  (some (false, false, 15), some (false, true, 10)),
  (some (false, false, 25), some (true, true, 17)),
  (some (false, false, 78), some (true, false, 30)),
  (some (false, false, 11), some (false, true, 21)),
  (some (false, false, 22), some (true, false, 3)),
  (some (true, false, 2), some (false, false, 2)),
  (some (false, true, 23), some (false, true, 31)),
  (some (false, true, 83), some (false, false, 94)),
  (some (false, true, 27), some (true, true, 28)),
  (some (false, true, 29), some (true, true, 30)),
  (some (false, true, 23), some (false, true, 56)),
  (some (false, true, 32), some (true, true, 21)),
  (some (false, false, 33), some (true, false, 3)),
  (some (false, false, 34), some (false, true, 1)),
  (some (false, true, 35), some (true, true, 24)),
  (some (false, true, 120), some (true, true, 40)),
  (some (false, true, 37), some (false, false, 38)),
  (some (false, true, 39), some (true, true, 40)),
  (some (false, true, 41), some (true, true, 42)),
  (some (false, true, 43), some (true, true, 44)),
  (some (false, true, 20), some (true, true, 45)),
  (some (false, true, 46), some (true, true, 31)),
  (some (false, true, 31), some (true, true, 32)),
  (some (false, false, 68), some (true, false, 3)),
  (some (true, true, 34), some (true, false, 2)),
  (some (false, true, 48), some (true, true, 35)),
  (some (false, true, 27), some (true, true, 19)),
  (some (false, false, 11), some (false, true, 35)),
  (some (false, false, 5), some (true, false, 50)),
  (some (false, true, 23), some (false, true, 24)),
  (some (false, true, 12), some (false, false, 15)),
  (some (false, true, 52), some (true, true, 53)),
  (some (false, true, 54), some (true, true, 55)),
  (some (false, true, 23), some (false, true, 51)),
  (some (false, true, 57), some (true, true, 58)),
  (some (false, true, 59), some (false, false, 15)),
  (some (false, true, 24), some (true, true, 46)),
  (some (false, false, 34), some (false, true, 60)),
  (some (false, true, 15), some (true, true, 48)),
  (some (false, true, 62), some (true, true, 63)),
  (some (false, false, 38), some (true, false, 50)),
  (some (false, true, 21), some (true, true, 51)),
  (some (false, false, 11), some (false, true, 48)),
  (some (false, true, 57), some (false, false, 15)),
  (some (false, true, 64), some (true, true, 65)),
  (some (false, true, 58), some (true, true, 66)),
  (some (false, true, 51), some (true, true, 56)),
  (some (false, true, 47), some (false, true, 24)),
  (some (false, false, 27), some (true, false, 67)),
  (some (false, false, 101), some (true, false, 29)),
  (some (false, true, 0), some (true, true, 60)),
  (some (true, true, 123), some (true, false, 50)),
  (some (false, true, 69), some (true, true, 209)),
  (some (false, false, 124), some (true, true, 30)),
  (some (false, true, 39), some (true, true, 59)),
  (some (false, false, 78), some (true, true, 70)),
  (some (false, true, 52), some (true, false, 71)),
  (some (false, true, 72), some (true, true, 73)),
  (some (false, true, 68), some (true, true, 74)),
  (some (false, true, 75), some (true, true, 76)),
  (some (false, true, 78), some (true, false, 109)),
  (some (false, false, 97), some (true, true, 53)),
  (some (false, true, 47), some (false, true, 32)),
  (some (false, true, 80), some (false, false, 40)),
  (some (false, true, 49), some (true, true, 128)),
  (some (false, true, 126), some (true, true, 20)),
  (some (false, true, 100), some (true, true, 89)),
  (some (false, true, 91), some (true, true, 92)),
  (some (false, true, 72), some (true, true, 71)),
  (some (false, true, 90), some (true, true, 117)),
  (some (false, true, 94), some (true, true, 95)),
  (some (false, true, 61), some (false, true, 1)),
  (some (false, true, 26), some (true, true, 96)),
  (some (false, true, 88), some (true, true, 87)),
  (some (true, false, 98), some (true, false, 84)),
  (some (false, true, 18), some (true, true, 99)),
  (some (false, true, 57), some (true, true, 57)),
  (some (false, true, 115), some (true, true, 114)),
  (some (false, false, 25), some (true, true, 208)),
  (some (false, true, 94), some (false, false, 127)),
  (some (false, true, 101), some (true, true, 102)),
  (some (false, true, 66), some (true, true, 55)),
  (some (false, true, 54), some (true, true, 103)),
  (some (false, true, 20), some (true, true, 104)),
  (some (false, true, 20), some (false, false, 10)),
  (some (false, true, 58), some (true, true, 40)),
  (some (false, true, 105), some (true, true, 8)),
  (some (false, true, 90), some (true, true, 106)),
  (some (false, false, 127), some (false, false, 84)),
  (some (false, true, 107), some (true, true, 93)),
  (some (false, false, 108), some (false, false, 2)),
  (some (false, true, 37), some (true, true, 67)),
  (some (false, true, 58), some (true, true, 109)),
  (some (false, true, 58), some (true, true, 110)),
  (some (false, true, 65), some (false, false, 15)),
  (some (false, true, 13), some (true, true, 109)),
  (some (false, true, 20), some (true, true, 111)),
  (some (false, true, 112), some (true, false, 19)),
  (some (false, true, 29), some (true, true, 64)),
  (some (false, true, 37), some (true, false, 107)),
  (some (false, true, 119), some (false, false, 15)),
  (some (false, true, 113), some (false, false, 15)),
  (some (false, true, 23), some (false, true, 46)),
  (some (false, true, 47), some (false, true, 31)),
  (some (false, true, 69), some (true, true, 85)),
  (some (false, true, 124), some (true, true, 27)),
  (some (false, true, 120), some (true, true, 106)),
  (some (false, true, 93), some (true, true, 85)),
  (some (false, true, 82), some (true, true, 97)),
  (some (false, true, 86), some (true, true, 86)),
  (some (false, true, 16), some (true, false, 108)),
  (some (false, true, 69), some (true, true, 100)),
  (some (false, true, 95), some (true, true, 107)),
  (some (true, false, 38), some (true, false, 98)),
  (some (false, true, 79), some (true, true, 77)),
  (some (false, true, 118), some (true, true, 129)),
  (some (false, true, 43), some (true, true, 89)),
  (some (false, false, 5), some (false, false, 127)),
  (some (false, true, 125), some (true, true, 58)),
  (some (false, true, 11), some (true, true, 36)),
  (some (false, true, 18), some (true, true, 19)),
  (some (false, true, 77), some (true, true, 86)),
  (some (false, true, 85), some (true, true, 131)),
  (some (false, true, 130), some (true, true, 132)),
  (some (false, false, 159), some (true, true, 77)),
  (some (false, false, 169), some (true, true, 134)),
  (some (false, true, 18), some (true, true, 116)),
  (some (false, true, 136), some (true, true, 134)),
  (some (false, true, 134), some (true, true, 133)),
  (some (false, true, 57), some (true, true, 77)),
  (some (false, true, 18), some (true, true, 139)),
  (some (false, false, 197), some (true, true, 140)),
  (some (false, true, 140), some (true, true, 141)),
  (some (false, true, 138), some (true, true, 135)),
  (some (false, true, 137), some (true, true, 143)),
  (some (false, true, 136), some (true, true, 131)),
  (some (false, true, 130), some (true, true, 145)),
  (some (false, true, 132), some (true, true, 133)),
  (some (false, true, 145), some (true, true, 77)),
  (some (false, false, 147), some (true, false, 184)),
  (some (false, true, 149), some (true, true, 57)),
  (some (false, true, 130), some (true, true, 150)),
  (some (false, true, 148), some (true, true, 151)),
  (some (false, false, 174), some (true, true, 152)),
  (some (false, true, 146), some (true, true, 153)),
  (some (false, true, 144), some (true, true, 154)),
  (some (false, true, 135), some (true, true, 155)),
  (some (false, true, 124), some (true, true, 156)),
  (some (false, true, 77), some (true, true, 157)),
  (some (false, true, 158), some (true, true, 146)),
  (some (false, true, 136), some (true, false, 152)),
  (some (false, false, 184), some (true, true, 160)),
  (some (false, true, 138), some (true, true, 57)),
  (some (false, true, 161), some (true, true, 162)),
  (some (false, true, 163), some (true, true, 137)),
  (some (false, true, 164), some (true, true, 163)),
  (some (false, true, 159), some (true, true, 165)),
  (some (false, true, 85), some (true, true, 166)),
  (some (false, true, 142), some (true, true, 160)),
  (some (false, true, 167), some (true, true, 168)),
  (some (false, true, 130), some (true, true, 169)),
  (some (false, true, 63), some (true, true, 170)),
  (some (false, true, 57), some (true, true, 137)),
  (some (false, true, 147), some (true, true, 162)),
  (some (false, true, 172), some (true, true, 173)),
  (some (false, true, 171), some (true, true, 174)),
  (some (false, true, 175), some (true, true, 133)),
  (some (false, true, 133), some (true, true, 176)),
  (some (false, true, 160), some (true, true, 57)),
  (some (false, true, 130), some (true, true, 178)),
  (some (false, true, 179), some (true, true, 161)),
  (some (false, true, 148), some (true, true, 180)),
  (some (false, true, 151), some (true, true, 181)),
  (some (false, true, 153), some (true, true, 182)),
  (some (false, true, 139), some (true, true, 145)),
  (some (false, true, 137), some (true, true, 184)),
  (some (false, true, 136), some (true, true, 179)),
  (some (false, true, 140), some (true, true, 77)),
  (some (false, true, 187), some (true, true, 149)),
  (some (false, true, 186), some (true, true, 188)),
  (some (false, true, 136), some (true, true, 189)),
  (some (false, true, 190), some (true, true, 188)),
  (some (false, true, 185), some (true, true, 191)),
  (some (false, true, 183), some (true, true, 192)),
  (some (false, false, 197), some (true, true, 187)),
  (some (false, true, 77), some (true, true, 194)),
  (some (false, true, 132), some (true, true, 188)),
  (some (false, true, 195), some (true, true, 196)),
  (some (false, true, 193), some (true, true, 197)),
  (some (false, true, 194), some (true, true, 148)),
  (some (false, true, 141), some (true, true, 120)),
  (some (false, true, 121), some (false, false, 127)),
  (some (false, true, 122), some (true, true, 201)),
  (some (false, true, 121), some (true, true, 202)),
  (some (false, true, 200), some (true, true, 203)),
  (some (false, true, 199), some (true, true, 204)),
  (some (false, true, 186), some (true, true, 205)),
  (some (false, true, 198), some (true, true, 206)),
  (some (false, true, 177), some (true, true, 207))
]
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
/-- All 209 rows are fixed above. The initial state is 0, not a supplied parameter. -/
def Step (s t : Conf V) : Prop :=
 Valid E s ∧ Valid E t ∧ ∃ q : Fin 209, Numeral E q.val s.q ∧
 ∃ read write direction next,
 (if read then (literalRows.getD q.val (none,none)).2 else (literalRows.getD q.val (none,none)).1) = some (write,direction,next) ∧
 Move E read write direction next s t
/-- This finite condition matches no outgoing row: both entries of every
in-range row are defined. It requires a separate exact-row totality proof. -/
def Terminal (s : Conf V) : Prop := ∀ q : Fin 209, ¬ Numeral E q.val s.q
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
def NumericStep (before after : V) : Prop :=
 ∃ s t : Conf V, NumericConfCode E s before ∧ NumericConfCode E t after ∧ Step E s t
def RunEdge (initial next tail : V) : Prop :=
 (Empty E tail ∧ next = initial) ∨
 (¬ Empty E tail ∧ ∃ previous, ListHead E tail previous ∧ NumericStep E previous next)
/-- Preferred production-aligned representation. The iterator f is an
internal set function on successor(code), NOT an external recursive function.
Every nonzero tail encountered before code steps has a correct run edge. -/
def LinkedRun (initial code : V) : Prop :=
 NatObject E initial ∧ NatObject E code ∧ ¬ Empty E code ∧
 ∃ zero domain f, Empty E zero ∧ Succ E code domain ∧ FunctionOn E f domain ∧
 At E f zero code ∧ At E f code zero ∧
 (∀ i x, E i domain → At E f i x → NatObject E x) ∧
 ∀ i, E i code → ∃ j x y, Succ E i j ∧ At E f i x ∧ At E f j y ∧
 ListTail E x y ∧ (Empty E x ∨ ∃ a b, ListHead E x a ∧ ListTail E x b ∧ RunEdge E initial a b)
/-- Primary proposed Challenge operational predicate. The equivalence with
production physicalHalts is a NEW proof obligation, not assumed here. -/
def InternalLinkedHalts : Prop :=
 ∃ zero hist last, ∃ (t : Conf V), Empty E zero ∧ LinkedRun E zero hist ∧
 ListHead E hist last ∧ NumericConfCode E t last ∧ Valid E t ∧ Terminal E t
end InternalSets
end PalomarZF209History

namespace PalomarZF209
inductive Formula where
 | bot : Formula
 | mem : Nat → Nat → Formula
 | eq : Nat → Nat → Formula
 | and : Formula → Formula → Formula
 | or : Formula → Formula → Formula
 | imp : Formula → Formula → Formula
 | all : Formula → Formula
 | ex : Formula → Formula
 deriving DecidableEq, Repr

def lift (σ : Nat → Nat) : Nat → Nat
 | 0 => 0
 | n+1 => σ n + 1

def rename (σ : Nat → Nat) : Formula → Formula
 | .bot => .bot
 | .mem i j => .mem (σ i) (σ j)
 | .eq i j => .eq (σ i) (σ j)
 | .and a b => .and (rename σ a) (rename σ b)
 | .or a b => .or (rename σ a) (rename σ b)
 | .imp a b => .imp (rename σ a) (rename σ b)
 | .all a => .all (rename (lift σ) a)
 | .ex a => .ex (rename (lift σ) a)


def shift (a:Formula) := rename Nat.succ a
def substMap (t:Nat) : Nat→Nat | 0=>t | n+1=>n
def subst (t:Nat) (a:Formula) := rename (substMap t) a

def Bound : Formula → Nat → Prop
  | .bot, _ => True
  | .mem i j, n => i < n ∧ j < n
  | .eq i j, n => i < n ∧ j < n
  | .and p q, n => Bound p n ∧ Bound q n
  | .or p q, n => Bound p n ∧ Bound q n
  | .imp p q, n => Bound p n ∧ Bound q n
  | .all p, n => Bound p (n+1)
  | .ex p, n => Bound p (n+1)


universe u
/-- Interpretation of a de Bruijn assignment after pushing an eigenvariable. -/
def pushValue {α : Type u} (s : Nat → α) (x : α) : Nat → α
  | 0 => x
  | n + 1 => s n

def eval {α : Type u} (mem : α → α → Prop) : Formula → (Nat → α) → Prop
  | .bot, _ => False
  | .mem i j, s => mem (s i) (s j)
  | .eq i j, s => s i = s j
  | .and p q, s => eval mem p s ∧ eval mem q s
  | .or p q, s => eval mem p s ∨ eval mem q s
  | .imp p q, s => eval mem p s → eval mem q s
  | .all p, s => ∀ x, eval mem p (pushValue s x)
  | .ex p, s => ∃ x, eval mem p (pushValue s x)


abbrev Context := List Formula

def ContextSub (Γ Δ : Context) : Prop := ∀ a, a ∈ Γ → a ∈ Δ
inductive Row where
 | seq : Context → Formula → Row
 | branches : Context → Formula → Formula → Formula → Row
 deriving DecidableEq, Repr


def shiftContext (Γ:Context):=Γ.map shift

inductive ND : Row → Prop where
 | ctx {Γ a} : a ∈ Γ → ND (.seq Γ a)
 | pc (Γ a b) : ND (.seq Γ (.imp (.imp (.imp a b) a) a))
 | ii {Γ a b} : ND (.seq (a :: Γ) b) → ND (.seq Γ (.imp a b))
 | ie {Γ a b} : ND (.seq Γ (.imp a b)) → ND (.seq Γ a) → ND (.seq Γ b)
 | exp {Γ a} : ND (.seq Γ .bot) → ND (.seq Γ a)
 | ci {Γ a b} : ND (.seq Γ a) → ND (.seq Γ b) → ND (.seq Γ (.and a b))
 | ce1 {Γ a b} : ND (.seq Γ (.and a b)) → ND (.seq Γ a)
 | ce2 {Γ a b} : ND (.seq Γ (.and a b)) → ND (.seq Γ b)
 | di1 {Γ a b} : ND (.seq Γ a) → ND (.seq Γ (.or a b))
 | di2 {Γ a b} : ND (.seq Γ b) → ND (.seq Γ (.or a b))
 | branchPair {Γ a b c} : ND (.seq (a :: Γ) c) → ND (.seq (b :: Γ) c) → ND (.branches Γ a b c)
 | de {Γ a b c} : ND (.seq Γ (.or a b)) → ND (.branches Γ a b c) → ND (.seq Γ c)
 | wk {Γ Δ a} : ContextSub Γ Δ → ND (.seq Γ a) → ND (.seq Δ a)
 | allI {Γ a} : ND (.seq (shiftContext Γ) a) → ND (.seq Γ (.all a))
 | allE {Γ a} (t : Nat) : ND (.seq Γ (.all a)) → ND (.seq Γ (subst t a))
 | exI {Γ a} (t : Nat) : ND (.seq Γ (subst t a)) → ND (.seq Γ (.ex a))
 | exE {Γ a c} : ND (.seq Γ (.ex a)) → ND (.seq (a :: shiftContext Γ) (shift c)) → ND (.seq Γ c)


def fixedRefl : Formula := (.all (.eq 0 0))

def fixedSym : Formula := (.all (.all (.imp (.eq 1 0) (.eq 0 1))))

def fixedTrans : Formula := (.all (.all (.all (.imp (.eq 2 1) (.imp (.eq 1 0) (.eq 2 0))))))

def fixedEqElem : Formula := (.all (.all (.all (.all (.imp (.eq 3 1) (.imp (.eq 2 0) (.imp (.mem 3 2) (.mem 1 0))))))))

def fixedExt : Formula := (.all (.all (.imp (.all (.imp (.mem 0 2) (.mem 0 1))) (.imp (.all (.imp (.mem 0 1) (.mem 0 2))) (.eq 1 0)))))

def fixedEmpty : Formula := (.ex (.all (.imp (.mem 0 1) (.bot))))

def fixedPair : Formula := (.all (.all (.ex (.all (.and (.imp (.mem 0 1) (.or (.eq 0 3) (.eq 0 2))) (.imp (.or (.eq 0 3) (.eq 0 2)) (.mem 0 1)))))))

def fixedUnion : Formula := (.all (.ex (.all (.and (.imp (.mem 0 1) (.ex (.and (.mem 0 3) (.mem 1 0)))) (.imp (.ex (.and (.mem 0 3) (.mem 1 0))) (.mem 0 1))))))

def fixedPower : Formula := (.all (.ex (.all (.and (.imp (.mem 0 1) (.all (.imp (.mem 0 1) (.mem 0 3)))) (.imp (.all (.imp (.mem 0 1) (.mem 0 3))) (.mem 0 1))))))

def fixedOmega : Formula := (.ex (.and (.and (.ex (.and (.all (.imp (.mem 0 1) (.bot))) (.mem 0 1))) (.all (.imp (.mem 0 1) (.ex (.and (.all (.and (.imp (.mem 0 1) (.or (.mem 0 2) (.eq 0 2))) (.imp (.or (.mem 0 2) (.eq 0 2)) (.mem 0 1)))) (.mem 0 2)))))) (.all (.imp (.and (.ex (.and (.all (.imp (.mem 0 1) (.bot))) (.mem 0 1))) (.all (.imp (.mem 0 1) (.ex (.and (.all (.and (.imp (.mem 0 1) (.or (.mem 0 2) (.eq 0 2))) (.imp (.or (.mem 0 2) (.eq 0 2)) (.mem 0 1)))) (.mem 0 2)))))) (.all (.imp (.mem 0 2) (.mem 0 1)))))))

def fixedFoundation : Formula := (.all (.imp (.ex (.mem 0 1)) (.ex (.and (.mem 0 1) (.all (.imp (.mem 0 1) (.imp (.mem 0 2) (.bot))))))))


def sourceIff (a b : Formula) := Formula.and (.imp a b) (.imp b a)
def separationFormula (body : Formula) := Formula.all (.ex (.all
 (sourceIff (.mem 0 1) (.and (.mem 0 2) body))))
def functionalityFormula (a b : Formula) := Formula.all (.all (.all
 (.imp a (.imp b (.eq 1 0)))))
def replacementFormula (a b c : Formula) := Formula.imp (functionalityFormula a b)
 (.all (.ex (.all (sourceIff (.mem 0 1) (.ex (.and (.mem 0 3) c))))))
def allPrefix : Nat → Formula → Formula
 | 0, a => a
 | n+1, a => .all (allPrefix n a)

def sepIndex (i : Nat) := if i=0 then 0 else i+2
def repAIndex (i : Nat) := if i=0 then 2 else if i=1 then 1 else i+1
def repBIndex (i : Nat) := if i=0 then 2 else if i=1 then 0 else i+1
def repCIndex (i : Nat) := if i=0 then 0 else if i=1 then 1 else i+2

def separationSchema (n : Nat) (phi : Formula) := allPrefix n (separationFormula (rename sepIndex phi))
def replacementSchema (n : Nat) (phi : Formula) := allPrefix n
 (replacementFormula (rename repAIndex phi) (rename repBIndex phi) (rename repCIndex phi))


/-- All fixed axioms, including logical equality, omega, and foundation. -/
def FixedAxiom (p:Formula):Prop:=
 p=fixedRefl ∨ p=fixedSym ∨ p=fixedTrans ∨ p=fixedEqElem ∨ p=fixedExt ∨
 p=fixedEmpty ∨ p=fixedPair ∨ p=fixedUnion ∨ p=fixedPower ∨ p=fixedOmega ∨ p=fixedFoundation
/-- Full standard schemas, with arbitrary finite parameter lists. -/
def Axiom (p:Formula):Prop:= FixedAxiom p ∨
 (∃ n body,Bound body (n+1) ∧ p=separationSchema n body) ∨
 (∃ n body,Bound body (n+2) ∧ p=replacementSchema n body)
def Provable (p:Formula):Prop:=∃Γ:Context,(∀q,q∈Γ→Axiom q) ∧ ND (.seq Γ p)
def Consistent:Prop:=¬Provable .bot
def Closed (p:Formula):Prop:=Bound p 0
def Neg (p:Formula):Formula:=.imp p .bot
/-- Nonemptiness is separately required at every quantified model use. -/
def Model {V:Type} (E:V→V→Prop):Prop:=∀p,Axiom p→∀s:Nat→V,eval E p s
end PalomarZF209

namespace PalomarZF209
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
def ArithTerm.bound : ArithTerm→Nat→Prop
 | .zero,_ | .one,_=>True
 | .var i,n=>i<n
 | .add p q,n | .mul p q,n=>p.bound n ∧ q.bound n
def SigmaFormula.bound : SigmaFormula→Nat→Prop
 | .atom p q _ _,n=>p.bound n ∧ q.bound n
 | .conj p q,n | .disj p q,n=>p.bound n ∧ q.bound n
 | .exists_ p,n=>p.bound (n+1)
 | .forallLt t p,n=>t.bound n ∧ p.bound (n+1)
def ArithTerm.natValue : ArithTerm→(Nat→Nat)→Nat
 | .zero,_=>0 | .one,_=>1 | .var i,s=>s i
 | .add p q,s=>p.natValue s+q.natValue s
 | .mul p q,s=>p.natValue s*q.natValue s
def SigmaFormula.natEval : SigmaFormula→(Nat→Nat)→Prop
 | .atom p q eq pos,s=>
   let P:=if eq then p.natValue s=q.natValue s else p.natValue s<q.natValue s
   if pos then P else ¬P
 | .conj p q,s=>p.natEval s ∧ q.natEval s
 | .disj p q,s=>p.natEval s ∨ q.natEval s
 | .exists_ p,s=>∃x:Nat,p.natEval (pushValue s x)
 | .forallLt b p,s=>∀x:Nat,x<b.natValue s→p.natEval (pushValue s x)
open PalomarZF209History
/-- Fully relational evaluation, including arithmetic internal to a ZF model. -/
def ArithTerm.graph {V:Type} (E:V→V→Prop):ArithTerm→(Nat→V)→V→Prop
 | .zero,_,z=>Numeral E 0 z
 | .one,_,z=>Numeral E 1 z
 | .var i,s,z=>NatObject E z ∧ z=s i
 | .add p q,s,z=>∃a b,p.graph E s a ∧ q.graph E s b ∧ Add E a b z
 | .mul p q,s,z=>∃a b,p.graph E s a ∧ q.graph E s b ∧ Mul E a b z
def SigmaFormula.internalEval {V:Type} (E:V→V→Prop):SigmaFormula→(Nat→V)→Prop
 | .atom p q eq pos,s=>∃a b,p.graph E s a ∧ q.graph E s b ∧
   (if pos then (if eq then a=b else E a b) else ¬(if eq then a=b else E a b))
 | .conj p q,s=>p.internalEval E s ∧ q.internalEval E s
 | .disj p q,s=>p.internalEval E s ∨ q.internalEval E s
 | .exists_ p,s=>∃x:V,NatObject E x ∧ p.internalEval E (pushValue s x)
 | .forallLt b p,s=>∃bound,b.graph E s bound ∧
   ∀x:V,NatObject E x→E x bound→p.internalEval E (pushValue s x)
/-- Correct arithmetic meaning in ALL ZF models, not just well-founded or
omega-standard models. Both syntax objects are fixed finite external syntax. -/
def RepresentsArithmetic (φ:SigmaFormula) (ψ:Formula):Prop:=
 Closed ψ ∧ ∀(V:Type) (E:V→V→Prop),Nonempty V→Model E→
 ∀(s env:Nat→V),(∀i,NatObject E (env i))→(eval E ψ s ↔ φ.internalEval E env)
/-- The full Sigma1 class, independent of the chosen halting sentence. Its
 equivalence to the production hypothesis is an outstanding Solution theorem. -/
def ArithmeticSigma1Sound:Prop:=
 ∀φ:SigmaFormula,φ.bound 0→∀ψ:Formula,RepresentsArithmetic φ ψ→
 Provable ψ→∀s:Nat→Nat,φ.natEval s
/-- Uniform meaning is intended as a CONCLUSION of the compared theorem,
not as a premise that lets a caller supply an unspecified machine predicate. -/
def Represents209 (H:Formula):Prop:=
 Closed H ∧ ∀(V:Type) (E:V→V→Prop),Nonempty V→Model E→
 ∀s:Nat→V,eval E H s ↔ InternalLinkedHalts E
/-- Proposed full statement of record. This is a transparent proposition, not
an axiom or a theorem claiming the new Challenge interface is already proved. -/
def Exact209Claim:Prop:=∃H:Formula,Represents209 H ∧
 (Consistent→¬Provable (Neg H)) ∧
 (ArithmeticSigma1Sound→(¬Provable H) ∧ (¬Provable (Neg H)))
end PalomarZF209


namespace PalomarZF209
/-- STATEMENT-ONLY CHALLENGE PLACEHOLDER, as permitted by Palomar CONTRIBUTING
section 2.3. This file is not proof evidence. The separate Solution module exports
this exact theorem with a complete kernel-checked proof and no sorryAx or custom
axioms. Solution never imports Challenge; Comparator checks the two environments. -/
theorem exact209Claim : Exact209Claim := by
  sorry
end PalomarZF209
