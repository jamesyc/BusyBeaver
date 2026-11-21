module
public import Std

/-! A binary, two-way-infinite tape. Each side of the head is a stack of
bits encoded little-endian. The omitted high bits of either stack are all
zero. The left stack starts immediately to the left of the head, and the
right stack starts at the head. -/

@[expose] public section
namespace I0451

/-- Rows are base-2048 digits, ordered by state and read bit starting
with the least significant digit. Zero means no row. A move is a digit
`1 + 4*q + 2*d + b`, writing bit `b` and entering state `q`.
Direction `d = 1` moves right. -/
abbrev Table := Nat

structure Config where
  state : Nat
  left : Nat
  right : Nat
  deriving DecidableEq, Repr

def bit (n : Nat) : Bool := n % 2 == 1

def push (b : Bool) (tail : Nat) : Nat := b.toNat + 2 * tail

def digit (table : Table) (index : Nat) : Nat :=
  table / 2048 ^ index % 2048

def row (table : Table) (q : Nat) (read : Bool) : Nat :=
  digit table (2 * q + read.toNat)

/-- Apply a known transition code to the current tape. -/
def move (code : Nat) (left right : Nat) : Config :=
  if bit (code / 2) then
    ⟨code / 4, push (bit code) left, right / 2⟩
  else
    ⟨code / 4, left / 2, push (bit left) (push (bit code) (right / 2))⟩

def step (table : Table) (c : Config) : Option Config :=
  match row table c.state (bit c.right) with
  | 0 => none
  | code + 1 => some (move code c.left c.right)

def run (table : Table) : Nat → Config → Option Config
  | 0, c => some c
  | k + 1, c => (step table c).bind (run table k)

def blank (state : Nat) : Config := ⟨state, 0, 0⟩

/-- A run halts when it reaches the first configuration with no next move. -/
def Halts (table : Table) (initial : Config) : Prop :=
  ∃ n c, run table n initial = some c ∧ step table c = none

def literal : Table := 0xea0fb13252f8070be105ad2c0c722858ebe54fe0863f806fb229bdf7a163de1baf7415fdc8d6e722cfdc1b6f6c54bda944d4a15fda0ccf664ffd91b0f602abd78aef5c2e3d68d1f5855366178f56617d50e4f5269fd386cf4c153d28b4f481a7d18c5f44477d08baf4034bcf8fff3c2e7ce8dbf3832fcd868d7634fcd0e2f3235bcc196f2c3a7ca962f1a1a7ca0fbf26343c9190f202a398856f1e4c3c718cf182c3c5867f14503768b47125cfc4109e0c3a7c3944f0c617c2857f0860b688d6f04603c00f6efe5f7be944eee0bfb68ece2213b13231ef85974c0f4ee82ebbd843ef42a734148d9a4c3b80f3ef20bf8a960e922abbc176eec1fb6992aeea5cfb9934ee44cbb896fede41fb716ce2043fb60ecd565abb5068ed259fb3965eca2c3870d2ec858ba6069ec4583b0068dda2a35595e5ae15faf0b4eba4efae054eb650bad0caeb255fab955de6553aa152d981a7a90cbea253f3514fde745da7844e9c32fa694be962cfa5148c8a31ba40ebe8e517a2934e8850ba1140e8032f9f856e7c2eb9e93bd303b39d8e4d7232b9d0b2c8a4e19c068e6e2a79b134e684cb990a9cd04c3980ece5e1b3970bae5a36b9612ae544a37e06ce5016f93904e4c48f8f869e4a3c79206ce4646f3b0f4e4410f9091fe3e4778e91be363878d118e300bf8b900d4e32f8b0d2e2a13b20840e2844b660c0e2415f8890fe1e3672210d61a42f5a0f4e1631385067caa2ab848a4e103ef83905cd034734067db237b828a6e083ef5d8ece063d381100caa3ff7f8fdcae1537e8b9cec2e77e068df63d35e8b9df43e37c0e1c883db7b0f4de73c9610f1de23675d855de03bb2b8d0ddc3b3598ebd7638b6885bd621532e0d6dd63a7748b0dd01a771869dce397728e2dc638f718e1dc232b700decd41a76f0d1dba2e336868d561136dcda5b33616c0d6dac0cf6a8d3da632f34069da42c35d8d0da033b6706cd98333660cbd9632764869d9031b630bbd8a2c3620a2d000c761857d542e75a0b9ca41a73b06cd8330160012c282fb5f0bcd782e75d868d742e35c06cd6e1b35b0b4d682cb590b0cce04b580a4c6815f5746ccd21a3570accd0157560aad542a3540a6d3207f530a4cda1fb07aa3d461372703bf8816b510a0d400c704099c529473b075cb2a7b14a9dcee2734e09ac4d2674c841c52a5f4b81fd2c14b14a3fca40ef1323ed2a0ef07a93c4d24941891c4c8bb27866c528bb48817d2023b47017c5a10714a8cd0e22f3388ad140c71348850421f07a86d0c21342082d0420329051c5293b4007e4fc1f307a714e209d1347b4dd17311073cf61173d02ecf207f3c076ca41b33b069cea07f3a06cc1e9cb2d017c1e87f280258e205925c714959c31346f44a9ba3706ccd81ab14a3bcb01a735068ca419f2a85bcce19732831c3405b0e816cc818b28061c8205b1e016c9998425c5f49617c1345d4309211b05c4b816b2d052cb215f2b855caa14f29816c6005b29016c6405b2884dca00f327816c9c05b2684b4958e31344944b1211b047c8e1172244341e90b21016c5290320016c7e05b14a3ac528f71603d052873132294780eb1cc3904d0dd12c3646c0931a833c660c71881fc528bf17816c5c05f1680ec5805b1581fc528a314016c3089a10016c4a89412022c4404b1081fc3e0770e81bc3606707a1843005b0b014c2804b09010c1e83b0700cc1802b05008c0a8150400640280202a0440980e00e02c04808

/-- The literal table has 902 rows and a single edge into halt label 451. -/
def literalShape : Prop :=
  literal < 2048 ^ 902 ∧
  (List.range 902).all (fun i => let code := digit literal i
      code != 0 && (code - 1) / 4 ≤ 451) = true ∧
  ((List.range 902).filter (fun i => (digit literal i - 1) / 4 == 451)).length = 1

theorem literal_shape : literalShape := by
  unfold literalShape
  decide +kernel

end I0451

/-! Independent statement of the conditional result. The four formula
definitions below have their fixed values supplied by Solution. -/
namespace I0451.Logic
inductive NamedFormula where
  | truth
  | falsity
  | mem (x y : Nat)
  | equal (x y : Nat)
  | imp (left right : NamedFormula)
  | all (label : Nat) (body : NamedFormula)
  deriving DecidableEq

namespace NamedFormula
noncomputable def freeLabels (f : NamedFormula) : List Nat :=
  NamedFormula.rec (motive := fun _ => List Nat) [] []
    (fun a b => [a,b]) (fun a b => [a,b])
    (fun _ _ a b => a ++ b) (fun x _ a => a.filter (· != x)) f

end NamedFormula
end I0451.Logic

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

namespace I0451.Standalone

open I0451.Logic (NamedFormula)

/-- The first-order Berkeley cardinal axiom, with set-coded elementarity. -/
def berkeleyAxiom : NamedFormula := by sorry

/-- I₀ expressed using the proper ultrapower of L(V_{λ+1}).
Its elementary map has critical point below λ and its restriction
to V_λ belongs to L(V_{λ+1}). Both target theories use this sentence. -/
def i0Axiom : NamedFormula := by sorry

/-- Consistency of the specified Craig presentation of the arithmetic
consequences of ZFC + I₀, read in the membership model's natural numbers. -/
noncomputable def targetConsistency : NamedFormula := by sorry

/-- The Σ₁ assertion that there is a finite blank-tape run of the literal
machine stopping at a configuration with no outgoing transition. -/
def haltingArithmetic : SigmaFormula := by sorry

inductive Theory where
  | berkeley
  | zfcI0
  | zfI0

/-- A membership model satisfies the corresponding theory's additional axioms. -/
abbrev Models {V : Type} (T : Theory) (E : V → V → Prop) : Prop :=
  Model E ∧ Theory.casesOn T
    (∀ s, eval E s berkeleyAxiom)
    (Choice E ∧ ∀ s, eval E s i0Axiom)
    (∀ s, eval E s i0Axiom)

/-- Validity in all membership models. For these theories this is equivalent
to first-order provability, by completeness with the equality axioms. -/
abbrev Provable (T : Theory) (p : NamedFormula) : Prop :=
  ∀ (V : Type) (E : V → V → Prop), Nonempty V → Models T E → ∀ s, eval E s p

/-- Correct interpretation of a closed arithmetic assertion in every
ZF model, including models whose natural numbers are nonstandard. -/
def RepresentsArithmetic (p : SigmaFormula) (φ : NamedFormula) : Prop :=
  p.bound 0 ∧ φ.freeLabels = [] ∧
    ∀ (V : Type) (E : V → V → Prop), Nonempty V → Model E →
      ∀ s env : Nat → V, (∀ i, NatObject E (env i)) →
        (eval E s φ ↔ p.internalEval E env)

/-- Every provable Σ₁ arithmetic sentence is true in the standard naturals. -/
abbrev SigmaOneSound (T : Theory) : Prop :=
  ∀ (p : SigmaFormula) (φ : NamedFormula), RepresentsArithmetic p φ →
    Provable T φ → ∀ s : Nat → Nat, p.natEval s

/-- Conditional independence for the exact literal transition table.
The relative consistency premise is a Berkeley-theory proof for the
particular presentation used by `targetConsistency`. -/
abbrev Claim451 : Prop :=
  (∀ s : Nat → Nat, haltingArithmetic.natEval s ↔ I0451.Halts I0451.literal (I0451.blank 0)) ∧
    ∃ h : NamedFormula, RepresentsArithmetic haltingArithmetic h ∧
      ((¬ Provable .berkeley .falsity) → SigmaOneSound .zfcI0 → Provable .berkeley targetConsistency →
        (¬ I0451.Halts I0451.literal (I0451.blank 0)) ∧
          ((¬ Provable .zfcI0 h) ∧ (¬ Provable .zfcI0 (.imp h .falsity))) ∧
          ((¬ Provable .zfI0 h) ∧ (¬ Provable .zfI0 (.imp h .falsity))))

end I0451.Standalone

namespace I0451.Standalone
theorem exact451Claim : Claim451 := by sorry
end I0451.Standalone
