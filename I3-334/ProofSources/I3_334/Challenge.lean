module
public import Std
@[expose] public section

/-! Standalone statement for the exact I3-334 machine. -/

namespace PalomarI3380

/-- Each natural encodes one side of the tape, with the closest bit least
significant. The scanned cell is the least significant bit of `right`. -/
structure Configuration where
  state : Nat
  left : Nat
  right : Nat
  deriving DecidableEq, Repr

def blank : Configuration := ⟨0, 0, 0⟩

/-- Rows are ordered by working state, then by read bit. Each 11-bit row
stores `4 * next + 2 * write + direction`, with right = 1. Packing permits
constant-index arithmetic lookup during kernel replay. -/
structure Machine where
  workingStates : Nat
  packedRows : Nat

def Machine.row (m : Machine) (state read : Nat) : Nat :=
  (m.packedRows >>> (11 * (2 * state + read))) % 2048

def step (m : Machine) (c : Configuration) : Option Configuration :=
  if m.workingStates ≤ c.state then none else
    let row := m.row c.state (c.right % 2)
    let written := row / 2 % 2
    let next := row / 4
    let tail := c.right / 2
    if row % 2 = 1 then
      some ⟨next, 2 * c.left + written, tail⟩
    else
      some ⟨next, c.left / 2, 4 * tail + 2 * written + c.left % 2⟩

def run (m : Machine) : Nat → Configuration → Option Configuration
  | 0, c => some c
  | n + 1, c => match step m c with
    | some next => run m n next
    | none => none

end PalomarI3380

namespace PalomarI3380

/-- A terminal configuration reached after finitely many literal steps. -/
def HaltsFrom (m : Machine) (c : Configuration) : Prop :=
  ∃ n terminal, run m n c = some terminal ∧ step m terminal = none

end PalomarI3380

/-! De Bruijn syntax, proof rules, and axiom schemas for ZF.
The I3 theory adds Choice and the rank-embedding sentence. -/
namespace PalomarI3380.Logic
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
end PalomarI3380.Logic

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

end InternalSets
end PalomarI3380.Logic.Internal

namespace PalomarI3380.Logic

/-- Build de Bruijn formulas using levels that are fixed at their binders.
The builder's argument is the number of binders currently in scope. -/
abbrev SetFormula := Nat → Formula

namespace SetFormula

def falsity : SetFormula := fun _ => .bot
def eq (x y : Nat) : SetFormula := fun d => .eq (d - (x + 1)) (d - (y + 1))
def mem (x y : Nat) : SetFormula := fun d => .mem (d - (x + 1)) (d - (y + 1))
def both (p q : SetFormula) : SetFormula := fun d => .and (p d) (q d)
def either (p q : SetFormula) : SetFormula := fun d => .or (p d) (q d)
def implies (p q : SetFormula) : SetFormula := fun d => .imp (p d) (q d)
def neg (p : SetFormula) : SetFormula := implies p falsity
def iff (p q : SetFormula) : SetFormula := both (implies p q) (implies q p)

def every (body : Nat → SetFormula) : SetFormula := fun d => .all (body d (d + 1))
def someSet (body : Nat → SetFormula) : SetFormula := fun d => .ex (body d (d + 1))
def eachIn (domain : Nat) (body : Nat → SetFormula) : SetFormula :=
  every fun x => implies (mem x domain) (body x)
def someIn (domain : Nat) (body : Nat → SetFormula) : SetFormula :=
  someSet fun x => both (mem x domain) (body x)

def allOf : List SetFormula → SetFormula
  | [] => neg falsity
  | p :: ps => both p (allOf ps)

def anyOf : List SetFormula → SetFormula
  | [] => falsity
  | p :: ps => either p (anyOf ps)

def empty (a : Nat) : SetFormula :=
  every fun x => neg (mem x a)

def subset (a b : Nat) : SetFormula :=
  eachIn a fun x => mem x b

def successor (a b : Nat) : SetFormula :=
  every fun x => iff (mem x b) (either (mem x a) (eq x a))

def numeral : Nat → Nat → SetFormula
  | 0, a => empty a
  | n + 1, a => someSet fun b => both (numeral n b) (successor b a)

def unorderedPair (a b p : Nat) : SetFormula :=
  every fun x => iff (mem x p) (either (eq x a) (eq x b))

def orderedPair (a b p : Nat) : SetFormula :=
  someSet fun singleton => someSet fun double =>
    allOf [unorderedPair a a singleton, unorderedPair a b double, unorderedPair singleton double p]

def graphValue (graph x y : Nat) : SetFormula :=
  someIn graph fun p => orderedPair x y p

def functionOn (graph domain : Nat) : SetFormula :=
  both
    (eachIn graph fun p => someIn domain fun x => someSet fun y => orderedPair x y p)
    (eachIn domain fun x => someSet fun y =>
      both (graphValue graph x y) (every fun z => implies (graphValue graph x z) (eq z y)))

def functionInto (graph domain codomain : Nat) : SetFormula :=
  both (functionOn graph domain)
    (eachIn domain fun x => every fun y => implies (graphValue graph x y) (mem y codomain))

def inductiveSet (a : Nat) : SetFormula :=
  both (someIn a empty) (eachIn a fun x => someIn a (successor x))

def omegaSet (w : Nat) : SetFormula :=
  both (inductiveSet w) (every fun a => implies (inductiveSet a) (subset w a))

def transitive (a : Nat) : SetFormula :=
  eachIn a fun x => subset x a

def ordinal (a : Nat) : SetFormula :=
  both (transitive a) (eachIn a transitive)

/-- The cumulative hierarchy equation, starting graphValue the empty set.
At stage `b`, a set is present exactly when it is a subset of an earlier stage. -/
def hierarchy (graph domain : Nat) : SetFormula :=
  both (functionOn graph domain)
    (eachIn domain fun b => every fun stage => implies (graphValue graph b stage)
      (every fun x => iff (mem x stage)
        (someIn b fun a => someSet fun earlier => both (graphValue graph a earlier) (subset x earlier))))

def rank (height stage : Nat) : SetFormula :=
  both (ordinal height)
    (someSet fun domain => someSet fun graph =>
      allOf [successor height domain, hierarchy graph domain, graphValue graph height stage])

end SetFormula

open SetFormula in
/-- Every set of nonempty sets has a choice function. -/
def choiceAxiom : Formula :=
  (every fun family =>
    implies (eachIn family fun x => someIn x fun y => eq y y)
      (someSet fun f =>
        both (functionOn f family)
          (eachIn family fun x => every fun y => implies (graphValue f x y) (mem y x)))) 0

end PalomarI3380.Logic

namespace PalomarI3380.Logic

open SetFormula

/-- A postorder syntax row is a tagged pair of operands. The five tags
denote equality, membership, negation, conjunction and existential binding. -/
def syntaxRow (rows i : Nat) (body : Nat → Nat → Nat → SetFormula) : SetFormula :=
  someSet fun row => someSet fun tag => someSet fun operands =>
    someSet fun first => someSet fun second =>
      allOf [graphValue rows i row, orderedPair tag operands row,
        orderedPair first second operands, body tag first second]

def validRow (arity i tag first second : Nat) : SetFormula :=
  anyOf [
    allOf [numeral 0 tag, mem first arity, mem second arity],
    allOf [numeral 1 tag, mem first arity, mem second arity],
    both (numeral 2 tag) (mem first i),
    allOf [numeral 3 tag, mem first i, mem second i],
    allOf [numeral 4 tag, mem first arity, mem second i]
  ]

def syntaxCode (w arity count rows : Nat) : SetFormula :=
  allOf [mem arity w, mem count w, neg (empty count), functionOn rows count,
    eachIn count fun i => syntaxRow rows i fun tag first second =>
      allOf [mem first w, mem second w, validRow arity i tag first second]]

def agreesAway (arity old new index : Nat) : SetFormula :=
  eachIn arity fun i => implies (neg (eq i index))
    (every fun x => iff (graphValue old i x) (graphValue new i x))

def atomicTruth (relation : Nat → Nat → SetFormula) (env first second : Nat) : SetFormula :=
  someSet fun x => someSet fun y =>
    allOf [graphValue env first x, graphValue env second y, relation x y]

def rowTruth (arity stage sat env tag first second : Nat) : SetFormula :=
  anyOf [
    both (numeral 0 tag) (atomicTruth eq env first second),
    both (numeral 1 tag) (atomicTruth mem env first second),
    both (numeral 2 tag) (neg (graphValue sat first env)),
    allOf [numeral 3 tag, graphValue sat first env, graphValue sat second env],
    both (numeral 4 tag)
      (someSet fun amended =>
        allOf [functionInto amended arity stage, agreesAway arity env amended first,
          graphValue sat second amended])
  ]

/-- A truth set contains the pairs (syntax node, assignment) at which
the finite formula is true. The recursion ranges over the model's own
natural numbers and function graphs. -/
def truthSet (arity count rows stage sat : Nat) : SetFormula :=
  eachIn count fun i => every fun env => implies (functionInto env arity stage)
    (syntaxRow rows i fun tag first second =>
      iff (graphValue sat i env) (rowTruth arity stage sat env tag first second))

def mappedAssignment (arity embedding source target : Nat) : SetFormula :=
  eachIn arity fun i => every fun x => every fun y =>
    implies (both (graphValue source i x) (graphValue embedding x y)) (graphValue target i y)

def elementaryOnRank (w stage embedding : Nat) : SetFormula :=
  every fun arity => every fun count => every fun rows =>
    implies (syntaxCode w arity count rows)
      (someSet fun sat =>
        both (truthSet arity count rows stage sat)
          (eachIn count fun i => every fun source => every fun target =>
            implies (allOf [functionInto source arity stage, functionInto target arity stage,
                mappedAssignment arity embedding source target])
              (iff (graphValue sat i source) (graphValue sat i target))))

/-- There is a nonidentity elementary self-embedding at a nonzero
limit rank. Elementarity uses one uniform truth-set formula, including all internally
coded formulas in models with nonstandard natural numbers. -/
def i3Axiom : Formula :=
  (someSet fun w => someSet fun height => someSet fun stage => someSet fun embedding =>
    allOf [
      omegaSet w,
      rank height stage,
      inductiveSet height,
      functionInto embedding stage stage,
      someIn stage fun x => someIn stage fun y => both (graphValue embedding x y) (neg (eq x y)),
      elementaryOnRank w stage embedding
    ]) 0

def ZFCI3Axiom (p : Formula) : Prop := Axiom p ∨ p = choiceAxiom ∨ p = i3Axiom

def ZFCI3Provable (p : Formula) : Prop :=
  ∃ Γ : Context, (∀ q, q ∈ Γ → ZFCI3Axiom q) ∧ ND (.seq Γ p)

def ZFCI3Consistent : Prop := ¬ ZFCI3Provable .bot

def ZFCI3Model {V : Type} (E : V → V → Prop) : Prop :=
  ∀ p, ZFCI3Axiom p → ∀ s : Nat → V, eval E p s

end PalomarI3380.Logic

namespace PalomarI3380.Logic

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
def ArithTerm.value {V : Type} [Zero V] [One V] [Add V] [Mul V] :
    ArithTerm → (Nat → V) → V
 | .zero,_=>0 | .one,_=>1 | .var i,s=>s i
 | .add p q,s=>p.value s+q.value s
 | .mul p q,s=>p.value s*q.value s

def SigmaFormula.value {V : Type} [Zero V] [One V] [Add V] [Mul V] [LT V] :
    SigmaFormula → (Nat → V) → Prop
 | .atom p q eq pos,s=>
   let P:=if eq then p.value s=q.value s else p.value s<q.value s
   if pos then P else ¬P
 | .conj p q,s=>p.value s ∧ q.value s
 | .disj p q,s=>p.value s ∨ q.value s
 | .exists_ p,s=>∃x,p.value (pushValue s x)
 | .forallLt b p,s=>∀x,x<b.value s→p.value (pushValue s x)

abbrev ArithTerm.natValue (t : ArithTerm) (s : Nat → Nat) : Nat := t.value s
abbrev SigmaFormula.natEval (φ : SigmaFormula) (s : Nat → Nat) : Prop := φ.value s

open Internal
/-- Fully relational evaluation, including arithmetic internal to a set model. -/
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
/-- Correct arithmetic meaning in every ZFC + I3 model, not just well-founded or
omega-standard models. Both syntax objects are fixed finite external syntax. -/
def RepresentsArithmetic (φ:SigmaFormula) (ψ:Formula):Prop:=
 Closed ψ ∧ ∀(V:Type) (E:V→V→Prop),Nonempty V→ZFCI3Model E→
 ∀(s env:Nat→V),(∀i,NatObject E (env i))→(eval E ψ s ↔ φ.internalEval E env)
/-- Arithmetic Σ₁-soundness of ZFC + I3 under the standard interpretation in its natural numbers. -/
def ArithmeticSigma1Sound:Prop:=
 ∀φ:SigmaFormula,φ.bound 0→∀ψ:Formula,RepresentsArithmetic φ ψ→
 ZFCI3Provable ψ→∀s:Nat→Nat,φ.natEval s

end PalomarI3380.Logic

namespace PalomarI3380

def loaderExit : Configuration :=
  ⟨7, 1, 0x15555555555555555555555555555555555aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa80000⟩

end PalomarI3380

namespace PalomarI3334

/-- Exact rows of `data/zfc-i3-native-334.tm`. -/
def literal : Array Nat := #[
  7, 8, 9, 5, 14, 17, 16, 20, 2, 4, 20, 24,
  24, 28, 28, 32, 32, 36, 40, 38, 44, 38, 48, 38,
  52, 38, 56, 38, 61, 38, 61, 67, 69, 75, 77, 83,
  85, 91, 93, 96, 101, 107, 109, 115, 117, 123, 125, 131,
  132, 96, 137, 143, 145, 151, 93, 155, 157, 163, 165, 171,
  173, 179, 183, 184, 125, 191, 38, 132, 129, 195, 157, 199,
  125, 203, 205, 211, 213, 32, 125, 219, 221, 32, 125, 227,
  229, 32, 85, 235, 237, 243, 181, 247, 248, 186, 255, 258,
  261, 33, 145, 32, 201, 267, 269, 36, 273, 275, 277, 283,
  125, 287, 125, 147, 125, 159, 289, 295, 165, 299, 301, 307,
  309, 315, 317, 247, 320, 186, 253, 325, 328, 335, 221, 279,
  337, 267, 125, 303, 341, 343, 125, 347, 349, 355, 125, 359,
  125, 343, 125, 291, 361, 194, 125, 95, 365, 371, 85, 351,
  373, 379, 380, 247, 320, 132, 387, 327, 388, 330, 395, 333,
  186, 267, 125, 363, 125, 295, 165, 398, 400, 407, 125, 271,
  125, 223, 301, 411, 413, 419, 173, 423, 425, 431, 434, 184,
  437, 325, 440, 330, 124, 439, 445, 451, 453, 459, 461, 32,
  465, 28, 269, 471, 473, 459, 477, 483, 301, 36, 485, 491,
  381, 434, 188, 439, 440, 96, 493, 96, 157, 499, 285, 503,
  157, 507, 125, 511, 513, 515, 277, 32, 400, 519, 301, 523,
  525, 531, 269, 535, 353, 539, 125, 167, 345, 32, 541, 32,
  293, 32, 125, 279, 401, 547, 341, 32, 549, 96, 553, 559,
  561, 567, 569, 32, 573, 579, 277, 583, 585, 575, 589, 595,
  597, 599, 601, 607, 609, 615, 557, 619, 125, 463, 621, 627,
  629, 635, 445, 639, 641, 475, 301, 647, 649, 655, 569, 603,
  569, 659, 660, 599, 425, 667, 669, 675, 677, 683, 165, 687,
  493, 691, 692, 36, 357, 699, 157, 535, 269, 155, 701, 96,
  705, 175, 709, 715, 569, 547, 717, 603, 721, 695, 725, 731,
  361, 735, 609, 739, 369, 743, 745, 32, 729, 751, 753, 451,
  757, 763, 765, 771, 597, 607, 301, 775, 561, 779, 781, 547,
  225, 36, 785, 791, 493, 36, 301, 795, 797, 615, 557, 803,
  445, 751, 357, 36, 217, 807, 809, 1339, 273, 815, 301, 819,
  821, 827, 829, 96, 833, 839, 725, 843, 225, 503, 580, 847,
  717, 32, 785, 851, 553, 855, 845, 32, 357, 96, 357, 519,
  857, 96, 861, 555, 173, 867, 869, 875, 225, 879, 881, 887,
  889, 895, 509, 194, 789, 631, 561, 679, 897, 903, 569, 907,
  909, 915, 917, 923, 925, 931, 933, 96, 657, 939, 369, 563,
  493, 943, 637, 947, 301, 951, 952, 958, 657, 599, 301, 963,
  705, 967, 861, 971, 861, 975, 705, 979, 981, 987, 705, 991,
  569, 607, 297, 32, 657, 727, 993, 96, 997, 1003, 821, 1007,
  1009, 96, 1013, 1019, 1021, 975, 657, 603, 1021, 1027, 1029, 979,
  369, 983, 677, 1035, 905, 1039, 821, 1043, 1045, 1051, 1053, 563,
  1057, 1063, 821, 863, 705, 1067, 705, 559, 1069, 1071, 1072, 975,
  1041, 1079, 369, 1083, 609, 1087, 561, 1091, 997, 679, 1093, 563,
  301, 1099, 881, 1103, 917, 1107, 1093, 871, 1109, 1115, 369, 1119,
  1029, 1123, 797, 739, 369, 1127, 601, 659, 1129, 96, 649, 1135,
  957, 1139, 705, 959, 921, 1143, 705, 1147, 657, 974, 1013, 1151,
  677, 955, 1153, 1159, 973, 1163, 1165, 1171, 705, 1175, 1013, 855,
  301, 1179, 1121, 1183, 917, 1075, 1185, 1191, 561, 1195, 853, 1043,
  1197, 96, 1185, 1203, 553, 1031, 901, 1023, 1013, 1207, 905, 1211,
  369, 1123, 1145, 1215, 925, 1183, 677, 1219, 901, 1223, 705, 1227,
  1229, 1235, 609, 1239, 1121, 1243, 1245, 1251, 705, 1255, 1257, 799,
  361, 1263, 1121, 1267, 797, 799, 301, 1271, 861, 1275, 605, 32,
  1229, 1279, 901, 1283, 561, 1287, 861, 1291, 1109, 1295, 1165, 1299,
  1053, 1303, 1053, 1307, 1309, 1315, 861, 883, 525, 1319, 869, 1323,
  821, 1327, 869, 1331, 1309, 1335, 369, 1187
]

def packedLiteral : Nat := 0x9465c69bd1da66d9697b35a56d9693a0d6e6d7691d1da370768bc1da2723687c55a16d7683a31a06e167fccd0409767db5d9ee4b58fb1d9e71867796963f3a673ac19c73766dc619ae98669ccd996b0663b85986a964fb9d97f1e631971976e265bbf57fee1603a29967284304ad826d5655a3194f28619b9593f1864d92d6aefd64bac192723645bcd90f205ddaa58fefd5e72918f6b063bb9977eb0639bbd8dea2430469526966339715c6c7631c058be5c62dc556cf11629b9589edc62592d46711553be58868c61fa618765c61bc1179f0c217c2d45eb0615ac16becd613c214670760dc15826cd607b89816a95eb9717a701601bfd4b6a45e7bfd7f6fd4303f17decd5f5be50c0f856ba910404a52fa397beb05edbd57a6b05e7b5d796d75e3ac17864b52ba9177cee1db92d7669f5d79ed4665c5d5a910c0e95d1b9d736e55c9b8d7168e5c3b8154e8c53bb151847f5bfb796eedc5b78e16d6d95b18ad456d743035940e59430165040d35aba296a6c44102cd69e910fb8e1696b55a3b410c0cf59db356664b597911a76ca5938d9048595779bd6468b533b1d6364b4121ed62ec44120e1446c3585a3160e4b52fa55606bf57daf5386bc577ad9040ba5739715c69856f9695b6b555bad14b6b3511a39596b1457ac10c0af44d90d42e2755d965048ad1599ed55e29555aa5546a754d9a94aea5149a394b68e547a8950e4b4eda814fe6f53da754e69b4e787d4d68b533a614be9652ba554a69351fa4948e45521a3d0408e51ba3145e8a4302250405551199122e1f4101250408741015914e1f50d96142e43509a0d4164b50399004045501a013fe1f4fd89d3ee474f989d0c07b4301b836e2f0d917d3d67941212d3c6774e59d93ae4340e1d1040734e59c53866f4db87c2946e0a29b51706c8d79a934e2b4d199d3364b46f87d21e1f4cb99031c2949387d2d61f4858ba29a62ca518428e60c421401ee5f0bd9752be154b996d0be1f4611692461f4ab87d2ce1f4b195d2b61f4ab95525e1f48595122e374a794828a3f45d1401ee4f49d9352664b4958a524e4844f87d1261f48f87d23645489911048434858c9040244109052043fc5d0f81ee2d4798ed1d6154100e51c61f4100dd1b61f4100d51a63346587d18e274618811080985f87d1702dc598ad1562945189d1361744b89111e224300841061f43d8750e61b4358650c01742d8550a6134258450860f41303d04c0e01303404c0c01302c04c0a0120200400700e018030050020020280400880e00a02404007

def machine : PalomarI3380.Machine := ⟨334, packedLiteral⟩

end PalomarI3334

namespace PalomarI3334

open PalomarI3380 (HaltsFrom blank)
open PalomarI3380.Logic

namespace Internal

open PalomarI3380.Logic.Internal

variable {V : Type} (E : V → V → Prop)

def LiteralStep (s t : Configuration V) : Prop :=
  ∃ q : Fin 334, Numeral E q.val s.state ∧ ∃ read : Bool,
    let row := literal[2 * q.val + (if read then 1 else 0)]?.getD 0
    Move E read (row / 2 % 2 == 1) (row % 2 == 1) (row / 4) s t

/-- An internal finite history of the exact 334-state machine. Its length
and entries may be nonstandard in a model of ZFC + I3. -/
def Halts : Prop :=
  ∃ n domain history zero start finish,
    NatObject E n ∧ Succ E n domain ∧ FunctionOn E history domain ∧ Empty E zero ∧
      ConfigurationCode E ⟨zero, zero, zero⟩ start ∧ At E history zero start ∧
      At E history n finish ∧
      (∃ final, ConfigurationCode E final finish ∧ Numeral E 334 final.state) ∧
      ∀ i, E i n → ∃ next s t before after, Succ E i next ∧
        At E history i before ∧ At E history next after ∧
        ConfigurationCode E s before ∧ ConfigurationCode E t after ∧ LiteralStep E s t

end Internal

/-- A closed set-theoretic sentence for halting of the 334-state machine. -/
def RepresentsHalting (H : Formula) : Prop :=
  Closed H ∧ ∀ (V : Type) (E : V → V → Prop), Nonempty V → ZFCI3Model E →
    ∀ env : Nat → V, eval E H env ↔ Internal.Halts E

/-- Conditional independence for the literal 334-state machine on a blank tape. -/
def ExactClaim : Prop :=
  ∃ H : Formula, RepresentsHalting H ∧
    (ZFCI3Consistent → ¬ HaltsFrom machine blank ∧ ¬ ZFCI3Provable (Neg H)) ∧
    (ArithmeticSigma1Sound → ¬ ZFCI3Provable H ∧ ¬ ZFCI3Provable (Neg H))

end PalomarI3334

namespace PalomarI3334

open PalomarI3380

def decoderEntry : Configuration := { PalomarI3380.loaderExit with state := 16 }

theorem literal_binding :
    machine.workingStates = 334 ∧ literal.size = 668 ∧
    (literal.toList.zipIdx.all fun (row, i) => machine.row (i / 2) (i % 2) == row) = true ∧
    (literal.toList.all fun row => row / 4 ≤ 334) = true ∧
    (literal.toList.zipIdx.filter fun (row, _) => row / 4 == 334) = [(4 * 334 + 3, 379)] := by
  sorry

theorem literal_startup : run machine 39765 blank = some decoderEntry := by
  sorry

theorem exactClaim : ExactClaim := by
  sorry

end PalomarI3334
