module
public import I3_380.Logic.SetFormulas
@[expose] public section

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

def checkBound (p : Formula) (n : Nat) : Bool :=
  match p with
  | .bot => true
  | .mem i j | .eq i j => decide (i < n) && decide (j < n)
  | .and a b | .or a b | .imp a b => checkBound a n && checkBound b n
  | .all a | .ex a => checkBound a (n + 1)

theorem checkBound_sound (p : Formula) (n : Nat) :
    checkBound p n = true ↔ Bound p n := by
  induction p generalizing n <;> simp [checkBound, Bound, *]

theorem choice_closed : Closed choiceAxiom :=
  (checkBound_sound _ _).mp (by decide +kernel)

theorem i3_closed : Closed i3Axiom :=
  (checkBound_sound _ _).mp (by decide +kernel)

end PalomarI3380.Logic
