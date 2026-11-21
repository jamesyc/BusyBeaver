module
public import I3_380.Logic.Syntax
@[expose] public section

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
