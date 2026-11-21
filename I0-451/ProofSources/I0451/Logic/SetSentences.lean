module
public import I0451.Logic.Derivability
public import I0451.AssignmentCode

/-! Readable named encodings of the two closed formulas emitted by EXTRA.
Fresh labels are allocated by the quantifier combinators. -/
@[expose] public section
namespace I0451.Logic.SetSentences

open I0451.AssignmentCode

def formulaNot (a : Formula) : Formula := .imp a (.mem 0 0)
def formulaAnd (a b : Formula) : Formula := formulaNot (.imp a (formulaNot b))
def formulaOr (a b : Formula) : Formula := .imp (formulaNot a) b
def formulaIff (a b : Formula) : Formula := formulaAnd (.imp a b) (.imp b a)
def formulaExists (i : Nat) (f : Formula) : Formula := formulaNot (.all i (formulaNot f))

abbrev Template := Nat → Formula

def member (x y : Nat) : Template := fun _ => .mem x y
def equals (x y : Nat) : Template := fun _ => .equal x y
def implies (a b : Template) : Template := fun next => .imp (a next) (b next)
def conjunction (a b : Template) : Template := fun next => formulaAnd (a next) (b next)
def disjunction (a b : Template) : Template := fun next => formulaOr (a next) (b next)
def equivalent (a b : Template) : Template := fun next => formulaIff (a next) (b next)
def negate (a : Template) : Template := fun next => formulaNot (a next)

def each (body : Nat → Template) : Template := fun next => .all next (body next (next + 1))
def witness (body : Nat → Template) : Template := fun next => formulaExists next (body next (next + 1))

def eachIn (domain : Nat) (body : Nat → Template) : Template :=
  each fun x => implies (member x domain) (body x)

def witnessIn (domain : Nat) (body : Nat → Template) : Template :=
  witness fun x => conjunction (member x domain) (body x)

def isSubset (x y : Nat) : Template :=
  eachIn x fun z => member z y

def isTransitive (d : Nat) : Template :=
  eachIn d fun x => isSubset x d

def isPair (p x y : Nat) : Template :=
  each fun s => equivalent (member s p) (conjunction (member x s)
    (eachIn s fun z => disjunction (equals z x) (equals z y)))

def hasValue (g x y : Nat) : Template :=
  witnessIn g fun p => isPair p x y

def isBounded (g d : Nat) : Template :=
  eachIn g fun p => eachIn p fun a => isSubset a d

def isMap (g d : Nat) : Template :=
  conjunction (isBounded g d) (eachIn d fun x => witness fun y =>
    conjunction (hasValue g x y) (each fun z => implies (hasValue g x z) (equals z y)))

def agrees (i g h : Nat) : Template :=
  eachIn g fun p => implies (negate (member p h)) (eachIn p fun a => member i a)

def relativeAtom (d U C : Nat) : Template :=
  each fun i => each fun k => implies (conjunction (member i d) (member k d))
    (witnessIn C fun R => eachIn U fun g =>
      equivalent (member g R) (each fun x => each fun y =>
        implies (conjunction (hasValue g i x) (hasValue g k y)) (member x y)))

def relativeClose (d U C : Nat) : Template :=
  each fun R => each fun S => each fun i =>
    implies (conjunction (member R C) (conjunction (member S C) (member i d)))
      (witnessIn C fun W => eachIn U fun g =>
        equivalent (member g W) (witnessIn U fun h =>
          conjunction (implies (member h R) (member h S)) (agrees i g h)))

def identityComparison (d j U C : Nat) : Template :=
  witnessIn U fun e =>
    conjunction (eachIn d fun x => hasValue e x x)
      (eachIn C fun R => implies (member e R) (member j R))

def compressedBerkeley : Template :=
  witness fun a => each fun d =>
    implies (conjunction (isTransitive d) (member a d))
      (witness fun j => witness fun U => witness fun C =>
        conjunction (member j U)
          (conjunction (witnessIn a fun x => negate (hasValue j x x))
            (conjunction (each fun g => equivalent (member g U) (isMap g d))
              (conjunction (relativeAtom d U C)
                (conjunction (relativeClose d U C) (identityComparison d j U C))))))

def foundationTemplate : Template :=
  each fun a => implies (witness fun x => member x a)
    (witnessIn a fun x => eachIn x fun y => negate (member y a))

def foundationFormula : Formula := foundationTemplate 0
def berkeleyFormula : Formula := compressedBerkeley 0

def foundationCode : Nat := foundationFormula.code
def berkeleyCode : Nat := berkeleyFormula.code

def Foundation {V : Type} (E : V → V → Prop) : Prop :=
  ∀ a, (∃ x, E x a) → ∃ x, E x a ∧ ∀ y, E y x → ¬ E y a

def Transitive {V : Type} (E : V → V → Prop) (d : V) : Prop :=
  ∀ x, E x d → ∀ y, E y x → E y d

def BerkeleyFormula {V : Type} (E : V → V → Prop) : Prop :=
  ∃ a, ∀ d, Transitive E d → E a d →
    ∃ j U C, E j U ∧ (∃ x, E x a ∧ ¬ At E j x x) ∧ TruthSets E d U C ∧
      ∃ e, E e U ∧ (∀ x, E x d → At E e x x) ∧
        ∀ R, E R C → E e R → E j R

theorem eval_or {V : Type} {E : V → V → Prop} (s : Nat → V)
    (irrefl : ∀ x, ¬ E x x) (a b : Nat) :
    Eval E s (Logic.or a b) ↔ Eval E s a ∨ Eval E s b := by
  unfold Logic.or
  rw [eval_imp, eval_neg irrefl]
  exact ⟨fun proof => by
    by_cases ha : Eval E s a
    · exact Or.inl ha
    · exact Or.inr (proof ha),
    fun proof na => proof.elim (fun a => (na a).elim) id⟩

private theorem eval_formulaNot {V : Type} {E : V → V → Prop} (irrefl : ∀ x, ¬ E x x)
    (s : Nat → V) (a : Formula) : (formulaNot a).eval E s ↔ ¬ a.eval E s := by
  simp only [← eval_formula E]
  exact eval_neg irrefl s a.code

private theorem eval_formulaAnd {V : Type} {E : V → V → Prop} (irrefl : ∀ x, ¬ E x x)
    (s : Nat → V) (a b : Formula) : (formulaAnd a b).eval E s ↔ a.eval E s ∧ b.eval E s := by
  simp only [← eval_formula E]
  exact eval_and s irrefl a.code b.code

private theorem eval_formulaOr {V : Type} {E : V → V → Prop} (irrefl : ∀ x, ¬ E x x)
    (s : Nat → V) (a b : Formula) : (formulaOr a b).eval E s ↔ a.eval E s ∨ b.eval E s := by
  simp only [← eval_formula E]
  exact eval_or s irrefl a.code b.code

private theorem eval_formulaIff {V : Type} {E : V → V → Prop} (irrefl : ∀ x, ¬ E x x)
    (s : Nat → V) (a b : Formula) : (formulaIff a b).eval E s ↔ (a.eval E s ↔ b.eval E s) := by
  simp only [← eval_formula E]
  exact eval_iff s irrefl a.code b.code

private theorem eval_formulaExists {V : Type} {E : V → V → Prop} (irrefl : ∀ x, ¬ E x x)
    (s : Nat → V) (x : Nat) (a : Formula) :
    (formulaExists x a).eval E s ↔ ∃ v, a.eval E (assign s x v) := by
  simp only [← eval_formula E]
  exact eval_ex s irrefl x a.code

theorem foundation_eval {V : Type} {E : V → V → Prop} (irrefl : ∀ x, ¬ E x x)
    (s : Nat → V) : Eval E s foundationCode ↔ Foundation E := by
  rw [foundationCode, eval_formula]
  simp [foundationFormula, foundationTemplate, Foundation, each, eachIn, witness,
    witnessIn, implies, conjunction, negate, member, eval_formulaExists irrefl, eval_formulaAnd irrefl,
    eval_formulaNot irrefl, Formula.eval, assign]

private theorem truthSets_explicit {V : Type} {E : V → V → Prop} (d U C : V) :
    TruthSets E d U C ↔
      (∀ g, E g U ↔ IsMap E d g) ∧
      (∀ i k, E i d → E k d → ∃ R, E R C ∧ ∀ g, E g U →
        (E g R ↔ ∀ x y, At E g i x → At E g k y → E x y)) ∧
      (∀ R S i, E R C → E S C → E i d → ∃ W, E W C ∧ ∀ g, E g U →
        (E g W ↔ ∃ u, E u U ∧ (E u R → E u S) ∧ Agree E i g u)) := by
  constructor
  · intro given
    refine ⟨given.codes, ?_, ?_⟩
    · intro i k hi hk
      exact given.atom ⟨i, hi⟩ ⟨k, hk⟩
    · intro R S i hr hs hi
      exact given.close ⟨i, hi⟩ R S hr hs
  · rintro ⟨codes, atom, close⟩
    exact ⟨codes, fun i k => atom i k i.property k.property,
      fun i R S hr hs => close R S i hr hs i.property⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem berkeley_formula_eval {V : Type} {E : V → V → Prop} (irrefl : ∀ x, ¬ E x x)
    (s : Nat → V) : Eval E s berkeleyCode ↔ BerkeleyFormula E := by
  rw [berkeleyCode, eval_formula]
  simp [berkeleyFormula, compressedBerkeley, BerkeleyFormula, truthSets_explicit,
    relativeAtom, relativeClose, identityComparison, agrees, isMap, isBounded,
    hasValue, isPair, isTransitive, isSubset, Transitive, At, Pair, Bounded, Agree,
    IsMap, each, witness, eachIn, witnessIn, conjunction, disjunction, implies,
    equivalent, negate, member, equals, eval_formulaExists irrefl, Formula.eval,
    eval_formulaAnd irrefl, eval_formulaOr irrefl, eval_formulaIff irrefl, eval_formulaNot irrefl,
    assign, and_assoc, and_imp]
theorem sound_in_model {V : Type} {E : V → V → Prop} (point : V) (M : BundleModel E)
    (foundation : Foundation E) (berkeley : BerkeleyFormula E) :
    ¬ Derives foundationCode berkeleyCode 1 := by
  intro contradiction
  have good := contradiction.sound M (fun values => (foundation_eval M.irrefl values).2 foundation)
    (fun values => (berkeley_formula_eval M.irrefl values).2 berkeley) (fun _ => point)
  exact eval_false _ M.irrefl good

end I0451.Logic.SetSentences
