module
public import ZFRArbitraryFiniteSets
@[expose] public section
/- Concrete hereditarily-finite set naming formulas in the exact ZFR calculus.
These are foundational data-code certificates, not an encoding of the final TM. -/
namespace ZFR.FiniteCode
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

inductive Code where
 | node (children : List Code)
 deriving Repr

def disjunction : List Formula → Formula
 | [] => .bot
 | p :: ps => .or p (disjunction ps)

noncomputable def value {V : Type*} [SetStructure V] [Nonempty V]
 [V↓[ℒₛₑₜ] ⊧* BasicSetTheory] : Code → V
 | .node children => modelFiniteSet (children.map value)

/-- After binding k child values, variable k is the set being named and
variables0..k-1 are its listed members. -/
def exactMembers (k : Nat) : Formula :=
 let member := disjunction ((List.range k).map (fun i => Formula.eq 0 (i+1)))
 .all (.and (.imp (.mem 0 (k+1)) member) (.imp member (.mem 0 (k+1))))

/-- Each child naming formula occurs ONCE. Existential bindings provide
sharing instead of expanding each child's definition in both directions. -/
def bindNames : List Formula → Nat → Formula
 | [], k => exactMembers k
 | p :: ps, k => .ex (.and p (bindNames ps (k+1)))

def compactNames : Code → Formula
 | .node children => bindNames (children.map compactNames) 0

def formulaNodes : Formula → Nat
 | .bot | .mem _ _ | .eq _ _ => 1
 | .and p q | .or p q | .imp p q => 1 + formulaNodes p + formulaNodes q
 | .all p | .ex p => 1 + formulaNodes p

/-- Production naming uses existential sharing. The recursive reference is
retained only for semantic comparison and small diagnostic benchmarks. -/
def names (c : Code) : Formula := compactNames c

theorem eval_rename {V : Type*} (mem : V → V → Prop) (p : Formula)
 (σ : Nat → Nat) (s : Nat → V) :
 eval mem (rename σ p) s ↔ eval mem p (s ∘ σ) := by
 induction p generalizing σ s with
 | bot => rfl
 | mem i j => rfl
 | eq i j => rfl
 | and p q ip iq => exact and_congr (ip σ s) (iq σ s)
 | or p q ip iq => exact or_congr (ip σ s) (iq σ s)
 | imp p q ip iq => exact imp_congr (ip σ s) (iq σ s)
 | all p ih =>
   change (∀ x, eval mem (rename (lift σ) p) (pushValue s x)) ↔ _
   apply forall_congr'; intro x
   rw [ih]
   have hs : pushValue s x ∘ lift σ = pushValue (s ∘ σ) x := by
     funext i; cases i <;> rfl
   rw [hs]
 | ex p ih =>
   change (∃ x, eval mem (rename (lift σ) p) (pushValue s x)) ↔ _
   apply exists_congr; intro x
   rw [ih]
   have hs : pushValue s x ∘ lift σ = pushValue (s ∘ σ) x := by
     funext i; cases i <;> rfl
   rw [hs]

/-- Closed source formula relating two specifically named finite sets. -/
def fact (a b : Code) (relation : Formula) : Formula :=
 .all (.all (.imp (.and (names a) (shift (names b))) relation))

end ZFR.FiniteCode
