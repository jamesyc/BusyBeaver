module
public import I3_334.Search.Templates
public import I3_334Support.Equations.Meredith
@[expose] public section

namespace PalomarI3334

open PalomarI3380 (RawTerm MeredithLaws meredithLaws)
open Templates

/-- The ten-equation signature, with one operation for each additional
arity-tag pair admitted by the literal term reader. -/
structure NativeAlgebra (A : Type) where
  domain : A
  embedding : A
  membership : A
  seed : A
  identity : A
  neg : A → A
  converse : A → A
  choice : A → A
  nand : A → A → A
  product : A → A → A
  other : Nat → List A → A

namespace NativeAlgebra

variable {A : Type} (M : NativeAlgebra A)

def operation (tag : Nat) (args : List A) : A :=
  match args, tag with
  | [], 0 => M.embedding
  | [], 1 => M.domain
  | [], 2 => M.membership
  | [], 3 => M.seed
  | [], 5 => M.identity
  | [x], 1 => M.choice x
  | [x], 3 => M.neg x
  | [x], 4 => M.converse x
  | [x, y], 3 => M.nand x y
  | [x, y], 4 => M.product x y
  | _, _ => M.other tag args

def evalRaw (t : RawTerm) : A := t.fold M.operation

theorem evalRaw_app (tag : Nat) (children : List RawTerm) :
    M.evalRaw (.app tag children) = M.operation tag (children.map M.evalRaw) :=
  RawTerm.fold_app _ _ _

def eval (values : Fin 4 → A) : Pattern → A
  | .capture slot => values slot
  | .constant tag => M.operation tag []
  | .unary tag arg => M.operation tag [eval values arg]
  | .binary tag left right => M.operation tag [eval values left, eval values right]

theorem eval_instantiate (values : Fin 4 → RawTerm) (p : Pattern) :
    M.evalRaw (p.instantiate values) = M.eval (M.evalRaw ∘ values) p := by
  induction p <;> simp_all [Pattern.instantiate, evalRaw, eval]

def valuation (a b c d : A) : Fin 4 → A :=
  fun i => if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else d

/-- The fourth operand ranges over a designated collection of safe values.
Both ordinary and arithmetic-coded closed terms supply such a collection. -/
structure ModelsOn (safe : A → Prop) : Prop where
  equations : ∀ equation ∈ Templates.equations, ∀ a b c d : A, safe d →
    let values := valuation a b c d
    M.eval values equation.1 = M.eval values equation.2
  seed_safe : safe M.seed

def SafeValue (x : A) : Prop :=
  ∃ t : RawTerm, Guarded t ∧ M.evalRaw t = x

theorem safe_seed : M.SafeValue M.seed :=
  ⟨.app 3 [], by simp [Guarded], by rw [evalRaw_app]; rfl⟩

abbrev Models : Prop := M.ModelsOn M.SafeValue

theorem models_of_raw (rows : ∀ equation ∈ equations, ∀ a b c : A, ∀ d : RawTerm, Guarded d →
    let values := valuation a b c (M.evalRaw d)
    M.eval values equation.1 = M.eval values equation.2) : M.Models := by
  refine ⟨?_,M.safe_seed⟩
  rintro eq listed a b c x ⟨d,guard,rfl⟩
  exact rows eq listed a b c d guard

theorem Models.ground {M : NativeAlgebra A} (model : M.Models) {eq : Equation}
    (listed : eq ∈ equations) (values : Fin 4 → RawTerm) (safe : Guarded (values 3)) :
    M.evalRaw (eq.1.instantiate values) = M.evalRaw (eq.2.instantiate values) := by
  have same : valuation (M.evalRaw (values 0)) (M.evalRaw (values 1))
      (M.evalRaw (values 2)) (M.evalRaw (values 3)) = M.evalRaw ∘ values := by
    funext i
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> rfl
  simp only [eval_instantiate]
  rw [← same]
  exact model.equations eq listed _ _ _ _ ⟨values 3,safe,rfl⟩

def meet (x y : A) : A := M.neg (M.nand x y)

variable {safe : A → Prop}

theorem ModelsOn.boolean {M : NativeAlgebra A} (model : M.ModelsOn safe) : MeredithLaws M.meet M.neg := by
  refine meredithLaws M.meet M.neg ?_ ?_
  · intro x y
    exact (model.equations boolean_left (by simp [Templates.equations]) x y x M.seed model.seed_safe).symm
  · intro x y z
    exact (model.equations boolean_right (by simp [Templates.equations]) x y z M.seed model.seed_safe).symm

theorem ModelsOn.associative {M : NativeAlgebra A} (model : M.ModelsOn safe) (x y z : A) :
    M.product x (M.product y z) = M.product (M.product x y) z :=
  model.equations product_assoc (by simp [Templates.equations]) x y z M.seed model.seed_safe

theorem ModelsOn.unit {M : NativeAlgebra A} (model : M.ModelsOn safe) (x : A) :
    M.product x M.identity = x :=
  model.equations right_identity (by simp [Templates.equations]) x x x M.seed model.seed_safe

theorem ModelsOn.seed {M : NativeAlgebra A} (model : M.ModelsOn safe) :
    M.seed = M.product M.membership M.domain :=
  model.equations membership_seed (by simp [Templates.equations]) M.seed M.seed M.seed M.seed model.seed_safe

end NativeAlgebra
end PalomarI3334
