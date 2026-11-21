module
public import Std
@[expose] public section

namespace PalomarI3380

inductive Constant where
  | D | J | U | E | I | T | S
  deriving DecidableEq, Repr

inductive Term (Var : Type) where
  | var : Var → Term Var
  | const : Constant → Term Var
  | neg : Term Var → Term Var
  | converse : Term Var → Term Var
  | choice : Term Var → Term Var
  | localRel : Term Var → Term Var
  | nand : Term Var → Term Var → Term Var
  | product : Term Var → Term Var → Term Var
  | node : Term Var → Term Var → Term Var → Term Var
  deriving DecidableEq, Repr

def Term.subst {V W : Type} (σ : V → Term W) : Term V → Term W
  | .var x => σ x
  | .const c => .const c
  | .neg x => .neg (x.subst σ)
  | .converse x => .converse (x.subst σ)
  | .choice x => .choice (x.subst σ)
  | .localRel x => .localRel (x.subst σ)
  | .nand x y => .nand (x.subst σ) (y.subst σ)
  | .product x y => .product (x.subst σ) (y.subst σ)
  | .node x y z => .node (x.subst σ) (y.subst σ) (z.subst σ)

structure Algebra (A : Type) where
  constant : Constant → A
  neg : A → A
  converse : A → A
  choice : A → A
  localRel : A → A
  nand : A → A → A
  product : A → A → A
  node : A → A → A → A

def Algebra.inf {A : Type} (M : Algebra A) (x y : A) : A := M.neg (M.nand x y)

def Algebra.eval {A V : Type} (M : Algebra A) (v : V → A) : Term V → A
  | .var x => v x
  | .const c => M.constant c
  | .neg x => M.neg (M.eval v x)
  | .converse x => M.converse (M.eval v x)
  | .choice x => M.choice (M.eval v x)
  | .localRel x => M.localRel (M.eval v x)
  | .nand x y => M.nand (M.eval v x) (M.eval v y)
  | .product x y => M.product (M.eval v x) (M.eval v y)
  | .node x y z => M.node (M.eval v x) (M.eval v y) (M.eval v z)

theorem Algebra.eval_subst {A V W : Type} (M : Algebra A) (v : W → A)
    (σ : V → Term W) (t : Term V) :
    M.eval v (t.subst σ) = M.eval (fun x => M.eval v (σ x)) t := by
  induction t <;> simp_all [Term.subst, Algebra.eval]

abbrev Equation := Term (Fin 3) × Term (Fin 3)

def Algebra.Satisfies {A : Type} (M : Algebra A) (e : Equation) : Prop :=
  ∀ v : Fin 3 → A, M.eval v e.1 = M.eval v e.2

def Algebra.Models {A : Type} (M : Algebra A) (equations : List Equation) : Prop :=
  ∀ e ∈ equations, M.Satisfies e

namespace Manifest

open Term

local infixl:70 " ⋆ " => product

def a : Term (Fin 3) := .var 0
def b : Term (Fin 3) := .var 1
def c : Term (Fin 3) := .var 2
def meet {V : Type} (x y : Term V) : Term V := neg (nand x y)
def subset {V : Type} : Term V := neg (converse (const .E) ⋆ neg (const .E))
def stage {V : Type} (t : Term V) : Term V := converse (choice t) ⋆ choice t

def meredith1 : Equation := (meet (neg (meet (neg a) b)) a, a)
def meredith2 : Equation := (meet (neg (meet (neg a) b)) (meet c b), meet b (meet c a))

def defineSubset : Equation := (const .T, subset)
def defineStages : Equation := (const .S, stage (const .T))

def productAssociative : Equation := (a ⋆ (b ⋆ c), (a ⋆ b) ⋆ c)
def rightIdentity : Equation := (a ⋆ const .I, a)
def converseInvolution : Equation := (converse (converse a), a)
def productMonotonicity : Equation := (meet (a ⋆ b) (a ⋆ meet c b), a ⋆ meet c b)
def converseMeet : Equation := (converse (meet a b), meet (converse a) (converse b))
def peirce : Equation := (meet (converse a ⋆ neg (a ⋆ b)) b, neg (const .U))

def extensionality : Equation := (meet (const .T) (converse (const .T)), const .I)

def choiceSub : Equation := (meet (choice a) a, choice a)

def choiceFunctional : Equation :=
  (meet (converse (choice a) ⋆ choice a) (neg (const .I)), neg (const .U))

def choiceDomain : Equation := (choice a ⋆ const .U, a ⋆ const .U)

def imageEquation : Equation :=
  let e := const .E
  let u := const .U
  let image := converse e ⋆ choice a
  (meet (neg (image ⋆ neg e)) (neg (neg image ⋆ e)) ⋆ u, u)

def defineDomain : Equation := (const .D, meet (const .I) (const .J ⋆ const .U))

def stageLaw : Equation :=
  let back := converse (const .E)
  let s := const .S
  (s ⋆ back, s ⋆ back ⋆ s ⋆ converse (const .T))

def domainClosed : Equation :=
  let d := const .D
  (d, meet (const .I) (const .E ⋆ meet (const .S) d ⋆ const .U))

/-- Non-Meredith rows of the 21-equation NAND presentation, with the two
definition equations recorded separately. The order of the equations is
immaterial to the equational theory. -/
def retained : List Equation :=
  let e := const .E
  let i := const .I
  let u := const .U
  let d := const .D
  let j := const .J
  [
    productAssociative,
    rightIdentity,
    converseInvolution,
    productMonotonicity,
    converseMeet,
    peirce,
    extensionality,
    choiceSub,
    choiceFunctional,
    choiceDomain,
    imageEquation,
    defineDomain,
    stageLaw,
    domainClosed,
    (localRel i, e ⋆ d),                                                 -- h-seed1
    (localRel (node a b c),
      meet (localRel a ⋆ converse (localRel b)) (nand (localRel b) (localRel c))),
    (meet (converse j ⋆ localRel a ⋆ j) (neg (localRel a)), neg u)         -- h-pres
  ]

def preceding : List Equation :=
  [meredith1, meredith2, defineSubset, defineStages] ++ retained

def expand {V : Type} : Term V → Term V
  | .const .T => subset
  | .const .S => stage subset
  | .const c => .const c
  | .var v => .var v
  | .neg x => .neg (expand x)
  | .converse x => .converse (expand x)
  | .choice x => .choice (expand x)
  | .localRel x => .localRel (expand x)
  | .nand x y => .nand (expand x) (expand y)
  | .product x y => .product (expand x) (expand y)
  | .node x y z => .node (expand x) (expand y) (expand z)

def cancel (lhs rhs : Term (Fin 3)) : Equation :=
  match lhs, rhs with
  | .neg l, .neg r => cancel l r
  | l, r => (l, r)

def reduce (eq : Equation) : Equation := cancel (expand eq.1) (expand eq.2)

/-- The 19 raw equations of I3-380. The exact Meredith rows are retained. -/
def final : List Equation := [meredith1, meredith2] ++ retained.map reduce

theorem counts : preceding.length = 21 ∧ final.length = 19 := by decide

end Manifest
end PalomarI3380
