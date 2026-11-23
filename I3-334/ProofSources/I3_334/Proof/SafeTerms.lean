module
public import I3_334.Proof.GuardedAlgebra
public import I3_334Support.Equations.LocalRelationAlgebra
@[expose] public section

namespace PalomarI3334

open PalomarI3380 PalomarI3380.Logic Templates

/-- Closed guarded terms use membership restricted to the rank, equality,
and the Boolean and relation operations. Extra symbols denote top. -/
inductive SafeTerm where
  | seed | one | top
  | neg (t : SafeTerm)
  | converse (t : SafeTerm)
  | nand (t u : SafeTerm)
  | product (t u : SafeTerm)

namespace SafeTerm

def fromOp (tag : Nat) (arguments : List SafeTerm) : SafeTerm :=
  match arguments, tag with
  | [], 3 => .seed
  | [], 5 => .one
  | [t], 3 => .neg t
  | [t], 4 => .converse t
  | [t, u], 3 => .nand t u
  | [t, u], 4 => .product t u
  | _, _ => .top

def ofRaw (t : RawTerm) : SafeTerm := t.fold fromOp

variable {V : Type} (K : V → V → Prop)

def rel : SafeTerm → V → V → Prop
  | .seed => K
  | .one => Eq
  | .top => fun _ _ => True
  | .neg t => fun x y => ¬ rel t x y
  | .converse t => fun x y => rel t y x
  | .nand t u => fun x y => ¬(rel t x y ∧ rel u x y)
  | .product t u => fun x y => ∃ z, rel t x z ∧ rel u z y

open Expanded.LocalTree (spare)

def formula : SafeTerm → Fin 3 → Fin 3 → LocalFormula
  | .seed, i, j => .member i j
  | .one, i, j => .equal i j
  | .top, i, _ => .equal i i
  | .neg t, i, j => .neg (formula t i j)
  | .converse t, i, j => formula t j i
  | .nand t u, i, j => .neg (.conj (formula t i j) (formula u i j))
  | .product t u, i, j => .bind (spare i j)
      (.conj (formula t i (spare i j)) (formula u (spare i j) j))

private theorem spare_distinct (i j : Fin 3) : spare i j ≠ i ∧ spare i j ≠ j := by
  revert i j
  decide +kernel

theorem formula_eval (t : SafeTerm) (env : Fin 3 → V) (i j : Fin 3) :
    LocalFormula.eval K (fun _ => True) (formula t i j) env ↔ t.rel K (env i) (env j) := by
  induction t generalizing i j env with
  | seed | one => rfl
  | top => simp [formula, rel, LocalFormula.eval]
  | neg t ih => rw [formula, LocalFormula.eval, ih, rel]
  | converse t ih => exact ih env j i
  | nand t u it iu => simp only [formula, rel, LocalFormula.eval, it, iu]
  | product t u it iu =>
    have a := (spare_distinct i j).1.symm
    have b := (spare_distinct i j).2.symm
    simp only [formula, rel, LocalFormula.eval, it, iu, LocalFormula.bindValue, a, b,
      ite_true, ite_false, true_and]

end SafeTerm

namespace Logic

/-- Changing the carrier along an injection whose range is the allowed
quantifier domain preserves the meaning of each three-variable formula. -/
theorem eval_along {U V : Type} (f : U → V) (injective : Function.Injective f)
    (E : V → V → Prop) (D : V → Prop) (range : ∀ y, D y ↔ ∃ x, f x = y)
    (p : LocalFormula) (env : Fin 3 → U) :
    LocalFormula.eval (fun x y => E (f x) (f y)) (fun _ => True) p env ↔
      LocalFormula.eval E D p (f ∘ env) := by
  induction p generalizing env with
  | equal i j => exact ⟨congrArg f, fun h => injective h⟩
  | member i j => rfl
  | neg p ih => exact not_congr (ih env)
  | conj p q ip iq => exact and_congr (ip env) (iq env)
  | bind i p ih =>
    have push (x : U) : f ∘ LocalFormula.bindValue env i x =
        LocalFormula.bindValue (f ∘ env) i (f x) := by
      funext j
      by_cases h : j = i <;> simp [LocalFormula.bindValue, h]
    constructor
    · rintro ⟨x, _, hx⟩
      exact ⟨f x, (range _).mpr ⟨x, rfl⟩, push x ▸ (ih _).mp hx⟩
    · rintro ⟨y, hy, hx⟩
      obtain ⟨x, rfl⟩ := (range _).mp hy
      exact ⟨x, trivial, (ih _).mpr ((push x).symm ▸ hx)⟩

end Logic
end PalomarI3334
