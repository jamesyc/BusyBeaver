module
public import RankHullDiagonalLogic
@[expose] public section
namespace ZFR

def parameterBound : Formula → Nat
 | .bot => 0
 | .mem i j => max i j + 1
 | .eq i j => max i j + 1
 | .and a b => max (parameterBound a) (parameterBound b)
 | .or a b => max (parameterBound a) (parameterBound b)
 | .imp a b => max (parameterBound a) (parameterBound b)
 | .all a => parameterBound a
 | .ex a => parameterBound a

theorem Bound.mono {a : Formula} {n m : Nat} (h : Bound a n) (hnm : n ≤ m) : Bound a m := by
 induction a generalizing n m with
 | bot => trivial
 | mem i j => exact ⟨Nat.lt_of_lt_of_le h.1 hnm,Nat.lt_of_lt_of_le h.2 hnm⟩
 | eq i j => exact ⟨Nat.lt_of_lt_of_le h.1 hnm,Nat.lt_of_lt_of_le h.2 hnm⟩
 | and a b ia ib => exact ⟨ia h.1 hnm,ib h.2 hnm⟩
 | or a b ia ib => exact ⟨ia h.1 hnm,ib h.2 hnm⟩
 | imp a b ia ib => exact ⟨ia h.1 hnm,ib h.2 hnm⟩
 | all a ia => exact ia h (by omega)
 | ex a ia => exact ia h (by omega)

theorem parameterBound_valid (a : Formula) : Bound a (parameterBound a) := by
 induction a with
 | bot => trivial
 | mem i j => simp [Bound,parameterBound]; omega
 | eq i j => simp [Bound,parameterBound]; omega
 | and a b ia ib => exact ⟨ia.mono (Nat.le_max_left _ _),ib.mono (Nat.le_max_right _ _)⟩
 | or a b ia ib => exact ⟨ia.mono (Nat.le_max_left _ _),ib.mono (Nat.le_max_right _ _)⟩
 | imp a b ia ib => exact ⟨ia.mono (Nat.le_max_left _ _),ib.mono (Nat.le_max_right _ _)⟩
 | all a ia => exact ia.mono (by simp [parameterBound])
 | ex a ia => exact ia.mono (by simp [parameterBound])

theorem all_formula_diagonal_certificate (phi : Formula) (i : Nat) :
 ClosedSeparation (separationSchema (parameterBound phi) phi) ∧
 ClosedContext (parameterizedSeparationContext (parameterBound phi) phi) ∧
 ND (.seq (parameterizedSeparationContext (parameterBound phi) phi)
   (.ex (diagonalPointedBody i phi))) :=
 parameterized_diagonal_certificate (parameterBound phi) phi
   ((parameterBound_valid phi).mono (by omega)) i

end ZFR
