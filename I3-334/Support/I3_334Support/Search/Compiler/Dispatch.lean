module
public import Std
@[expose] public section

namespace PalomarI3380.Compiler.Source

/-- Saturating dispatch. A selector above the final index arrives at
the final branch with a nonzero residual in the selector register. -/
def selectBranch {α : Type} : List α → Nat → Option (α × Nat)
  | [], _ => none
  | [p], n => some (p, n)
  | p :: _ :: _, 0 => some (p, 0)
  | _ :: q :: qs, n + 1 => selectBranch (q :: qs) n

theorem selectBranch_exists {α : Type} (ps : List α) (n : Nat) (hn : ps ≠ []) :
    ∃ p r, selectBranch ps n = some (p, r) := by
  induction ps generalizing n with
  | nil => exact (hn rfl).elim
  | cons p ps ih =>
    cases ps with
    | nil => exact ⟨p, n, rfl⟩
    | cons q qs =>
      cases n with
      | zero => exact ⟨p, 0, rfl⟩
      | succ n => exact ih n (by simp)

theorem selectBranch_mem {α : Type} {ps : List α} {n : Nat} {p : α} {r : Nat}
    (chosen : selectBranch ps n = some (p, r)) : p ∈ ps := by
  induction ps generalizing n with
  | nil => simp [selectBranch] at chosen
  | cons h rest ih =>
    cases rest with
    | nil => simp_all [selectBranch]
    | cons g gs =>
      cases n with
      | zero => simp_all [selectBranch]
      | succ n => exact List.mem_cons_of_mem _ (ih chosen)

theorem selectBranch_map {α β : Type} (f : α → β) (ps : List α) (n : Nat) :
    selectBranch (ps.map f) n =
      (selectBranch ps n).map (fun (p, r) => (f p, r)) := by
  induction ps generalizing n with
  | nil => rfl
  | cons p ps ih =>
    cases ps with
    | nil => rfl
    | cons q qs => cases n <;> first | rfl | exact ih _

theorem selectBranch_exact {α : Type} (ps : List α) (n : Nat) (hn : n < ps.length) :
    selectBranch ps n = some (ps[n], 0) := by
  induction ps generalizing n with
  | nil => simp at hn
  | cons p ps ih =>
    cases ps with
    | nil =>
      have eq : n = 0 := by simpa using hn
      subst n
      rfl
    | cons q qs =>
      cases n with
      | zero => rfl
      | succ n => exact ih n (by simpa using hn)

end PalomarI3380.Compiler.Source
