module
public import I3_380.Equations
import I3_380.Meredith
@[expose] public section

namespace PalomarI3380
namespace Algebra

open Manifest

theorem involution_of_basis {A : Type} (M : Algebra A)
    (b1 : M.Satisfies meredith1) (b2 : M.Satisfies meredith2) (x : A) :
    M.neg (M.neg x) = x := by
  let meet (x y : A) := M.neg (M.nand x y)
  apply complement_involution meet M.neg _ _ x
  · intro x y
    exact b1 (fun i => if i.val = 0 then x else y)
  · intro x y z
    exact b2 (fun i => if i.val = 0 then x else if i.val = 1 then y else z)

/-- Interpret the two eliminated constants via closed terms. -/
def withStages {A : Type} (M : Algebra A) : Algebra A :=
  let subset := M.eval (fun x : Empty => x.elim) (Manifest.subset : Term Empty)
  { M with constant := fun
      | .T => subset
      | .S => M.product (M.converse (M.choice subset)) (M.choice subset)
      | c => M.constant c }

private theorem eval_subset {A V W : Type} (M : Algebra A) (v : V → A) (w : W → A) :
    M.eval v (Manifest.subset : Term V) = M.eval w (Manifest.subset : Term W) := rfl

theorem eval_expand {A V : Type} (M : Algebra A) (v : V → A) (t : Term V) :
    M.eval v (Manifest.expand t) = M.withStages.eval v t := by
  induction t with
  | const c => cases c <;> rfl
  | var => rfl
  | neg _ ih | converse _ ih | choice _ ih | localRel _ ih =>
      simp only [Manifest.expand, Algebra.eval, ih, withStages]
  | nand _ _ h₁ h₂ | product _ _ h₁ h₂ =>
      simp only [Manifest.expand, Algebra.eval, h₁, h₂, withStages]
  | node _ _ _ h₁ h₂ h₃ =>
      simp only [Manifest.expand, Algebra.eval, h₁, h₂, h₃, withStages]

theorem withStages_models_definitions {A : Type} (M : Algebra A) :
    M.withStages.Satisfies defineSubset ∧ M.withStages.Satisfies defineStages :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem withStages_eq {A : Type} (M : Algebra A)
    (sub : M.Satisfies defineSubset) (stages : M.Satisfies defineStages) :
    M.withStages = M := by
  have hT := sub (fun _ => M.constant .U)
  change M.constant .T = M.eval (fun (_ : Fin 3) => M.constant .U) subset at hT
  have hS := stages (fun _ => M.constant .U)
  have h : M.withStages.constant = M.constant := by
    funext c
    cases c <;> try rfl
    · exact hT.symm
    · change M.product (M.converse (M.choice (M.eval (fun x : Empty => x.elim) subset)))
        (M.choice (M.eval (fun x : Empty => x.elim) subset)) = M.constant .S
      rw [eval_subset M _ (fun (_ : Fin 3) => M.constant .U), ← hT]
      exact hS.symm
  cases M
  simp only [withStages] at h ⊢
  rw [h]

theorem satisfies_cancel {A : Type} (M : Algebra A) (inv : ∀ x, M.neg (M.neg x) = x)
    (lhs rhs : Term (Fin 3)) :
    M.Satisfies (cancel lhs rhs) ↔ M.Satisfies (lhs, rhs) := by
  induction lhs generalizing rhs with
  | neg lhs ih =>
      cases rhs <;> try rfl
      case neg rhs =>
        rw [cancel, ih]
        constructor
        · intro h v
          exact congrArg M.neg (h v)
        · intro h v
          have hh := congrArg M.neg (h v)
          change M.neg (M.neg (M.eval v lhs)) = M.neg (M.neg (M.eval v rhs)) at hh
          simpa only [inv] using hh
  | _ => cases rhs <;> rfl

theorem satisfies_reduce {A : Type} (M : Algebra A) (inv : ∀ x, M.neg (M.neg x) = x)
    (e : Equation) : M.Satisfies (reduce e) ↔ M.withStages.Satisfies e := by
  rcases e with ⟨lhs, rhs⟩
  rw [reduce, satisfies_cancel M inv]
  simp only [Satisfies, eval_expand]

private theorem final_models {A : Type} (M : Algebra A) :
    M.Models final ↔ M.Satisfies meredith1 ∧ M.Satisfies meredith2 ∧
      ∀ e ∈ retained, M.Satisfies (reduce e) := by
  rw [final]
  simp only [Models, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map, or_imp, forall_and, forall_eq]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, rest⟩
    exact ⟨h₁, h₂, fun e he => rest (reduce e) ⟨e, he, rfl⟩⟩
  · rintro ⟨h₁, h₂, rest⟩
    exact ⟨⟨h₁, h₂⟩, fun e ⟨a, ha, he⟩ => he ▸ rest a ha⟩

private theorem preceding_models {A : Type} (M : Algebra A) :
    M.Models preceding ↔ M.Satisfies meredith1 ∧ M.Satisfies meredith2 ∧
      M.Satisfies defineSubset ∧ M.Satisfies defineStages ∧ M.Models retained := by
  simp [Models, preceding, or_imp, forall_and]

theorem models_final_iff {A : Type} (M : Algebra A) :
    M.Models final ↔ M.withStages.Models preceding := by
  rw [final_models, preceding_models]
  have b₁ : M.withStages.Satisfies meredith1 ↔ M.Satisfies meredith1 := Iff.rfl
  have b₂ : M.withStages.Satisfies meredith2 ↔ M.Satisfies meredith2 := Iff.rfl
  rw [b₁, b₂]
  have ⟨dT, dS⟩ := M.withStages_models_definitions
  constructor
  · rintro ⟨h₁, h₂, rest⟩
    exact ⟨h₁, h₂, dT, dS, fun e he =>
      (M.satisfies_reduce (M.involution_of_basis h₁ h₂) e).mp (rest e he)⟩
  · rintro ⟨h₁, h₂, _, _, rest⟩
    exact ⟨h₁, h₂, fun e he =>
      (M.satisfies_reduce (M.involution_of_basis h₁ h₂) e).mpr (rest e he)⟩

theorem models_final_of_preceding {A : Type} (M : Algebra A)
    (h : M.Models preceding) : M.Models final := by
  have hh := (preceding_models M).mp h
  apply M.models_final_iff.mpr
  rw [M.withStages_eq hh.2.2.1 hh.2.2.2.1]
  exact h

/-- The 19- and 21-equation presentations have the same countermodels to
the unchanged target `D = J`, up to interpreting the defined constants. -/
theorem countermodel_iff {A : Type} :
    (∃ M : Algebra A, M.Models final ∧ M.constant .D ≠ M.constant .J) ↔
    (∃ M : Algebra A, M.Models preceding ∧ M.constant .D ≠ M.constant .J) := by
  constructor
  · rintro ⟨M, h, hne⟩
    exact ⟨M.withStages, M.models_final_iff.mp h, hne⟩
  · rintro ⟨M, h, hne⟩
    exact ⟨M, M.models_final_of_preceding h, hne⟩

end Algebra
end PalomarI3380
