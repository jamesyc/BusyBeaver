module
public import ZF192Support.Logic.Source.Definitions
@[expose] public section
namespace ZFR

export PalomarZF192Theory (Formula lift rename shift substMap subst eval pushValue)

namespace Formula
export PalomarZF192Theory.Formula (bot mem eq and or imp all ex)
end Formula

@[simp] theorem lift_zero (σ : Nat → Nat) : lift σ 0 = 0 := rfl
@[simp] theorem lift_succ (σ : Nat → Nat) (n : Nat) : lift σ (n+1) = σ n+1 := rfl

theorem lift_comp (σ τ : Nat → Nat) : lift (σ ∘ τ) = lift σ ∘ lift τ := by
 funext n; cases n <;> rfl
@[simp] theorem lift_id : lift id = id := by funext n; cases n <;> rfl

theorem rename_comp (σ τ : Nat → Nat) (a : Formula) :
 rename σ (rename τ a) = rename (σ ∘ τ) a := by
 induction a generalizing σ τ with
 | bot => rfl
 | mem i j => rfl
 | eq i j => rfl
 | and a b ia ib => simp only [rename, ia, ib]
 | or a b ia ib => simp only [rename, ia, ib]
 | imp a b ia ib => simp only [rename, ia, ib]
 | all a ih => simp only [rename, ih, lift_comp]
 | ex a ih => simp only [rename, ih, lift_comp]
@[simp] theorem rename_id (a : Formula) : rename id a = a := by
 induction a with
 | bot => rfl
 | mem i j => rfl
 | eq i j => rfl
 | and a b ia ib => simp only [rename, ia, ib]
 | or a b ia ib => simp only [rename, ia, ib]
 | imp a b ia ib => simp only [rename, ia, ib]
 | all a ih => simp only [rename, lift_id, ih]
 | ex a ih => simp only [rename, lift_id, ih]

theorem rename_shift (σ : Nat → Nat) (a : Formula) :
 rename (lift σ) (shift a) = shift (rename σ a) := by
 simp only [shift, rename_comp]
 rfl

theorem rename_subst (σ : Nat → Nat) (t : Nat) (a : Formula) :
 rename σ (subst t a) = subst (σ t) (rename (lift σ) a) := by
 simp only [subst, rename_comp]
 congr 1
 funext n; cases n <;> rfl

end ZFR
