module
public import PropositionalTemplates
@[expose] public section
namespace ZFR

theorem subst_lift_shift (p : Formula) :
    subst 0 (rename (lift Nat.succ) p) = p := by
  unfold subst
  rw [rename_comp]
  have h : substMap 0 ∘ lift Nat.succ = id := by
    funext n; cases n <;> rfl
  rw [h, rename_id]

/-- Universal distribution derived using the source eigenvariable rule.
No validity-to-provability principle or logical axiom has been added. -/
theorem nd_all_distribution (Γ : Context) (p q : Formula) :
    ND (.seq Γ (.imp (.all p) (.imp (.all (.imp p q)) (.all q)))) := by
  apply ND.ii
  apply ND.ii
  apply ND.allI
  have hp : ND (.seq (shiftContext (.all (.imp p q) :: .all p :: Γ)) p) := by
    have h := ND.allE 0 (ND.ctx (Γ := shiftContext (.all (.imp p q) :: .all p :: Γ))
      (a := .all (rename (lift Nat.succ) p)) (by simp [shiftContext, shift, rename]))
    simpa only [subst_lift_shift] using h
  have hi : ND (.seq (shiftContext (.all (.imp p q) :: .all p :: Γ)) (.imp p q)) := by
    have h := ND.allE 0 (ND.ctx (Γ := shiftContext (.all (.imp p q) :: .all p :: Γ))
      (a := .all (rename (lift Nat.succ) (.imp p q))) (by simp [shiftContext, shift, rename]))
    simpa only [subst_lift_shift] using h
  exact ND.ie hi hp

end ZFR
