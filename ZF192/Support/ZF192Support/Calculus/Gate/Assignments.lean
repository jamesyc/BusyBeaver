module
public import ZF192Support.Calculus.Codes.HeadEvaluation
@[expose] public section
namespace CCodeSoundness
universe u
variable {α : Type u}

theorem update_shadow (s : Assignment α) (i j : Nat) (x y z : α) :
    update (update (update s i x) j y) i z = update (update s j y) i z := by
  funext k
  by_cases h : k = i
  · subst k; simp [update]
  · simp [update, h]

theorem evalCode_erase_self_under_two (n i j : Nat) (hni : n ≠ i) (hnj : n ≠ j)
    (mem : α → α → Prop) (s : Assignment α) (c x y : α) :
    evalCode mem n (update (update (update s n c) i x) j y) ↔
      evalCode mem n (update (update s i x) j y) := by
  rw [update_commute s n i hni c x,
    update_commute (update s i x) n j hnj c y]
  exact evalCode_self_independent n mem (update (update s i x) j y) c

end CCodeSoundness
