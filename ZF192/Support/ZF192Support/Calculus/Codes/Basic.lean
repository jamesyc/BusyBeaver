module
public import Std
@[expose] public section
namespace CCodeSoundness
universe u
variable {α : Type u}
abbrev Assignment (α : Type u) := Nat → α
def update (s : Assignment α) (i : Nat) (x : α) : Assignment α :=
  fun j => if j = i then x else s j

theorem update_same (s : Assignment α) (i : Nat) (x y : α) :
    update (update s i x) i y = update s i y := by
  funext j
  by_cases h : j = i <;> simp [update, h]

theorem update_restore (s : Assignment α) (i : Nat) : update s i (s i) = s := by
  funext j
  by_cases h : j = i
  · subst j; simp [update]
  · simp [update, h]

theorem update_commute (s : Assignment α) (i j : Nat) (h : i ≠ j) (x y : α) :
    update (update s i x) j y = update (update s j y) i x := by
  funext k
  by_cases hi : k = i
  · subst k; simp [update, h]
  · by_cases hj : k = j
    · subst k; simp [update, hi]
    · simp [update, hi, hj]

def All (i : Nat) (P : Assignment α → Prop) (s : Assignment α) : Prop :=
  ∀ x, P (update s i x)

theorem head1_sound (i : Nat) (P Q : Assignment α → Prop) (s : Assignment α) :
    All i P s → All i (fun t => P t → Q t) s → All i Q s := by
  intro hp hpq x
  exact hpq x (hp x)

theorem head2_sound (d h : Nat) (s : Assignment α) :
    ¬ All d (fun t => ¬ t h = t d) s := by
  intro hn
  apply hn (s h)
  by_cases hd : h = d
  · subst h; rfl
  · simp [update, hd]

theorem head3_sound (mem : α → α → Prop) (a d h : Nat) (s : Assignment α) :
    s h = s d → mem (s a) (s h) → mem (s a) (s d) := by
  intro he hm
  exact he ▸ hm

theorem head4_sound (mem : α → α → Prop) (a d h : Nat) (s : Assignment α) :
    mem (s h) (s d) → s h = s a → mem (s a) (s d) := by
  intro hm he
  exact he ▸ hm

theorem head5_sound (a d : Nat) (P : Assignment α → Prop) (s : Assignment α) :
    All d (All a P) s → All a (All d P) s := by
  intro hp
  by_cases h : a = d
  · subst a; exact hp
  · intro x y
    have hh := hp y x
    rw [update_commute s d a (Ne.symm h) y x] at hh
    exact hh

theorem head6_sound (d : Nat) (P : Assignment α → Prop) (s : Assignment α) :
    (¬ All d (fun t => ¬ All d P t) s) → P s := by
  intro hn
  apply Classical.byContradiction
  intro hp
  apply hn
  intro x hall
  have h := hall (s d)
  rw [update_same, update_restore] at h
  exact hp h

theorem rho8_sound (A D H U : Prop) :
    ((H → U) → D) → (D → H) → A → H := by
  intro h hd _
  apply Classical.byContradiction
  intro hn
  have hu : H → U := fun hH => False.elim (hn hH)
  exact hn (hd (h hu))

end CCodeSoundness
