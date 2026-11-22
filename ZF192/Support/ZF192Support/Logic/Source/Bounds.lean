module
public import ZF192Support.Logic.Source.Deduction
@[expose] public section
namespace ZFR

export PalomarZF192Theory (Bound)

theorem rename_agree (p : Formula) (n : Nat) (h : Bound p n)
    (σ τ : Nat → Nat) (agree : ∀ i, i < n → σ i = τ i) :
    rename σ p = rename τ p := by
  induction p generalizing n σ τ with
  | bot => rfl
  | mem i j => simp [rename, agree i h.1, agree j h.2]
  | eq i j => simp [rename, agree i h.1, agree j h.2]
  | and p q ihp ihq => simp only [rename, ihp n h.1 σ τ agree, ihq n h.2 σ τ agree]
  | or p q ihp ihq => simp only [rename, ihp n h.1 σ τ agree, ihq n h.2 σ τ agree]
  | imp p q ihp ihq => simp only [rename, ihp n h.1 σ τ agree, ihq n h.2 σ τ agree]
  | all p ih =>
      simp only [rename]
      congr 1
      apply ih (n+1) h (lift σ) (lift τ)
      intro i hi
      cases i with
      | zero => rfl
      | succ i => simpa only [lift] using congrArg Nat.succ (agree i (by omega))
  | ex p ih =>
      simp only [rename]
      congr 1
      apply ih (n+1) h (lift σ) (lift τ)
      intro i hi
      cases i with
      | zero => rfl
      | succ i => simpa only [lift] using congrArg Nat.succ (agree i (by omega))

theorem rename_closed (p : Formula) (h : Bound p 0) (σ : Nat → Nat) : rename σ p = p := by
  rw [rename_agree p 0 h σ id (by intro i hi; omega), rename_id]

def ClosedContext (Γ : Context) : Prop := ∀ p, p ∈ Γ → Bound p 0

theorem renameContext_closed {Γ : Context} (h : ClosedContext Γ) (σ : Nat → Nat) :
    renameContext σ Γ = Γ := by
  induction Γ with
  | nil => rfl
  | cons p ps ih =>
      have hp := h p (by simp)
      have ht : ClosedContext ps := by
        intro q hq
        exact h q (by simp [hq])
      simp only [renameContext, List.map_cons, rename_closed p hp σ]
      exact congrArg (List.cons p) (ih ht)

theorem shiftContext_closed {Γ : Context} (h : ClosedContext Γ) : shiftContext Γ = Γ :=
  renameContext_closed h Nat.succ

end ZFR
