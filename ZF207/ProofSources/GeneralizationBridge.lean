module
public import SourceND
public import NumericTranslation
@[expose] public section
namespace ZFR

def Bound : Formula → Nat → Prop
  | .bot, _ => True
  | .mem i j, n => i < n ∧ j < n
  | .eq i j, n => i < n ∧ j < n
  | .and p q, n => Bound p n ∧ Bound q n
  | .or p q, n => Bound p n ∧ Bound q n
  | .imp p q, n => Bound p n ∧ Bound q n
  | .all p, n => Bound p (n+1)
  | .ex p, n => Bound p (n+1)

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

/-- A concrete derivation of the named C-GEN rule using only the exact source
    ND renaming theorem and eigenvariable-respecting AllI. -/
theorem nd_generalize_code {Γ : Context} (closed : ClosedContext Γ) (i n : Nat)
    (proof : ND (.seq Γ (translateCode id n))) :
    ND (.seq Γ (translateCode id (4*C207Soundness.cantor n i+2))) := by
  rw [translateCode_gen]
  apply ND.allI
  have renamed := proof.rename (generalizeMap i)
  simp only [renameRow, renameContext_closed closed] at renamed
  simpa only [shiftContext_closed closed] using renamed

end ZFR
