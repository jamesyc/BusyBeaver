module
public import ZF192Support.Logic.Source.Bounds
@[expose] public section
namespace ZFR

export PalomarZF192Theory (sourceIff separationFormula functionalityFormula replacementFormula
  allPrefix sepIndex repAIndex repBIndex repCIndex separationSchema replacementSchema)

theorem _root_.PalomarZF192Theory.Bound.rename {a : Formula} {n m : Nat} (ha : Bound a n) (σ : Nat → Nat)
 (hσ : ∀ i, i<n → σ i<m) : Bound (ZFR.rename σ a) m := by
 induction a generalizing n m σ with
 | bot => trivial
 | mem i j => exact ⟨hσ i ha.1,hσ j ha.2⟩
 | eq i j => exact ⟨hσ i ha.1,hσ j ha.2⟩
 | and a b ia ib => exact ⟨ia ha.1 σ hσ,ib ha.2 σ hσ⟩
 | or a b ia ib => exact ⟨ia ha.1 σ hσ,ib ha.2 σ hσ⟩
 | imp a b ia ib => exact ⟨ia ha.1 σ hσ,ib ha.2 σ hσ⟩
 | all a ia =>
   apply ia ha (lift σ)
   intro i hi; cases i with
   | zero => simp [lift]
   | succ i => have hh := hσ i (by omega); simp [lift]; omega
 | ex a ia =>
   apply ia ha (lift σ)
   intro i hi; cases i with
   | zero => simp [lift]
   | succ i => have hh := hσ i (by omega); simp [lift]; omega

theorem bound_allPrefix (n m : Nat) (a : Formula) : Bound (allPrefix n a) m ↔ Bound a (m+n) := by
 induction n generalizing m with
 | zero => simp [allPrefix]
 | succ n ih => simpa [allPrefix, Bound, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (m+1)

theorem separationSchema_closed (n : Nat) (phi : Formula) (h : Bound phi (n+1)) :
 Bound (separationSchema n phi) 0 := by
 have hr : Bound (rename sepIndex phi) (n+3) := h.rename sepIndex (by
   intro i hi; unfold sepIndex; split <;> omega)
 apply (bound_allPrefix n 0 _).mpr
 simpa [separationFormula, sourceIff, Bound, Nat.add_assoc] using hr

theorem replacementSchema_closed (n : Nat) (phi : Formula) (h : Bound phi (n+2)) :
 Bound (replacementSchema n phi) 0 := by
 have ha : Bound (rename repAIndex phi) (n+3) := h.rename repAIndex (by
   intro i hi; unfold repAIndex; split <;> (try split) <;> omega)
 have hb : Bound (rename repBIndex phi) (n+3) := h.rename repBIndex (by
   intro i hi; unfold repBIndex; split <;> (try split) <;> omega)
 have hc : Bound (rename repCIndex phi) (n+4) := h.rename repCIndex (by
   intro i hi; unfold repCIndex; split <;> (try split) <;> omega)
 apply (bound_allPrefix n 0 _).mpr
 simp [replacementFormula, functionalityFormula, sourceIff, Bound, Nat.add_assoc, ha, hb, hc]

/-- Typed counterparts of the exact guarded schema recognizers, not added ND rules. -/
def ClosedSeparation (a : Formula) := Bound a 0 ∧ ∃ phi n, Bound phi (n+1) ∧ a = separationSchema n phi
theorem separationSchema_recognized (n : Nat) (phi : Formula) (h : Bound phi (n+1)) :
 ClosedSeparation (separationSchema n phi) := ⟨separationSchema_closed n phi h, phi,n,h,rfl⟩
def liftN : Nat → (Nat → Nat) → (Nat → Nat)
 | 0, σ => σ
 | n+1, σ => lift (liftN n σ)

theorem liftN_comm (n : Nat) (σ : Nat → Nat) : liftN n (lift σ) = lift (liftN n σ) := by
 induction n <;> simp_all [liftN]

theorem rename_allPrefix (n : Nat) (a : Formula) (σ : Nat → Nat) :
 rename σ (allPrefix n a) = allPrefix n (rename (liftN n σ) a) := by
 induction n generalizing σ with
 | zero => rfl
 | succ n ih => simp [allPrefix, rename, ih, liftN, liftN_comm]

end ZFR
