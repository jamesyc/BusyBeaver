module
public import RankHullSourceSchemas
@[expose] public section
namespace ZFR

/-- Instantiate the outermost parameter first, preserving all original free
indices below n. This is an actual repeated AllE construction. -/
def restoreParameters : Nat → Formula → Formula
 | 0, a => a
 | n+1, a => restoreParameters n (rename (liftN n (substMap n)) a)

def restoreIndex : Nat → Nat → Nat
 | 0, i => i
 | n+1, i => restoreIndex n (liftN n (substMap n) i)

theorem liftN_index (n : Nat) (σ : Nat → Nat) (i : Nat) :
 liftN n σ i = if i<n then i else n+σ (i-n) := by
 induction n generalizing i with
 | zero => simp [liftN]
 | succ n ih =>
   cases i with
   | zero => simp [liftN, lift]
   | succ i =>
     simp only [liftN, lift, ih]
     split <;> rename_i hi
     · simp [show i+1<n+1 by omega] <;> omega
     · simp [show ¬i+1<n+1 by omega, show i+1-(n+1)=i-n by omega] <;> omega

theorem restoreIndex_eq (n i : Nat) : restoreIndex n i = if i<n then i else i-n := by
 induction n generalizing i with
 | zero => simp [restoreIndex]
 | succ n ih =>
   rw [restoreIndex, ih, liftN_index]
   by_cases hi : i<n
   · simp [hi, show i<n+1 by omega]
   · by_cases he : i=n
     · subst i
       simp [substMap, show ¬n+n<n by omega]
     · have hh : i-n = (i-n-1)+1 := by omega
       rw [if_neg hi, hh, substMap]
       split <;> split <;> omega

theorem restoreParameters_rename (n : Nat) (a : Formula) :
 restoreParameters n a = rename (restoreIndex n) a := by
 induction n generalizing a with
 | zero => exact (rename_id a).symm
 | succ n ih =>
   rw [restoreParameters, ih, rename_comp]
   rfl

theorem restoreParameters_bound (n : Nat) (a : Formula) (h : Bound a n) :
 restoreParameters n a = a := by
 rw [restoreParameters_rename, rename_agree a n h (restoreIndex n) id]
 · exact rename_id a
 · intro i hi; simp [restoreIndex_eq, hi]

theorem nd_restoreParameters {Γ : Context} (n : Nat) (a : Formula)
 (h : ND (.seq Γ (allPrefix n a))) : ND (.seq Γ (restoreParameters n a)) := by
 induction n generalizing a with
 | zero => exact h
 | succ n ih =>
   apply ih
   have hh := ND.allE n h
   simpa only [allPrefix, subst, rename_allPrefix] using hh

theorem nd_declose {Γ : Context} (n : Nat) (a : Formula) (ha : Bound a n)
 (h : ND (.seq Γ (allPrefix n a))) : ND (.seq Γ a) := by
 have hh := nd_restoreParameters n a h
 simpa only [restoreParameters_bound n a ha] using hh

theorem nd_separation_declose {Γ : Context} (n : Nat) (phi : Formula)
 (hphi : Bound phi (n+1)) (hs : separationSchema n phi ∈ Γ) :
 ND (.seq Γ (separationFormula (rename sepIndex phi))) := by
 apply nd_declose n
 · simpa only [Nat.zero_add] using (bound_allPrefix n 0 _).mp (separationSchema_closed n phi hphi)
 · exact ND.ctx hs

theorem nd_replacement_declose {Γ : Context} (n : Nat) (phi : Formula)
 (hphi : Bound phi (n+2)) (hs : replacementSchema n phi ∈ Γ) :
 ND (.seq Γ (replacementFormula (rename repAIndex phi) (rename repBIndex phi) (rename repCIndex phi))) := by
 apply nd_declose n
 · simpa only [Nat.zero_add] using (bound_allPrefix n 0 _).mp (replacementSchema_closed n phi hphi)
 · exact ND.ctx hs

end ZFR
