import PA215.OriginalCertified

namespace PA215.Census

/-- Each stored index is intrinsically bound to its original census data. -/
abbrev OriginalRegistry := List (Σ i : Fin 5134, OriginalCertified i)

/-- A lookup transports only along a proved equality of census indices. -/
def OriginalRegistry.lookup : OriginalRegistry → (i : Fin 5134) → Option (OriginalCertified i)
  | [], _ => none
  | ⟨j, c⟩ :: rest, i =>
      if h : j = i then some (h ▸ c) else OriginalRegistry.lookup rest i

/-- Registry coverage reduces to finite index coverage, independently of the
large proof objects. Duplicate entries do not manufacture coverage. -/
theorem OriginalRegistry.lookup_isSome (entries : OriginalRegistry) (i : Fin 5134) :
    (entries.lookup i).isSome = true ↔ i ∈ entries.map Sigma.fst := by
  induction entries with
  | nil => simp [OriginalRegistry.lookup]
  | cons entry rest ih =>
      rcases entry with ⟨j, c⟩
      by_cases h : j = i
      · subst i
        simp [OriginalRegistry.lookup]
      · simp [OriginalRegistry.lookup, h, ih, Ne.symm h]

/-- Finite index coverage provides an actual certificate of the exact original
full-frame obligation, not merely a boolean registry label. -/
theorem OriginalRegistry.covered (entries : OriginalRegistry) (i : Fin 5134)
    (hi : i ∈ entries.map Sigma.fst) : Nonempty (OriginalCertified i) := by
  have h := (entries.lookup_isSome i).2 hi
  cases he : entries.lookup i with
  | none => simp [he] at h
  | some c => exact ⟨c⟩

end PA215.Census
