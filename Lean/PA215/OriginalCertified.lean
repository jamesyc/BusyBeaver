import PA215.OriginalCensus
import PA215.CertifiedContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.Census
open PA215.Runtime PA215.Contracts PA215.Zip PA215.NativeTable
attribute [local irreducible] originalAt

/-- A certificate is indexed by the exact original census, not by an unchecked
registry label. The terminal obligation is deliberately not represented here. -/
structure OriginalCertified (i : Fin 5134) where
  target : SConf
  target_eq : (originalAt i).target = some target
  fuel : Nat
  accepted : check fuel ⟨(originalAt i).branch, (originalAt i).initial, target⟩ = true

/-- The entire original frame advances positively, for arbitrary padding,
register values and spare cells satisfying precisely the original branch. -/
theorem OriginalCertified.sound (c : OriginalCertified i) (n : Nat) (vs : List Nat)
    (hv : Valid (originalAt i).branch vs) :
    Reach1 machine (conc n vs (originalAt i).initial) (conc n vs c.target) :=
  Contracts.sound c.fuel _ c.accepted n vs hv

theorem RawOriginal.toContract_fields (r : RawOriginal) (c : Contract)
    (h : r.toContract = some c) :
    r.target = some c.target ∧ r.branch = c.branch ∧ r.initial = c.initial := by
  cases ht : r.target with
  | none => simp [RawOriginal.toContract, ht] at h
  | some t =>
      simp only [RawOriginal.toContract, ht, Option.map_some, Option.some.injEq] at h
      cases h
      exact ⟨rfl, rfl, rfl⟩

/-- Conversion requires actual census data equality; a matching numeric ID alone
is insufficient. -/
def OriginalCertified.ofContract (i : Fin 5134) (c : Contract) (fuel : Nat)
    (binding : (originalAt i).toContract = some c)
    (accepted : check fuel c = true) : OriginalCertified i := by
  obtain ⟨ht, hb, hi⟩ := RawOriginal.toContract_fields (originalAt i) c binding
  refine ⟨c.target, ht, fuel, ?_⟩
  cases c
  simpa only [hb, hi] using accepted

end PA215.Census
