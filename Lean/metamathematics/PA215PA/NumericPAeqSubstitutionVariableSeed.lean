module

public import PA215PA.NumericPAeqSubstitutionVariableTransport

@[expose] public section
namespace PA215.PA.RelationalClosedCertificate
noncomputable section
open FFL FFL.FirstOrder RelationalSource ND PairGraph ForwardRelational
attribute [local irreducible] lkBudget isoRightTransportDerivation isoRightTransportClosed

def isoRightTransportReserve : Nat := max 20 (4+lkBudget isoRightTransportDerivation) + (1+Encodable.encode isoRightTransportClosed)
theorem isoRightTransportReserve_code : 1+Encodable.encode isoRightTransportClosed≤isoRightTransportReserve := Nat.le_add_left _ _
theorem isoRightTransportReserve_room : 20≤isoRightTransportReserve :=
  le_trans (le_max_left _ _) (Nat.le_add_right _ _)
theorem isoRightTransportReserve_budget : 4+lkBudget isoRightTransportDerivation≤isoRightTransportReserve :=
  le_trans (le_max_right _ _) (Nat.le_add_right _ _)
attribute [local irreducible] isoRightTransportReserve

def isoRightTransportNativeProof : NativeCalculus.ActualBasis.Proof
    (code isoRightTransportClosed (fun _=>0) 1 isoRightTransportReserve) := by
  unfold isoRightTransportClosed
  apply closeParametersSupplier 3 isoRightTransportOpen
  apply compileContext zeroIsoAxioms isoRightTransportOpen isoRightTransportDerivation _ (1+3) isoRightTransportReserve (by decide)
    (closureLabels_bound 3 (fun _=>0) 1 (by intro; decide)) isoRightTransportReserve_budget
  intro p hp
  classical
  by_cases h0 : p=reflexivityFormula
  · subst p; exact reflexivitySupplier _ _ _
  by_cases h1 : p=symmetryFormula
  · subst p; exact symmetrySupplier _ _ _
  by_cases h2 : p=transitivityFormula
  · subst p; exact transitivitySupplier _ _ _
  have h3 : p=congruenceFormula := by simpa [zeroIsoAxioms,h0,h1,h2] using hp
  subst p
  exact congruenceSupplier _ _ _ (lt_of_lt_of_le (by decide : 1+3+3<20) isoRightTransportReserve_room)
#print axioms isoRightTransportNativeProof
end
end PA215.PA.RelationalClosedCertificate
