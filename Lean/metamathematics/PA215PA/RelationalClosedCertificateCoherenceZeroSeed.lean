module

public import PA215PA.RelationalClosedCertificateCoherenceZero

@[expose] public section
namespace PA215.PA.RelationalClosedCertificate
noncomputable section
open FFL FFL.FirstOrder RelationalSource ND PairGraph ForwardRelational
attribute [local irreducible] lkBudget zeroIsoDerivation zeroIsoClosed

def zeroIsoReserve : Nat := max 20 (3+lkBudget zeroIsoDerivation) + (1+Encodable.encode zeroIsoClosed)
theorem zeroIsoReserve_code : 1+Encodable.encode zeroIsoClosed≤zeroIsoReserve := Nat.le_add_left _ _
theorem zeroIsoReserve_room : 20≤zeroIsoReserve :=
  le_trans (le_max_left _ _) (Nat.le_add_right _ _)
theorem zeroIsoReserve_budget : 3+lkBudget zeroIsoDerivation≤zeroIsoReserve :=
  le_trans (le_max_right _ _) (Nat.le_add_right _ _)
attribute [local irreducible] zeroIsoReserve

def zeroIsoNativeProof : NativeCalculus.ActualBasis.Proof
    (code zeroIsoClosed (fun _=>0) 1 zeroIsoReserve) := by
  unfold zeroIsoClosed
  apply closeParametersSupplier 2 zeroIsoOpen
  apply compileContext zeroIsoAxioms zeroIsoOpen zeroIsoDerivation _ (1+2) zeroIsoReserve (by decide)
    (closureLabels_bound 2 (fun _=>0) 1 (by intro; decide)) zeroIsoReserve_budget
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
  exact congruenceSupplier _ _ _ (lt_of_lt_of_le (by decide : 1+2+3<20) zeroIsoReserve_room)
#print axioms zeroIsoNativeProof
end
end PA215.PA.RelationalClosedCertificate
