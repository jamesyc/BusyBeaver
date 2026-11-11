module
public import M6PA.Theory
public import M6PA.Calibration.RelationalClosedCertificateCoherenceSuccessor
@[expose] public section
namespace M6.PA.RelationalClosedCertificate
noncomputable section
open FFL FFL.FirstOrder RelationalSource ND PairGraph ForwardRelational
attribute [local irreducible] lkBudget successorIsoClosed

def successorIsoReserve : Nat := max 20 (max (7+lkBudget adjunctionDerivation)
  (5+lkBudget (orderIsoSuccessorDerivation 3 2 1 0))) + (1+Encodable.encode successorIsoClosed)
theorem successorIsoReserve_code : 1+Encodable.encode successorIsoClosed≤successorIsoReserve := Nat.le_add_left _ _
theorem successorIsoReserve_room : 20≤successorIsoReserve :=
  le_trans (le_max_left _ _) (Nat.le_add_right _ _)
theorem successorIsoReserve_adj : 7+lkBudget adjunctionDerivation≤successorIsoReserve :=
  le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (Nat.le_add_right _ _)
theorem successorIsoReserve_budget : 5+lkBudget (orderIsoSuccessorDerivation 3 2 1 0)≤successorIsoReserve :=
  le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (Nat.le_add_right _ _)
attribute [local irreducible] successorIsoReserve

def successorIsoNativeProof : NativeCalculus.ActualBasis.Proof
    (code successorIsoClosed (fun _=>0) 1 successorIsoReserve) := by
  unfold successorIsoClosed
  apply closeParametersSupplier 4 (orderIsoSuccessorStatement 3 2 1 0)
  exact orderIsoSuccessorSupplier 3 2 1 0 _ (1+4) successorIsoReserve (by decide)
    (closureLabels_bound 4 (fun _=>0) 1 (by intro; decide))
    (lt_of_lt_of_le (by decide : 1+4+6<20) successorIsoReserve_room)
    successorIsoReserve_adj successorIsoReserve_budget
#print axioms successorIsoNativeProof
end
end M6.PA.RelationalClosedCertificate

