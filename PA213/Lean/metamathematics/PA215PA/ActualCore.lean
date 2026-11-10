import PA215.Source.ActualAXCode
import PA215.Source.Enumeration
import PA215PA.NativeCalculus

/-! Finite proof trees for the AX fragment used to derive rho7. The available rules are R1, R2, R6, R8, quantified R7, modus ponens, and generalization. -/
namespace PA215.PA.NativeCalculus.ActualCore

def quantifiedR7 (a b c : Nat) :=
  wim (weq c a) (wim (weq c b) (wal (wel a b) (weq a b)))

attribute [local irreducible] rho1 rho2 rho6 rho8 quantifiedR7
set_option maxHeartbeats 1000000 in
inductive Proof : Nat → Type where
  | mp {a b} : Proof a → Proof (wim a b) → Proof b
  | all (a) {b} : Proof b → Proof (wal a b)
  | r1 (a b) : Proof (rho1 a b)
  | r2 (a b c) : Proof (rho2 a b c)
  | r6 (a b) : Proof (rho6 a b)
  | r7 (a b c) : Proof (quantifiedR7 a b c)
  | r8 (a b c u) : u ≤ a → Proof (rho8 a b c u)

theorem quantifiedR7_eq_actual (a b c : Nat) :
    quantifiedR7 a b c = PA215.Source.ActualAXCode.rho7 a b c := by
  simp only [quantifiedR7,PA215.Source.ActualAXCode.rho7,
    PA215.Source.AXCode.wim,PA215.Source.AXCode.wal,PA215.Source.AXCode.weq,PA215.Source.AXCode.wel,
    wim,wal,weq,wel]

theorem r1_eq_actual (a b : Nat) : rho1 a b = PA215.Source.ActualAXCode.rho1 a b := by
  simp only [rho1,PA215.Source.ActualAXCode.rho1,PA215.Source.AXCode.rho1,
    wex,PA215.Source.AXCode.wex,wn,PA215.Source.AXCode.wn,wal,PA215.Source.AXCode.wal,
    wim,PA215.Source.AXCode.wim,weq,PA215.Source.AXCode.weq]

theorem r2_eq_actual (a b c : Nat) : rho2 a b c = PA215.Source.ActualAXCode.rho2 a b c := by
  simp only [rho2,PA215.Source.ActualAXCode.rho2,PA215.Source.AXCode.rho2,
    wim,PA215.Source.AXCode.wim,wal,PA215.Source.AXCode.wal]

theorem r6_eq_actual (a b : Nat) : rho6 a b = PA215.Source.ActualAXCode.rho6 a b := by
  simp only [rho6,PA215.Source.ActualAXCode.rho6,PA215.Source.AXCode.rho6,
    wex,PA215.Source.AXCode.wex,wn,PA215.Source.AXCode.wn,wal,PA215.Source.AXCode.wal,
    wim,PA215.Source.AXCode.wim]

theorem r8_eq_actual (a b c u : Nat) : rho8 a b c u = PA215.Source.ActualAXCode.rho8 a b c u := by
  simp only [rho8,PA215.Source.ActualAXCode.rho8,PA215.Source.AXCode.rho8,wim,PA215.Source.AXCode.wim]

#print axioms quantifiedR7_eq_actual
end PA215.PA.NativeCalculus.ActualCore
