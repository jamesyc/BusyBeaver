module
public import ZF192Support.Logic.Foundation.Syntax.FromSource
public import Foundation.FirstOrder.SetTheory.BST.BST
@[expose] public section
namespace ZFR.FoundationBridge
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
def certificateAssignment {V : Type*} (n : Nat) (b : Fin n → V) (s : Nat → V) (i : Nat) : V :=
 if hi : i<n then b ⟨i,hi⟩ else s (i-n)

theorem certificateTerm_val {V : Type*} [SetStructure V] (n i : Nat) (b : Fin n → V) (s : Nat → V) :
 Semiterm.val b s (sourceTerm n i) = certificateAssignment n b s i := by
 unfold sourceTerm certificateAssignment
 split <;> rfl

theorem certificateAssignment_cons {V : Type*} (n : Nat) (b : Fin n → V) (s : Nat → V) (x : V) :
 certificateAssignment (n+1) (x :> b) s = pushValue (certificateAssignment n b s) x := by
 funext i
 cases i with
 | zero => simp [certificateAssignment,pushValue]
 | succ i =>
   simp only [certificateAssignment,pushValue,Nat.succ_lt_succ_iff]
   split <;> rename_i hi
   · rfl
   · simp [Nat.succ_sub_succ_eq_sub]

theorem certificate_ofSource_eval {V : Type*} [SetStructure V] (p : ZFR.Formula)
 (n : Nat) (b : Fin n → V) (s : Nat → V) :
 Semiformula.Eval b s (ofSource n p) ↔
 ZFR.eval (fun x y : V => x ∈ y) p (certificateAssignment n b s) := by
 induction p generalizing n with
 | bot => rfl
 | mem i j =>
   change (Semiterm.val b s (sourceTerm n i) ∈ Semiterm.val b s (sourceTerm n j)) ↔ _
   rw [certificateTerm_val,certificateTerm_val]; rfl
 | eq i j =>
   change (Semiterm.val b s (sourceTerm n i) = Semiterm.val b s (sourceTerm n j)) ↔ _
   rw [certificateTerm_val,certificateTerm_val]; rfl
 | and p q ip iq =>
   change (Semiformula.Eval b s (ofSource n p) ∧ Semiformula.Eval b s (ofSource n q)) ↔ _
   exact and_congr (ip n b) (iq n b)
 | or p q ip iq =>
   change (Semiformula.Eval b s (ofSource n p) ∨ Semiformula.Eval b s (ofSource n q)) ↔ _
   exact or_congr (ip n b) (iq n b)
 | imp p q ip iq =>
   change (Semiformula.Eval b s (Semiformula.neg (ofSource n p)) ∨ Semiformula.Eval b s (ofSource n q)) ↔ _
   have hn : Semiformula.Eval b s (Semiformula.neg (ofSource n p)) ↔ ¬Semiformula.Eval b s (ofSource n p) := by
     change Semiformula.EvalAux (standardStructure V) s b (Semiformula.neg (ofSource n p)) ↔
       ¬Semiformula.EvalAux (standardStructure V) s b (ofSource n p)
     rw [← Semiformula.neg_eq, Semiformula.EvalAux_neg]
   rw [hn,ip,iq]
   exact (imp_iff_not_or).symm
 | all p ip =>
   change (∀ x : V, Semiformula.Eval (x :> b) s (ofSource (n+1) p)) ↔ _
   apply forall_congr'; intro x
   rw [ip,certificateAssignment_cons]
 | ex p ip =>
   change (∃ x : V, Semiformula.Eval (x :> b) s (ofSource (n+1) p)) ↔ _
   apply exists_congr; intro x
   rw [ip,certificateAssignment_cons]


end ZFR.FoundationBridge
