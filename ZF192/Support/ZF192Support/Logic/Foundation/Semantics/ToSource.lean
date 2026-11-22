module
public import ZF192Support.Logic.Foundation.Syntax.ToSource
@[expose] public section
namespace ZFR.FoundationBridge
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
variable {V : Type*} [SetStructure V]
theorem sourceIndex_eval {n : Nat} (t : Semiterm Language.set Nat n) (s : Nat → V) :
 t.val (fun i => s i.val) (fun j => s (n+j)) = s (termIndex t) := by
 cases t with
 | bvar i => rfl
 | fvar j => rfl
 | func f _ => exact Empty.elim f
theorem pushBound_eval (n : Nat) (s : Nat → V) (x : V) :
 (fun i : Fin (n+1) => pushValue s x i.val) = x :> (fun i : Fin n => s i.val) := by
 funext i
 exact Fin.cases rfl (fun _ => rfl) i
theorem pushFree_eval (n : Nat) (s : Nat → V) (x : V) :
 (fun j => pushValue s x ((n+1)+j)) = (fun j => s (n+j)) := by
 funext j
 have he : (n+1)+j=(n+j)+1 := by omega
 rw [he]
 rfl
/-- Exact semantics of the existing set-syntax→source translation, for all
assignments and formulas. No theoremhood/completeness is used. -/
theorem toSource_eval {n : Nat} (p : Semiformula Language.set Nat n) (s : Nat → V) :
 p.Eval (fun i => s i.val) (fun j => s (n+j)) ↔ eval (fun x y : V => x∈y) (toSource p) s := by
 induction p using Semiformula.rec' generalizing s with
 | hverum => simp [toSource,eval]
 | hfalsum => rfl
 | hrel r v =>
   cases r
   · change (v 0).val _ _ = (v 1).val _ _ ↔ _
     simp [toSource,atom,eval,sourceIndex_eval]
   · change (v 0).val _ _ ∈ (v 1).val _ _ ↔ _
     simp [toSource,atom,eval,sourceIndex_eval]
 | hnrel r v =>
   cases r
   · change ¬((v 0).val _ _ = (v 1).val _ _) ↔ _
     simp [toSource,atom,eval,sourceIndex_eval]
   · change ¬((v 0).val _ _ ∈ (v 1).val _ _) ↔ _
     simp [toSource,atom,eval,sourceIndex_eval]
 | hand p q ihp ihq => simpa [toSource,eval] using and_congr (ihp s) (ihq s)
 | hor p q ihp ihq => simpa [toSource,eval] using or_congr (ihp s) (ihq s)
 | hall p ih =>
   simp only [toSource,eval,Semiformula.eval_all]
   apply forall_congr'
   intro x
   simpa only [pushBound_eval,pushFree_eval] using ih (pushValue s x)
 | hexs p ih =>
   simp only [toSource,eval,Semiformula.eval_ex]
   apply exists_congr
   intro x
   simpa only [pushBound_eval,pushFree_eval] using ih (pushValue s x)
end ZFR.FoundationBridge
