module
public import DirectSubstTraversal
public import DirectRawPremiseBuilder
@[expose] public section
namespace RosserDirect.SubstitutionRow
open Turing Segment FourStack
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
inductive Q where
 | swap (q : OperandSwap.Control)
 | subst (q : SubstTraversal.Q)
 | move (q : Grammar.CopyControl TypedBlock.Control)
 | row (q : FramedRowConstructor.Control)
 | done
 deriving DecidableEq, Fintype, Inhabited

def machine : Q → Stmt4 Q
 | .swap .done => .goto (fun _ => .subst (.prepare (.reverse .formulaTag)))
 | .swap q => Routine.relocate dataRoles Q.swap (OperandSwap.machine q)
 | .subst .done => .goto (fun _ => .move (.scan (.run 0 .start)))
 | .subst q => Routine.relocate id Q.subst (SubstTraversal.machine q)
 | .move .done => .goto (fun _ => .row (.formula0 0))
 | .move q => Routine.relocate outputRoles Q.move (TypedBlock.moveMachine q)
 | .row .done => .goto (fun _ => .done)
 | .row q => Routine.relocate dataRoles Q.row (FramedRowConstructor.machine false q)
 | .done => .halt

theorem agree_swap q (h : OperandSwap.machine q ≠ .halt) :
 machine (.swap q) = Routine.relocate dataRoles Q.swap (OperandSwap.machine q) := by
 cases q <;> simp_all [machine,OperandSwap.machine]
theorem agree_subst q (h : SubstTraversal.machine q ≠ .halt) :
 machine (.subst q) = Routine.relocate id Q.subst (SubstTraversal.machine q) := by
 cases q <;> simp_all [machine,SubstTraversal.machine]
theorem agree_move q (h : TypedBlock.moveMachine q ≠ .halt) :
 machine (.move q) = Routine.relocate outputRoles Q.move (TypedBlock.moveMachine q) := by
 cases q <;> simp_all [machine,TypedBlock.moveMachine,GrammarMove.machine]
theorem agree_row q (h : FramedRowConstructor.machine false q ≠ .halt) :
 machine (.row q) = Routine.relocate dataRoles Q.row (FramedRowConstructor.machine false q) := by
 cases q <;> simp_all [machine,FramedRowConstructor.machine]

/-- Actual substitution and sequent construction, with arbitrary stream and data tails.
This is the allE result/exI expected-premise builder, not yet an opcode rule. -/
theorem substituted_row (Γ : ZFR.Context) (f : ZFR.Formula) (t : Nat)
 (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches machine
 (cfg4 (.swap (.first (.scan (.run 0 .start)))) v p
  (TypedContext.value (.nat t) ++ TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ a) [] c)
 (cfg4 .done none p a [] (FramedRow.encode (.seq Γ (ZFR.subst t f)) ++ c)) := by
 have h0 := Routine.lift_embedded_run dataRoles data_injective Q.swap OperandSwap.machine machine agree_swap (fun _ => p)
  (OperandSwap.swap_fields (.formula f) (.nat t) v (TypedContext.value (.context Γ) ++ a) c) (by simp [config])
 simp only [embed_data] at h0
 have l0 : TM2.Reaches machine
  (cfg4 (.swap .done) none p (TypedContext.value (.formula f) ++ TypedContext.value (.nat t) ++ (TypedContext.value (.context Γ) ++ a)) [] c)
  (cfg4 (.subst (.prepare (.reverse .formulaTag))) none p (TypedContext.value (.formula f) ++ TypedContext.value (.nat t) ++ (TypedContext.value (.context Γ) ++ a)) [] c) := Relation.ReflTransGen.single rfl
 have h1 := relabel_run Q.subst SubstTraversal.machine machine agree_subst _ _ _ _ _ _ _ _ _ _ _ _
  (SubstTraversal.subst_formula f t none p (TypedContext.value (.context Γ) ++ a) c)
 have l1 : TM2.Reaches machine
  (cfg4 (.subst .done) none p (TypedContext.value (.context Γ) ++ a) [] (TypedContext.value (.formula (ZFR.subst t f)) ++ c))
  (cfg4 (.move (.scan (.run 0 .start))) none p (TypedContext.value (.context Γ) ++ a) [] (TypedContext.value (.formula (ZFR.subst t f)) ++ c)) := Relation.ReflTransGen.single rfl
 have h2 := Routine.lift_embedded_run outputRoles output_injective Q.move TypedBlock.moveMachine machine agree_move (fun _ => p)
  (TypedBlock.move_block 0 [.formula (ZFR.subst t f)] rfl none c (TypedContext.value (.context Γ) ++ a)) (by simp [config])
 simp only [embed_output,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil] at h2
 have l2 : TM2.Reaches machine
  (cfg4 (.move .done) none p (TypedContext.value (.formula (ZFR.subst t f)) ++ (TypedContext.value (.context Γ) ++ a)) [] c)
  (cfg4 (.row (.formula0 0)) none p (TypedContext.value (.formula (ZFR.subst t f)) ++ (TypedContext.value (.context Γ) ++ a)) [] c) := Relation.ReflTransGen.single rfl
 have h3 := Routine.lift_embedded_run dataRoles data_injective Q.row (FramedRowConstructor.machine false) machine agree_row (fun _ => p)
  (FramedRowConstructor.construct_seq_raw Γ (ZFR.subst t f) none a c) (by simp [config])
 simp only [embed_data] at h3
 have l3 : TM2.Reaches machine
  (cfg4 (.row .done) none p a [] (FramedRow.encode (.seq Γ (ZFR.subst t f)) ++ c))
  (cfg4 .done none p a [] (FramedRow.encode (.seq Γ (ZFR.subst t f)) ++ c)) := Relation.ReflTransGen.single rfl
 simp only [TM2.Reaches,List.append_assoc] at h0 l0 h1 l1 h2 l2 h3 l3 ⊢
 exact h0.trans (l0.trans (h1.trans (l1.trans (h2.trans (l2.trans (h3.trans l3))))))

end RosserDirect.SubstitutionRow
