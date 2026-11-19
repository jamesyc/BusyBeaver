module
public import DirectRowSwap
public import DirectRawPremiseBuilder
public import DirectBinaryConstructors
@[expose] public section
namespace RosserDirect.DisjElimPremises
open Turing Segment
set_option backward.isDefEq.respectTransparency false
inductive Control where
 | copy (q : Grammar.CopyControl TypedBlock.Control)
 | branches (q : FramedRowConstructor.Control)
 | moveRow (q : Grammar.CopyControl FramedRowEquality.Control)
 | drop (q : Grammar.DropControl TypedBlock.Control)
 | binary (q : Binary.Control)
 | moveFormula (q : Grammar.CopyControl TypedBlock.Control)
 | seq (q : FramedRowConstructor.Control)
 | swapOut (q : RowSwap.Control)
 | done
 deriving DecidableEq, Fintype, Inhabited

def machine : Control → Stmt Control
 | .copy .done => .goto (fun _ => .branches (.formula0 2))
 | .copy q => Routine.relocate id Control.copy ((TypedBlock.machine) q)
 | .branches .done => .goto (fun _ => .moveRow (.scan .tag))
 | .branches q => Routine.relocate SelectSecond.swap Control.branches ((FramedRowConstructor.machine true) q)
 | .moveRow .done => .goto (fun _ => .drop (.scan (.run 0 .start)))
 | .moveRow q => Routine.relocate id Control.moveRow ((FramedRowMove.machine) q)
 | .drop .done => .goto (fun _ => .binary .boot)
 | .drop q => Routine.relocate id Control.drop ((TypedBlock.dropMachine) q)
 | .binary .done => .goto (fun _ => .moveFormula (.scan (.run 0 .start)))
 | .binary q => Routine.relocate id Control.binary ((Binary.machine 9) q)
 | .moveFormula .done => .goto (fun _ => .seq (.formula0 0))
 | .moveFormula q => Routine.relocate SelectSecond.swap Control.moveFormula ((TypedBlock.moveMachine) q)
 | .seq .done => .goto (fun _ => .swapOut (.first (.scan .tag)))
 | .seq q => Routine.relocate id Control.seq ((FramedRowConstructor.machine false) q)
 | .swapOut .done => .goto (fun _ => .done)
 | .swapOut q => Routine.relocate SelectSecond.swap Control.swapOut ((RowSwap.machine) q)
 | .done => .halt

theorem agree_copy (q : Grammar.CopyControl TypedBlock.Control) (h : (TypedBlock.machine) q ≠ .halt) :
 machine (.copy q) = Routine.relocate id Control.copy ((TypedBlock.machine) q) := by
 cases q <;> simp_all [machine,TypedBlock.machine,Grammar.copyMachine]

theorem embed_copy (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.copy (config q v a b c) (fun _ => []) = config (.copy q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_branches (q : FramedRowConstructor.Control) (h : (FramedRowConstructor.machine true) q ≠ .halt) :
 machine (.branches q) = Routine.relocate SelectSecond.swap Control.branches ((FramedRowConstructor.machine true) q) := by
 cases q <;> simp_all [machine,FramedRowConstructor.machine]

theorem embed_branches (q : FramedRowConstructor.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed SelectSecond.swap Control.branches (config q v a b c) (fun _ => []) = config (.branches q) v c b a := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_moveRow (q : Grammar.CopyControl FramedRowEquality.Control) (h : (FramedRowMove.machine) q ≠ .halt) :
 machine (.moveRow q) = Routine.relocate id Control.moveRow ((FramedRowMove.machine) q) := by
 cases q <;> simp_all [machine,FramedRowMove.machine,GrammarMove.machine]

theorem embed_moveRow (q : Grammar.CopyControl FramedRowEquality.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.moveRow (config q v a b c) (fun _ => []) = config (.moveRow q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_drop (q : Grammar.DropControl TypedBlock.Control) (h : (TypedBlock.dropMachine) q ≠ .halt) :
 machine (.drop q) = Routine.relocate id Control.drop ((TypedBlock.dropMachine) q) := by
 cases q <;> simp_all [machine,TypedBlock.dropMachine,Grammar.dropMachine]

theorem embed_drop (q : Grammar.DropControl TypedBlock.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.drop (config q v a b c) (fun _ => []) = config (.drop q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_binary (q : Binary.Control) (h : (Binary.machine 9) q ≠ .halt) :
 machine (.binary q) = Routine.relocate id Control.binary ((Binary.machine 9) q) := by
 cases q <;> simp_all [machine,Binary.machine]

theorem embed_binary (q : Binary.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.binary (config q v a b c) (fun _ => []) = config (.binary q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_moveFormula (q : Grammar.CopyControl TypedBlock.Control) (h : (TypedBlock.moveMachine) q ≠ .halt) :
 machine (.moveFormula q) = Routine.relocate SelectSecond.swap Control.moveFormula ((TypedBlock.moveMachine) q) := by
 cases q <;> simp_all [machine,TypedBlock.moveMachine,GrammarMove.machine]

theorem embed_moveFormula (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed SelectSecond.swap Control.moveFormula (config q v a b c) (fun _ => []) = config (.moveFormula q) v c b a := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_seq (q : FramedRowConstructor.Control) (h : (FramedRowConstructor.machine false) q ≠ .halt) :
 machine (.seq q) = Routine.relocate id Control.seq ((FramedRowConstructor.machine false) q) := by
 cases q <;> simp_all [machine,FramedRowConstructor.machine]

theorem embed_seq (q : FramedRowConstructor.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.seq (config q v a b c) (fun _ => []) = config (.seq q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_swapOut (q : RowSwap.Control) (h : (RowSwap.machine) q ≠ .halt) :
 machine (.swapOut q) = Routine.relocate SelectSecond.swap Control.swapOut ((RowSwap.machine) q) := by
 cases q <;> simp_all [machine,RowSwap.machine]

theorem embed_swapOut (q : RowSwap.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed SelectSecond.swap Control.swapOut (config q v a b c) (fun _ => []) = config (.swapOut q) v c b a := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

abbrev field (a : ZFR.Formula) := TypedContext.value (.formula a)
abbrev context (Γ : ZFR.Context) := TypedContext.value (.context Γ)

theorem or_local (a b : ZFR.Formula) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches (Binary.machine 9)
 (config .boot v (field b ++ field a ++ src) [] dst)
 (config .done none src [] (field (.or a b) ++ dst)) := by
 have h := Binary.assemble 9 (payloadBits (valueTokens (.formula a))) (Membership.formulaPayload b)
   (payloadBits_no_end _) (payloadBits_no_end _) v src dst
 have hb : tokenBits 1 = [.bit1,.tokenEnd] := by decide
 simpa [field,TypedContext.value,valueSymbols,valueTokens,Membership.formulaPayload,
   ZFR.TokenVM.emitFormula,payloadBits,List.flatMap_append,List.append_assoc,hb] using h

/-- Construct branch row above disjunction sequent, the exact de premise order. -/
theorem construct (Γ : ZFR.Context) (a b c : ZFR.Formula) (v : Option Symbol)
 (src dst : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (config (.copy (.scan (.run 3 .start))) v (TypedContext.stack (.formula c :: .formula b :: .formula a :: .context Γ :: src)) [] (TypedContext.stack dst))
 (config .done none (TypedContext.stack src) [] (FramedRow.encode (.branches Γ a b c) ++ FramedRow.encode (.seq Γ (.or a b)) ++ TypedContext.stack dst)) := by
 let orig := .formula c :: .formula b :: .formula a :: .context Γ :: src
 let rb := FramedRow.encode (.branches Γ a b c)
 let rs := FramedRow.encode (.seq Γ (.or a b))
 have h0 := Routine.lift_embedded_run id Function.injective_id Control.copy TypedBlock.machine machine agree_copy (fun _ => [])
   (TypedBlock.copy_block 3 [.formula c,.formula b,.formula a,.context Γ] rfl v (TypedContext.stack src) (TypedContext.stack dst)) (by simp [config])
 simp only [embed_copy] at h0
 have l0 : TM2.Reaches machine
   (config (.copy .done) none (TypedContext.stack orig) [] (TypedContext.stack (.formula c :: .formula b :: .formula a :: .context Γ :: dst)))
   (config (.branches (.formula0 2)) none (TypedContext.stack orig) [] (TypedContext.stack (.formula c :: .formula b :: .formula a :: .context Γ :: dst))) := Relation.ReflTransGen.single rfl
 have h1 := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective Control.branches (FramedRowConstructor.machine true) machine agree_branches (fun _ => [])
   (FramedRowConstructor.construct_branches Γ a b c none dst (TypedContext.stack orig)) (by simp [config])
 simp only [embed_branches] at h1
 have l1 : TM2.Reaches machine
   (config (.branches .done) none (rb ++ TypedContext.stack orig) [] (TypedContext.stack dst))
   (config (.moveRow (.scan .tag)) none (rb ++ TypedContext.stack orig) [] (TypedContext.stack dst)) := Relation.ReflTransGen.single rfl
 have h2 := Routine.lift_embedded_run id Function.injective_id Control.moveRow FramedRowMove.machine machine agree_moveRow (fun _ => [])
   (FramedRowMove.move_row (.branches Γ a b c) none (TypedContext.stack orig) (TypedContext.stack dst)) (by simp [config])
 simp only [embed_moveRow] at h2
 have l2 : TM2.Reaches machine
   (config (.moveRow .done) none (TypedContext.stack orig) [] (rb ++ TypedContext.stack dst))
   (config (.drop (.scan (.run 0 .start))) none (TypedContext.stack orig) [] (rb ++ TypedContext.stack dst)) := Relation.ReflTransGen.single rfl
 obtain ⟨w,h⟩ := TypedBlock.drop_block 0 [.formula c] rfl none (TypedContext.stack (.formula b :: .formula a :: .context Γ :: src)) [] (rb ++ TypedContext.stack dst)
 have h3 := Routine.lift_embedded_run id Function.injective_id Control.drop TypedBlock.dropMachine machine agree_drop (fun _ => []) h (by simp [config])
 simp only [embed_drop] at h3
 have l3 : TM2.Reaches machine
   (config (.drop .done) w (TypedContext.stack (.formula b :: .formula a :: .context Γ :: src)) [] (rb ++ TypedContext.stack dst))
   (config (.binary .boot) w (TypedContext.stack (.formula b :: .formula a :: .context Γ :: src)) [] (rb ++ TypedContext.stack dst)) := Relation.ReflTransGen.single rfl
 have h4 := Routine.lift_embedded_run id Function.injective_id Control.binary (Binary.machine 9) machine agree_binary (fun _ => [])
   (or_local a b w (TypedContext.stack (.context Γ :: src)) (rb ++ TypedContext.stack dst)) (by simp [config])
 simp only [embed_binary] at h4
 have l4 : TM2.Reaches machine
   (config (.binary .done) none (TypedContext.stack (.context Γ :: src)) [] (field (.or a b) ++ rb ++ TypedContext.stack dst))
   (config (.moveFormula (.scan (.run 0 .start))) none (TypedContext.stack (.context Γ :: src)) [] (field (.or a b) ++ rb ++ TypedContext.stack dst)) := Relation.ReflTransGen.single rfl
 have h5 := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective Control.moveFormula TypedBlock.moveMachine machine agree_moveFormula (fun _ => [])
   (TypedBlock.move_block 0 [.formula (.or a b)] rfl none (rb ++ TypedContext.stack dst) (TypedContext.stack (.context Γ :: src))) (by simp [config])
 simp only [embed_moveFormula] at h5
 have l5 : TM2.Reaches machine
   (config (.moveFormula .done) none (TypedContext.stack (.formula (.or a b) :: .context Γ :: src)) [] (rb ++ TypedContext.stack dst))
   (config (.seq (.formula0 0)) none (TypedContext.stack (.formula (.or a b) :: .context Γ :: src)) [] (rb ++ TypedContext.stack dst)) := Relation.ReflTransGen.single rfl
 have h6 := Routine.lift_embedded_run id Function.injective_id Control.seq (FramedRowConstructor.machine false) machine agree_seq (fun _ => [])
   (FramedRowConstructor.construct_seq Γ (.or a b) none src (rb ++ TypedContext.stack dst)) (by simp [config])
 simp only [embed_seq] at h6
 have l6 : TM2.Reaches machine
   (config (.seq .done) none (TypedContext.stack src) [] (rs ++ rb ++ TypedContext.stack dst))
   (config (.swapOut (.first (.scan .tag))) none (TypedContext.stack src) [] (rs ++ rb ++ TypedContext.stack dst)) := Relation.ReflTransGen.single rfl
 have h7 := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective Control.swapOut RowSwap.machine machine agree_swapOut (fun _ => [])
   (RowSwap.swap_rows (.branches Γ a b c) (.seq Γ (.or a b)) none (TypedContext.stack dst) (TypedContext.stack src)) (by simp [config])
 simp only [embed_swapOut] at h7
 have l7 : TM2.Reaches machine
   (config (.swapOut .done) none (TypedContext.stack src) [] (rb ++ rs ++ TypedContext.stack dst))
   (config .done none (TypedContext.stack src) [] (rb ++ rs ++ TypedContext.stack dst)) := Relation.ReflTransGen.single rfl
 simp only [TM2.Reaches,orig,rb,rs,field,context,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] at h0 l0 h1 l1 h2 l2 h3 l3 h4 l4 h5 l5 h6 l6 h7 l7 ⊢
 exact h0.trans (l0.trans (h1.trans (l1.trans (h2.trans (l2.trans (h3.trans (l3.trans (h4.trans (l4.trans (h5.trans (l5.trans (h6.trans (l6.trans (h7.trans l7))))))))))))))

end RosserDirect.DisjElimPremises
