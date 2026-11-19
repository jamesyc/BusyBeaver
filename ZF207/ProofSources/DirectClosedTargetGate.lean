module
public import DirectScopeGuard
@[expose] public section
namespace RosserDirect.ClosedTargetGate
open Turing Segment FourStack
set_option backward.isDefEq.respectTransparency false
inductive Q where
 | save (q : Label) | seed | restore (q : Label)
 | scope (q : ScopeGuard.Q) | drop (q : Grammar.DropControl TypedBlock.Control)
 | accept | reject
 deriving DecidableEq, Fintype, Inhabited

def machine : Q → Stmt4 Q
 | .save .done => .goto (fun _ => .seed)
 | .save q => Routine.relocate dataRoles Q.save (RosserDirect.machine q)
 | .seed => .push .data (fun _ => .frameEnd) (.push .data (fun _ => .tokenEnd)
   (.push .data (fun _ => .tokenEnd) (.goto (fun _ => .restore .scan))))
 | .restore .done => .goto (fun _ => .scope .start)
 | .restore q => Routine.relocate outputRoles Q.restore (RosserDirect.machine q)
 | .scope .accept => .goto (fun _ => .drop (.scan (.run 1 .start)))
 | .scope .reject => .goto (fun _ => .reject)
 | .scope q => Routine.relocate id Q.scope (ScopeGuard.machine q)
 | .drop .done => .load (fun _ => none) (.goto (fun _ => .accept))
 | .drop q => Routine.relocate dataRoles Q.drop (TypedBlock.dropMachine q)
 | .accept | .reject => .halt

theorem agree_save q (h : RosserDirect.machine q ≠ .halt) :
 machine (.save q) = Routine.relocate dataRoles Q.save (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]
theorem agree_restore q (h : RosserDirect.machine q ≠ .halt) :
 machine (.restore q) = Routine.relocate outputRoles Q.restore (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]
theorem agree_scope q (h : ScopeGuard.machine q ≠ .halt) :
 machine (.scope q) = Routine.relocate id Q.scope (ScopeGuard.machine q) := by
 cases q <;> simp_all [machine,ScopeGuard.machine]
theorem agree_drop q (h : TypedBlock.dropMachine q ≠ .halt) :
 machine (.drop q) = Routine.relocate dataRoles Q.drop (TypedBlock.dropMachine q) := by
 cases q <;> simp_all [machine,TypedBlock.dropMachine,Grammar.dropMachine]
theorem move_formula (f : ZFR.Formula) (v : Option Symbol) (a c : List Symbol) :
 TM2.Reaches RosserDirect.machine (config Label.scan v (TypedContext.value (.formula f) ++ a) [] c)
  (config Label.done none a [] (TypedContext.value (.formula f) ++ c)) := by
 simpa [TM2.Reaches,cfg,config,TypedContext.value,valueSymbols,List.append_assoc] using
   RosserDirect.move_frame (payloadBits (valueTokens (.formula f))) (payloadBits_no_end _) v a c

theorem prepare (f : ZFR.Formula) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches machine
 (cfg4 (.save .scan) v p (TypedContext.value (.formula f) ++ a) [] c)
 (cfg4 (.scope .start) none p (TypedContext.stack [.formula f,.nat 0] ++ a) [] c) := by
 have h0 := Routine.lift_embedded_run dataRoles data_injective Q.save RosserDirect.machine machine agree_save (fun _ => p)
  (move_formula f v a c) (by simp [config])
 simp only [embed_data] at h0
 have h1 : TM2.Reaches machine (cfg4 (.save .done) none p a [] (TypedContext.value (.formula f) ++ c))
  (cfg4 .seed none p a [] (TypedContext.value (.formula f) ++ c)) := Relation.ReflTransGen.single rfl
 have h2 : TM2.Reaches machine (cfg4 .seed none p a [] (TypedContext.value (.formula f) ++ c))
  (cfg4 (.restore .scan) none p (TypedContext.value (.nat 0) ++ a) [] (TypedContext.value (.formula f) ++ c)) := Relation.ReflTransGen.single (by
   simp [machine,cfg4,TM2.step,TM2.stepAux,store4,TypedContext.value,tokenBits]
   funext j; cases j <;> rfl)
 have h3 := Routine.lift_embedded_run outputRoles output_injective Q.restore RosserDirect.machine machine agree_restore (fun _ => p)
  (move_formula f none c (TypedContext.value (.nat 0) ++ a)) (by simp [config])
 simp only [embed_output] at h3
 have h4 : TM2.Reaches machine (cfg4 (.restore .done) none p (TypedContext.stack [.formula f,.nat 0] ++ a) [] c)
  (cfg4 (.scope .start) none p (TypedContext.stack [.formula f,.nat 0] ++ a) [] c) := Relation.ReflTransGen.single rfl
 simp only [TM2.Reaches,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] at h0 h1 h2 h3 h4 ⊢
 exact h0.trans (h1.trans (h2.trans (h3.trans h4)))

theorem accepts (f : ZFR.Formula) (hf : ZFR.Bound f 0)
 (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches machine
 (cfg4 (.save .scan) v p (TypedContext.value (.formula f) ++ a) [] c)
 (cfg4 .accept none p a [] c) := by
 have h0 := prepare f v p (a) c
 have h1 := relabel_run Q.scope ScopeGuard.machine machine agree_scope _ _ _ _ _ _ _ _ _ _ _ _
  (ScopeGuard.accept f 0 hf none p (a) c)
 have h2 : TM2.Reaches machine
  (cfg4 (.scope .accept) (some .frameEnd) p (TypedContext.stack [.formula f,.nat 0] ++ (a)) [] c)
  (cfg4 (.drop (.scan (.run 1 .start))) (some .frameEnd) p (TypedContext.stack [.formula f,.nat 0] ++ (a)) [] c) := Relation.ReflTransGen.single rfl
 obtain ⟨w,h⟩ := TypedBlock.drop_block 1 [.formula f,.nat 0] rfl (some .frameEnd) (a) [] c
 have h3 := Routine.lift_embedded_run dataRoles data_injective Q.drop TypedBlock.dropMachine machine agree_drop (fun _ => p) h (by simp [config])
 simp only [embed_data] at h3
 have h4 : TM2.Reaches machine (cfg4 (.drop .done) w p (a) [] c)
  (cfg4 .accept none p a [] c) := Relation.ReflTransGen.single rfl
 simp only [TM2.Reaches,List.append_assoc] at h0 h1 h2 h3 h4 ⊢
 exact h0.trans (h1.trans (h2.trans (h3.trans h4)))


abbrev RejectTrace (start : Cfg4 Q) := ∃ w p a c, TM2.Reaches machine start (cfg4 .reject w p a [] c)
theorem rejects (f : ZFR.Formula) (hf : ¬ZFR.Bound f 0)
 (v : Option Symbol) (p a c : List Symbol) :
 RejectTrace (cfg4 (.save .scan) v p (TypedContext.value (.formula f) ++ a) [] c) := by
 have h0 := prepare f v p a c
 obtain ⟨w,p',a',h⟩ := ScopeGuard.reject f 0 hf none p a c
 have h1 := relabel_run Q.scope ScopeGuard.machine machine agree_scope _ _ _ _ _ _ _ _ _ _ _ _ h
 have h2 : TM2.Reaches machine (cfg4 (.scope .reject) w p' a' [] c) (cfg4 .reject w p' a' [] c) := Relation.ReflTransGen.single rfl
 exact ⟨w,p',a',c,h0.trans (h1.trans h2)⟩

end RosserDirect.ClosedTargetGate
