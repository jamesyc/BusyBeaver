module
public import DirectShiftTraversal
public import DirectReverseContext
@[expose] public section
namespace RosserDirect.ShiftContext
open Turing Segment FourStack
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

inductive Q where
 | prepare (q : ReverseContext.Q) | seed | uncons (q : ContextUncons.Control)
 | move (q : Label) | shift (q : ShiftTraversal.Q)
 | untag0 | untag1 | tagResult | done | reject
 deriving DecidableEq, Fintype, Inhabited

def machine : Q → Stmt4 Q
 | .prepare .done => .goto (fun _ => .seed)
 | .prepare q => Routine.relocate prepareRoles Q.prepare (ReverseContext.machine q)
 | .seed => .push .output (fun _ => .frameEnd) (.goto (fun _ => .uncons .tag0))
 | .uncons .empty => .goto (fun _ => .tagResult)
 | .uncons .nonempty => .goto (fun _ => .move .scan)
 | .uncons q => Routine.relocate readRoles Q.uncons (ContextUncons.machine q)
 | .move .done => .goto (fun _ => .shift (.prepare .formulaTag))
 | .move q => Routine.relocate readRoles Q.move (RosserDirect.machine q)
 | .shift .done => .goto (fun _ => .untag0)
 | .shift q => Routine.relocate id Q.shift (ShiftTraversal.machine q)
 | .untag0 => .pop .output (fun _ x => x)
   (.branch (fun x => x == some .bit1) (.goto (fun _ => .untag1)) (.goto (fun _ => .reject)))
 | .untag1 => .pop .output (fun _ x => x)
   (.branch (fun x => x == some .tokenEnd) (.load (fun _ => none) (.goto (fun _ => .uncons .tag0))) (.goto (fun _ => .reject)))
 | .tagResult => .push .output (fun _ => .tokenEnd)
   (.push .output (fun _ => .bit1) (.push .output (fun _ => .bit0)
    (.load (fun _ => none) (.goto (fun _ => .done)))))
 | .done | .reject => .halt

theorem agree_prepare (q : ReverseContext.Q) (h : ReverseContext.machine q ≠ .halt) :
 machine (.prepare q) = Routine.relocate prepareRoles Q.prepare (ReverseContext.machine q) := by
 cases q <;> simp_all [machine,ReverseContext.machine]
theorem agree_uncons (q : ContextUncons.Control) (h : ContextUncons.machine q ≠ .halt) :
 machine (.uncons q) = Routine.relocate readRoles Q.uncons (ContextUncons.machine q) := by
 cases q <;> simp_all [machine,ContextUncons.machine]
theorem agree_move (q : Label) (h : RosserDirect.machine q ≠ .halt) :
 machine (.move q) = Routine.relocate readRoles Q.move (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]
theorem agree_shift (q : ShiftTraversal.Q) (h : ShiftTraversal.machine q ≠ .halt) :
 machine (.shift q) = Routine.relocate id Q.shift (ShiftTraversal.machine q) := by
 cases q <;> simp_all [machine,ShiftTraversal.machine]

theorem untag (f : ZFR.Formula) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches machine (cfg4 .untag0 v p a [] (TypedContext.value (.formula f) ++ c))
  (cfg4 (.uncons .tag0) none p a [] (Membership.formulaPayload f ++ .frameEnd :: c)) := by
 have h0 : TM2.Reaches machine
   (cfg4 .untag0 v p a [] (.bit1 :: .tokenEnd :: (Membership.formulaPayload f ++ .frameEnd :: c)))
   (cfg4 .untag1 (some .bit1) p a [] (.tokenEnd :: (Membership.formulaPayload f ++ .frameEnd :: c))) := by
   apply Relation.ReflTransGen.single
   simp [machine,cfg4,TM2.step,TM2.stepAux,store4,Function.update]
   funext k; cases k <;> rfl
 have h1 : TM2.Reaches machine
   (cfg4 .untag1 (some .bit1) p a [] (.tokenEnd :: (Membership.formulaPayload f ++ .frameEnd :: c)))
   (cfg4 (.uncons .tag0) none p a [] (Membership.formulaPayload f ++ .frameEnd :: c)) := by
   apply Relation.ReflTransGen.single
   simp [machine,cfg4,TM2.step,TM2.stepAux,store4,Function.update]
   funext k; cases k <;> rfl
 simpa [TM2.Reaches,TypedContext.value,valueSymbols,valueTokens,Membership.formulaPayload,payloadBits,List.flatMap_cons,tokenBits,Nat.one_bits,bitSymbol,List.append_assoc] using h0.trans h1

theorem process (Γ : ZFR.Context) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches machine
  (cfg4 (.uncons .tag0) v (TypedContext.value (.context Γ) ++ p) a [] c)
  (cfg4 .tagResult (some .frameEnd) p a [] (Membership.contextFrames (Γ.map ZFR.shift).reverse ++ c)) := by
 induction Γ generalizing v c with
 | nil =>
   have h0 := Routine.lift_embedded_run readRoles read_injective Q.uncons
     ContextUncons.machine machine agree_uncons (fun _ => c)
     (ContextUncons.uncons_empty v p a) (by simp [config])
   simp only [embed_read] at h0
   have h1 : TM2.Reaches machine (cfg4 (.uncons .empty) (some .frameEnd) p a [] c)
     (cfg4 .tagResult (some .frameEnd) p a [] c) := Relation.ReflTransGen.single rfl
   exact h0.trans h1
 | cons f Γ ih =>
   have h0 := Routine.lift_embedded_run readRoles read_injective Q.uncons
     ContextUncons.machine machine agree_uncons (fun _ => c)
     (ContextUncons.uncons_nonempty f Γ v p a) (by simp [config])
   simp only [embed_read] at h0
   have h1 : TM2.Reaches machine
     (cfg4 (.uncons .nonempty) none (TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ p) a [] c)
     (cfg4 (.move .scan) none (TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ p) a [] c) := Relation.ReflTransGen.single rfl
   have hm : TM2.Reaches RosserDirect.machine
     (config Label.scan none (TypedContext.value (.formula f) ++ (TypedContext.value (.context Γ) ++ p)) [] a)
     (config Label.done none (TypedContext.value (.context Γ) ++ p) [] (TypedContext.value (.formula f) ++ a)) := by
     simpa [cfg,config,TypedContext.value,valueSymbols,List.append_assoc] using
       RosserDirect.move_frame (payloadBits (valueTokens (.formula f))) (payloadBits_no_end _) none (TypedContext.value (.context Γ) ++ p) a
   have h2 := Routine.lift_embedded_run readRoles read_injective Q.move
     RosserDirect.machine machine agree_move (fun _ => c) hm (by simp [config])
   simp only [embed_read] at h2
   have h3 : TM2.Reaches machine
     (cfg4 (.move .done) none (TypedContext.value (.context Γ) ++ p) (TypedContext.value (.formula f) ++ a) [] c)
     (cfg4 (.shift (.prepare .formulaTag)) none (TypedContext.value (.context Γ) ++ p) (TypedContext.value (.formula f) ++ a) [] c) := Relation.ReflTransGen.single rfl
   have h4 := FourStack.relabel_run Q.shift ShiftTraversal.machine machine agree_shift
     _ _ _ _ _ _ _ _ _ _ _ _ (ShiftTraversal.shift_formula f none (TypedContext.value (.context Γ) ++ p) a c)
   have h5 : TM2.Reaches machine
     (cfg4 (.shift .done) none (TypedContext.value (.context Γ) ++ p) a [] (TypedContext.value (.formula (ZFR.shift f)) ++ c))
     (cfg4 .untag0 none (TypedContext.value (.context Γ) ++ p) a [] (TypedContext.value (.formula (ZFR.shift f)) ++ c)) := Relation.ReflTransGen.single rfl
   have h6 := untag (ZFR.shift f) none (TypedContext.value (.context Γ) ++ p) a c
   have h7 := ih none (Membership.formulaPayload (ZFR.shift f) ++ .frameEnd :: c)
   simp only [TM2.Reaches,List.append_assoc] at h0 h1 h2 h3 h4 h5 h6 h7
   have h := h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7))))))
   simpa [TM2.Reaches,Membership.contextFrames,Membership.frames,List.map_cons,List.reverse_cons,List.map_append,List.flatMap_append,List.append_assoc] using h

/-- Complete finite context shift, preserving context order and all stack tails. -/
theorem shift_context (Γ : ZFR.Context) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches machine
  (cfg4 (.prepare .tag0) v p (TypedContext.value (.context Γ) ++ a) [] c)
  (cfg4 .done none p a [] (TypedContext.value (.context (ZFR.shiftContext Γ)) ++ c)) := by
 have h0 := Routine.lift_embedded_run prepareRoles prepare_injective Q.prepare
   ReverseContext.machine machine agree_prepare (fun _ => c)
   (ReverseContext.reverse_context Γ v a p) (by simp [config])
 simp only [embed_prepare] at h0
 have h1 : TM2.Reaches machine
   (cfg4 (.prepare .done) none (TypedContext.value (.context Γ.reverse) ++ p) a [] c)
   (cfg4 .seed none (TypedContext.value (.context Γ.reverse) ++ p) a [] c) := Relation.ReflTransGen.single rfl
 have h2 : TM2.Reaches machine
   (cfg4 .seed none (TypedContext.value (.context Γ.reverse) ++ p) a [] c)
   (cfg4 (.uncons .tag0) none (TypedContext.value (.context Γ.reverse) ++ p) a [] (.frameEnd :: c)) := by
   apply Relation.ReflTransGen.single
   simp [machine,cfg4,TM2.step,TM2.stepAux,store4,Function.update]
   funext k; cases k <;> rfl
 have h3 := process Γ.reverse none p a (.frameEnd :: c)
 have h4 : TM2.Reaches machine
   (cfg4 .tagResult (some .frameEnd) p a [] (Membership.contextFrames (Γ.reverse.map ZFR.shift).reverse ++ .frameEnd :: c))
   (cfg4 .done none p a [] (tokenBits 2 ++ Membership.contextFrames (Γ.reverse.map ZFR.shift).reverse ++ .frameEnd :: c)) := by
   apply Relation.ReflTransGen.single
   simp [machine,cfg4,TM2.step,TM2.stepAux,store4,Function.update,tokenBits]
   funext k; cases k <;> rfl
 have h := h0.trans (h1.trans (h2.trans (h3.trans h4)))
 simpa [TM2.Reaches,TypedContext.value,FramedContext.encode,Membership.contextFrames,Membership.frames,ZFR.shiftContext,List.map_reverse,List.append_assoc] using h

end RosserDirect.ShiftContext
