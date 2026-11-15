module
public import DirectRoutineRelabel
public import DirectSelectSecond
@[expose] public section
namespace RosserDirect.ContextUncons
open Turing Segment
set_option backward.isDefEq.respectTransparency false
inductive Control where
 | tag0 | tag1 | tag2 | entry | move (q : Label) | tag | restore (q : Label)
 | empty | nonempty | reject
 deriving DecidableEq, Fintype, Inhabited

def machine : Control → Stmt Control
 | .tag0 => TypedContext.expect .bit0 .tag1 .reject
 | .tag1 => TypedContext.expect .bit1 .tag2 .reject
 | .tag2 => TypedContext.expect .tokenEnd .entry .reject
 | .entry => .peek .input (fun _ x => x)
   (.branch (fun x => x == some .frameEnd)
     (.pop .input (fun _ x => x) (.goto (fun _ => .empty)))
     (.branch Option.isSome (.goto (fun _ => .move .scan)) (.goto (fun _ => .reject))))
 | .move .done => .goto (fun _ => .tag)
 | .move q => Routine.relocate id Control.move (RosserDirect.machine q)
 | .tag => .push .input (fun _ => .tokenEnd) (.push .input (fun _ => .bit1) (.push .input (fun _ => .bit0)
   (.push .output (fun _ => .tokenEnd) (.push .output (fun _ => .bit1) (.goto (fun _ => .restore .scan))))))
 | .restore .done => .goto (fun _ => .nonempty)
 | .restore q => Routine.relocate SelectSecond.swap Control.restore (RosserDirect.machine q)
 | .empty | .nonempty | .reject => .halt

theorem agree_move (q : Label) (h : RosserDirect.machine q ≠ .halt) :
 machine (.move q) = Routine.relocate id Control.move (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]
theorem agree_restore (q : Label) (h : RosserDirect.machine q ≠ .halt) :
 machine (.restore q) = Routine.relocate SelectSecond.swap Control.restore (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]

theorem embed_move (q : Label) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.move (RosserDirect.cfg q v a b c) (fun _ => []) = config (.move q) v a b c := by
 unfold Routine.embed RosserDirect.cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem embed_restore (q : Label) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed SelectSecond.swap Control.restore (RosserDirect.cfg q v a b c) (fun _ => []) = config (.restore q) v c b a := by
 unfold Routine.embed RosserDirect.cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem read_tag (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine (config .tag0 v (tokenBits 2 ++ src) [] dst)
 (config .entry (some .tokenEnd) src [] dst) := by
 have h0 := TypedContext.expect_step machine .tag0 .tag1 .reject .bit0 rfl v (.bit1 :: .tokenEnd :: src) [] dst
 have h1 := TypedContext.expect_step machine .tag1 .tag2 .reject .bit1 rfl (some .bit0) (.tokenEnd :: src) [] dst
 have h2 := TypedContext.expect_step machine .tag2 .entry .reject .tokenEnd rfl (some .bit1) src [] dst
 exact (TypedContext.reach_step h0).trans ((TypedContext.reach_step h1).trans (TypedContext.reach_step h2))

theorem entry_nonempty (x : Symbol) (hx : x ≠ .frameEnd) (v : Option Symbol) (src dst : List Symbol) :
 TM2.step machine (config .entry v (x :: src) [] dst) =
 some (config (.move .scan) (some x) (x :: src) [] dst) := by
 cases x <;> simp_all [machine,config,TM2.step,TM2.stepAux,storage]

theorem entry_empty (v : Option Symbol) (src dst : List Symbol) :
 TM2.step machine (config .entry v (.frameEnd :: src) [] dst) =
 some (config .empty (some .frameEnd) src [] dst) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage]
 funext k; cases k <;> rfl

theorem tag_step (f : ZFR.Formula) (Γ : ZFR.Context) (src dst : List Symbol) :
 TM2.step machine
 (config .tag none (FramedContext.encode Γ ++ src) [] (FramedRow.formulaFrame f ++ dst)) =
 some (config (.restore .scan) none (TypedContext.value (.context Γ) ++ src) [] (TypedContext.value (.formula f) ++ dst)) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage,TypedContext.value,valueSymbols,valueTokens,
   FramedRow.formulaFrame,Membership.formulaPayload,payloadBits,tokenBits,List.append_assoc]
 funext k; cases k <;> rfl

theorem uncons_nonempty (f : ZFR.Formula) (Γ : ZFR.Context) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine
 (config .tag0 v (TypedContext.value (.context (f :: Γ)) ++ src) [] dst)
 (config .nonempty none (TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ src) [] dst) := by
 obtain ⟨x,xs,hf⟩ := List.exists_cons_of_ne_nil (FramedContext.formula_nonempty f)
 have hx : x ≠ .frameEnd := payloadBits_no_end (ZFR.TokenVM.emitFormula f) x (by change x ∈ Membership.formulaPayload f; rw [hf]; simp)
 have ht := read_tag v (FramedContext.encode (f :: Γ) ++ src) dst
 have he := TypedContext.reach_step (entry_nonempty x hx (some .tokenEnd) (xs ++ .frameEnd :: (FramedContext.encode Γ ++ src)) dst)
 have hm := Routine.lift_embedded_run id Function.injective_id Control.move RosserDirect.machine machine agree_move (fun _ => [])
   (RosserDirect.move_frame (Membership.formulaPayload f) (payloadBits_no_end _) (some x) (FramedContext.encode Γ ++ src) dst) (by simp [RosserDirect.cfg])
 simp only [embed_move] at hm
 have hl : TM2.Reaches machine
   (config (.move .done) none (FramedContext.encode Γ ++ src) [] (FramedRow.formulaFrame f ++ dst))
   (config .tag none (FramedContext.encode Γ ++ src) [] (FramedRow.formulaFrame f ++ dst)) := Relation.ReflTransGen.single rfl
 have htag := TypedContext.reach_step (tag_step f Γ src dst)
 have hr := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective Control.restore RosserDirect.machine machine agree_restore (fun _ => [])
   (RosserDirect.move_frame (payloadBits (valueTokens (.formula f))) (payloadBits_no_end _) none dst (TypedContext.value (.context Γ) ++ src)) (by simp [RosserDirect.cfg])
 simp only [embed_restore] at hr
 have hrl : TM2.Reaches machine
   (config (.restore .done) none (TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ src) [] dst)
   (config .nonempty none (TypedContext.value (.formula f) ++ TypedContext.value (.context Γ) ++ src) [] dst) := Relation.ReflTransGen.single rfl
 simp only [TM2.Reaches,TypedContext.value,valueSymbols,FramedContext.encode,Membership.contextFrames,Membership.frames,List.map_cons,List.nil_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
   FramedRow.formulaFrame,hf,List.cons_append,List.append_assoc,List.singleton_append] at ht he hm hl htag hr hrl ⊢
 exact ht.trans (he.trans (hm.trans (hl.trans (htag.trans (hr.trans hrl)))))

theorem uncons_empty (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine
 (config .tag0 v (TypedContext.value (.context []) ++ src) [] dst)
 (config .empty (some .frameEnd) src [] dst) := by
 have h := (read_tag v (.frameEnd :: src) dst).trans (TypedContext.reach_step (entry_empty (some .tokenEnd) src dst))
 simpa [TM2.Reaches,TypedContext.value,FramedContext.encode,Membership.contextFrames,Membership.frames] using h

end RosserDirect.ContextUncons
