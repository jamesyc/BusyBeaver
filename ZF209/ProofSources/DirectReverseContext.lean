module
public import DirectFourStack
public import DirectContextUncons
@[expose] public section
namespace RosserDirect.ReverseContext
open Turing Segment
set_option backward.isDefEq.respectTransparency false

inductive Q where
 | tag0 | tag1 | tag2 | start | entry | move (q : Label) | tagResult | done | reject
 deriving DecidableEq, Fintype, Inhabited

def machine : Q → Stmt Q
 | .tag0 => TypedContext.expect .bit0 .tag1 .reject
 | .tag1 => TypedContext.expect .bit1 .tag2 .reject
 | .tag2 => TypedContext.expect .tokenEnd .start .reject
 | .start => .push .output (fun _ => .frameEnd) (.goto (fun _ => .entry))
 | .entry => .peek .input (fun _ x => x)
   (.branch (fun x => x == some .frameEnd)
    (.pop .input (fun _ x => x) (.goto (fun _ => .tagResult)))
    (.branch Option.isSome (.goto (fun _ => .move .scan)) (.goto (fun _ => .reject))))
 | .move .done => .goto (fun _ => .entry)
 | .move q => Routine.relocate id Q.move (RosserDirect.machine q)
 | .tagResult => .push .output (fun _ => .tokenEnd)
   (.push .output (fun _ => .bit1) (.push .output (fun _ => .bit0)
    (.load (fun _ => none) (.goto (fun _ => .done)))))
 | .done | .reject => .halt

theorem agree_move (q : Label) (h : RosserDirect.machine q ≠ .halt) :
 machine (.move q) = Routine.relocate id Q.move (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]

theorem embed (q : Label) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Q.move (config q v a b c) (fun _ => []) = config (.move q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem read_tag (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine (config .tag0 v (tokenBits 2 ++ src) [] dst)
 (config .start (some .tokenEnd) src [] dst) := by
 have h0 := TypedContext.expect_step machine .tag0 .tag1 .reject .bit0 rfl v (.bit1 :: .tokenEnd :: src) [] dst
 have h1 := TypedContext.expect_step machine .tag1 .tag2 .reject .bit1 rfl (some .bit0) (.tokenEnd :: src) [] dst
 have h2 := TypedContext.expect_step machine .tag2 .start .reject .tokenEnd rfl (some .bit1) src [] dst
 exact (TypedContext.reach_step h0).trans ((TypedContext.reach_step h1).trans (TypedContext.reach_step h2))

theorem entry_nonempty (x : Symbol) (hx : x ≠ .frameEnd) (v : Option Symbol) (src dst : List Symbol) :
 TM2.step machine (config .entry v (x :: src) [] dst) =
 some (config (.move .scan) (some x) (x :: src) [] dst) := by
 cases x <;> simp_all [machine,config,TM2.step,TM2.stepAux,storage]

theorem entry_empty (v : Option Symbol) (src dst : List Symbol) :
 TM2.step machine (config .entry v (.frameEnd :: src) [] dst) =
 some (config .tagResult (some .frameEnd) src [] dst) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]
 funext k; cases k <;> rfl

theorem reverse_frames (Γ : ZFR.Context) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine (config .entry v (FramedContext.encode Γ ++ src) [] dst)
  (config .tagResult (some .frameEnd) src [] (Membership.contextFrames Γ.reverse ++ dst)) := by
 induction Γ generalizing v dst with
 | nil => exact Relation.ReflTransGen.single (entry_empty v src dst)
 | cons f Γ ih =>
   obtain ⟨x,xs,hx⟩ := List.exists_cons_of_ne_nil (FramedContext.formula_nonempty f)
   have hne : x ≠ .frameEnd := payloadBits_no_end (ZFR.TokenVM.emitFormula f) x (by change x ∈ Membership.formulaPayload f; rw [hx]; simp)
   have h0 : TM2.Reaches machine
     (config .entry v (Membership.formulaPayload f ++ .frameEnd :: (FramedContext.encode Γ ++ src)) [] dst)
     (config (.move .scan) (some x) (Membership.formulaPayload f ++ .frameEnd :: (FramedContext.encode Γ ++ src)) [] dst) := by
     rw [hx]
     exact Relation.ReflTransGen.single (entry_nonempty x hne v (xs ++ .frameEnd :: (FramedContext.encode Γ ++ src)) dst)
   have hm : TM2.Reaches RosserDirect.machine
     (config Label.scan (some x) (Membership.formulaPayload f ++ .frameEnd :: (FramedContext.encode Γ ++ src)) [] dst)
     (config Label.done none (FramedContext.encode Γ ++ src) [] (Membership.formulaPayload f ++ .frameEnd :: dst)) :=
     RosserDirect.move_frame (Membership.formulaPayload f) (payloadBits_no_end _) (some x) (FramedContext.encode Γ ++ src) dst
   have h1 := Routine.lift_embedded_run id Function.injective_id Q.move
     RosserDirect.machine machine agree_move (fun _ => []) hm (by simp [config])
   simp only [embed] at h1
   have h2 : TM2.Reaches machine
     (config (.move .done) none (FramedContext.encode Γ ++ src) [] (Membership.formulaPayload f ++ .frameEnd :: dst))
     (config .entry none (FramedContext.encode Γ ++ src) [] (Membership.formulaPayload f ++ .frameEnd :: dst)) := Relation.ReflTransGen.single rfl
   have h3 := ih none (Membership.formulaPayload f ++ .frameEnd :: dst)
   have h := h0.trans (h1.trans (h2.trans h3))
   simpa [TM2.Reaches,FramedContext.encode,Membership.contextFrames,Membership.frames,List.map_cons,List.flatMap_cons,List.reverse_cons,List.map_append,List.flatMap_append,List.append_assoc] using h

theorem reverse_context (Γ : ZFR.Context) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine (config .tag0 v (TypedContext.value (.context Γ) ++ src) [] dst)
  (config .done none src [] (TypedContext.value (.context Γ.reverse) ++ dst)) := by
 have h0 := read_tag v (FramedContext.encode Γ ++ src) dst
 have h1 : TM2.Reaches machine
   (config .start (some .tokenEnd) (FramedContext.encode Γ ++ src) [] dst)
   (config .entry (some .tokenEnd) (FramedContext.encode Γ ++ src) [] (.frameEnd :: dst)) := by
   apply Relation.ReflTransGen.single
   simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]
   funext k; cases k <;> rfl
 have h2 := reverse_frames Γ (some .tokenEnd) src (.frameEnd :: dst)
 have h3 : TM2.Reaches machine
   (config .tagResult (some .frameEnd) src [] (Membership.contextFrames Γ.reverse ++ .frameEnd :: dst))
   (config .done none src [] (tokenBits 2 ++ Membership.contextFrames Γ.reverse ++ .frameEnd :: dst)) := by
   apply Relation.ReflTransGen.single
   simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update,tokenBits]
   funext k; cases k <;> rfl
 have h := h0.trans (h1.trans (h2.trans h3))
 simpa [TM2.Reaches,TypedContext.value,FramedContext.encode,Membership.contextFrames,Membership.frames,List.append_assoc] using h

end RosserDirect.ReverseContext
