module
public import DirectContextUncons
public import DirectFramedMembership
public import DirectTypedBlockDrop
@[expose] public section
namespace RosserDirect.ContextInclusion
open Turing Segment
set_option backward.isDefEq.respectTransparency false
inductive Control where
 | uncons (q : ContextUncons.Control)
 | copy (q : Grammar.CopyControl TypedBlock.Control)
 | dropCopy (q : Grammar.DropControl TypedBlock.Control)
 | strip | member (q : Membership.Control) | clear | dropTarget | accept | reject
 deriving DecidableEq, Fintype, Inhabited

def expectOn (k : Stack) (x : Symbol) (next : Stmt Control) : Stmt Control :=
 .pop k (fun _ y => y) (.branch (fun y => y == some x) next (.goto (fun _ => .reject)))

def machine : Control → Stmt Control
 | .uncons .empty => .goto (fun _ => .accept)
 | .uncons .nonempty => .goto (fun _ => .copy (.scan (.run 2 .start)))
 | .uncons q => Routine.relocate id Control.uncons (ContextUncons.machine q)
 | .copy .done => .goto (fun _ => .dropCopy (.scan (.run 1 .start)))
 | .copy q => Routine.relocate id Control.copy (TypedBlock.machine q)
 | .dropCopy .done => .goto (fun _ => .strip)
 | .dropCopy q => Routine.relocate SelectSecond.swap Control.dropCopy (TypedBlock.dropMachine q)
 | .strip => expectOn .input .bit1 (expectOn .input .tokenEnd
     (expectOn .output .bit0 (expectOn .output .bit1 (expectOn .output .tokenEnd (.goto (fun _ => .member .next))))))
 | .member .found => .goto (fun _ => .clear)
 | .member .absent => .goto (fun _ => .reject)
 | .member q => Routine.relocate id Control.member (Membership.machine q)
 | .clear => .pop .output (fun _ x => x)
    (.branch Option.isNone (.goto (fun _ => .dropTarget)) (.goto (fun _ => .clear)))
 | .dropTarget => .pop .input (fun _ x => x)
    (.branch Option.isNone (.goto (fun _ => .reject))
     (.branch (fun x => x == some .frameEnd) (.goto (fun _ => .uncons .tag0)) (.goto (fun _ => .dropTarget))))
 | .accept | .reject => .halt

theorem agree_uncons (q : ContextUncons.Control) (h : (ContextUncons.machine) q ≠ .halt) :
 machine (.uncons q) = Routine.relocate id Control.uncons ((ContextUncons.machine) q) := by
 cases q <;> simp_all [machine,ContextUncons.machine]

theorem embed_uncons (q : ContextUncons.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.uncons (config q v a b c) (fun _ => []) = config (.uncons q) v a b c := by
 unfold Routine.embed config 
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_copy (q : Grammar.CopyControl TypedBlock.Control) (h : (TypedBlock.machine) q ≠ .halt) :
 machine (.copy q) = Routine.relocate id Control.copy ((TypedBlock.machine) q) := by
 cases q <;> simp_all [machine,TypedBlock.machine,Grammar.copyMachine]

theorem embed_copy (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.copy (config q v a b c) (fun _ => []) = config (.copy q) v a b c := by
 unfold Routine.embed config 
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_dropCopy (q : Grammar.DropControl TypedBlock.Control) (h : (TypedBlock.dropMachine) q ≠ .halt) :
 machine (.dropCopy q) = Routine.relocate SelectSecond.swap Control.dropCopy ((TypedBlock.dropMachine) q) := by
 cases q <;> simp_all [machine,TypedBlock.dropMachine,Grammar.dropMachine]

theorem embed_dropCopy (q : Grammar.DropControl TypedBlock.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed SelectSecond.swap Control.dropCopy (config q v a b c) (fun _ => []) = config (.dropCopy q) v c b a := by
 unfold Routine.embed config 
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_member (q : Membership.Control) (h : (Membership.machine) q ≠ .halt) :
 machine (.member q) = Routine.relocate id Control.member ((Membership.machine) q) := by
 cases q <;> simp_all [machine,Membership.machine]

theorem embed_member (q : Membership.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.member (Membership.cfg q v a b c) (fun _ => []) = config (.member q) v a b c := by
 unfold Routine.embed config Membership.cfg
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem strip_step (f : ZFR.Formula) (Δ : ZFR.Context) (v : Option Symbol) (src : List Symbol) :
 TM2.step machine (config .strip v (TypedContext.value (.formula f) ++ src) [] (TypedContext.value (.context Δ))) =
 some (config (.member .next) (some .tokenEnd) (Membership.formulaPayload f ++ .frameEnd :: src) [] (FramedContext.encode Δ)) := by
 have hb1 : tokenBits 1 = [.bit1,.tokenEnd] := by decide
 have hb2 : tokenBits 2 = [.bit0,.bit1,.tokenEnd] := by decide
 simp [machine,expectOn,config,TM2.step,TM2.stepAux,storage,TypedContext.value,valueSymbols,valueTokens,
   Membership.formulaPayload,payloadBits,hb1,hb2,List.append_assoc]
 funext k; cases k <;> rfl

theorem head_test (f : ZFR.Formula) (Γ Δ : ZFR.Context) (v : Option Symbol) (src : List Symbol) :
 ∃ out, TM2.Reaches machine
 (config (.uncons .tag0) v (TypedContext.value (.context (f :: Γ)) ++ TypedContext.value (.context Δ) ++ src) [] [])
 (config (.member (if f ∈ Δ then .found else .absent)) none
   (Membership.formulaPayload f ++ .frameEnd :: (TypedContext.value (.context Γ) ++ TypedContext.value (.context Δ) ++ src)) [] out) := by
 let tail := TypedContext.value (.context Γ) ++ TypedContext.value (.context Δ) ++ src
 let vals := TypedContext.value (.formula f) ++ tail
 have h0 := Routine.lift_embedded_run id Function.injective_id Control.uncons ContextUncons.machine machine agree_uncons (fun _ => [])
   (ContextUncons.uncons_nonempty f Γ v (TypedContext.value (.context Δ) ++ src) []) (by simp [config])
 simp only [embed_uncons] at h0
 have l0 : TM2.Reaches machine (config (.uncons .nonempty) none vals [] [])
   (config (.copy (.scan (.run 2 .start))) none vals [] []) := Relation.ReflTransGen.single rfl
 have h1 := Routine.lift_embedded_run id Function.injective_id Control.copy TypedBlock.machine machine agree_copy (fun _ => [])
   (TypedBlock.copy_block 2 [.formula f,.context Γ,.context Δ] rfl none src []) (by simp [config])
 simp only [embed_copy] at h1
 have l1 : TM2.Reaches machine
   (config (.copy .done) none vals [] (TypedContext.stack [.formula f,.context Γ,.context Δ]))
   (config (.dropCopy (.scan (.run 1 .start))) none vals [] (TypedContext.stack [.formula f,.context Γ,.context Δ])) := Relation.ReflTransGen.single rfl
 obtain ⟨w,h⟩ := TypedBlock.drop_block 1 [.formula f,.context Γ] rfl none (TypedContext.value (.context Δ)) [] vals
 have h2 := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective Control.dropCopy TypedBlock.dropMachine machine agree_dropCopy (fun _ => []) h (by simp [config])
 simp only [embed_dropCopy] at h2
 have l2 : TM2.Reaches machine (config (.dropCopy .done) w vals [] (TypedContext.value (.context Δ)))
   (config .strip w vals [] (TypedContext.value (.context Δ))) := Relation.ReflTransGen.single rfl
 have hs := TypedContext.reach_step (strip_step f Δ w tail)
 obtain ⟨out,h⟩ := Membership.lookup_framed_context f Δ (some .tokenEnd) tail
 have h3 := Routine.lift_embedded_run id Function.injective_id Control.member Membership.machine machine agree_member (fun _ => []) h (by simp [Membership.cfg])
 simp only [embed_member] at h3
 refine ⟨out,?_⟩
 simp only [TM2.Reaches,tail,vals,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] at h0 l0 h1 l1 h2 l2 hs h3 ⊢
 exact h0.trans (l0.trans (h1.trans (l1.trans (h2.trans (l2.trans (hs.trans h3))))))

theorem clear_step (x : Symbol) (v : Option Symbol) (src out : List Symbol) :
 TM2.step machine (config .clear v src [] (x :: out)) = some (config .clear (some x) src [] out) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage]
 funext k; cases k <;> rfl

theorem clear_empty (v : Option Symbol) (src : List Symbol) :
 TM2.step machine (config .clear v src [] []) = some (config .dropTarget none src [] []) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]

theorem clear_all (v : Option Symbol) (src out : List Symbol) :
 TM2.Reaches machine (config .clear v src [] out) (config .dropTarget none src [] []) := by
 induction out generalizing v with
 | nil => exact TypedContext.reach_step (clear_empty v src)
 | cons x xs ih => exact (TypedContext.reach_step (clear_step x v src xs)).trans (ih (some x))

theorem drop_step (x : Symbol) (hx : x ≠ .frameEnd) (v : Option Symbol) (src : List Symbol) :
 TM2.step machine (config .dropTarget v (x :: src) [] []) = some (config .dropTarget (some x) src [] []) := by
 cases x <;> simp_all [machine,config,TM2.step,TM2.stepAux,storage]
 all_goals funext k; cases k <;> rfl

theorem drop_end (v : Option Symbol) (src : List Symbol) :
 TM2.step machine (config .dropTarget v (.frameEnd :: src) [] []) = some (config (.uncons .tag0) (some .frameEnd) src [] []) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage]
 funext k; cases k <;> rfl

theorem drop_frame (payload : List Symbol) (valid : ∀ x ∈ payload, x ≠ .frameEnd)
 (v : Option Symbol) (src : List Symbol) :
 TM2.Reaches machine (config .dropTarget v (payload ++ .frameEnd :: src) [] [])
 (config (.uncons .tag0) (some .frameEnd) src [] []) := by
 induction payload generalizing v with
 | nil => exact TypedContext.reach_step (drop_end v src)
 | cons x xs ih => exact (TypedContext.reach_step (drop_step x (valid x (by simp)) v (xs ++ .frameEnd :: src))).trans (ih (by intro y hy; exact valid y (by simp [hy])) (some x))

theorem head_success (f : ZFR.Formula) (Γ Δ : ZFR.Context) (hf : f ∈ Δ) (v : Option Symbol) (src : List Symbol) :
 TM2.Reaches machine
 (config (.uncons .tag0) v (TypedContext.value (.context (f :: Γ)) ++ TypedContext.value (.context Δ) ++ src) [] [])
 (config (.uncons .tag0) (some .frameEnd) (TypedContext.value (.context Γ) ++ TypedContext.value (.context Δ) ++ src) [] []) := by
 let tail := TypedContext.value (.context Γ) ++ TypedContext.value (.context Δ) ++ src
 obtain ⟨out,ht⟩ := head_test f Γ Δ v src
 simp only [hf,↓reduceIte] at ht
 have hl : TM2.Reaches machine (config (.member .found) none (Membership.formulaPayload f ++ .frameEnd :: tail) [] out)
   (config .clear none (Membership.formulaPayload f ++ .frameEnd :: tail) [] out) := Relation.ReflTransGen.single rfl
 exact ht.trans (hl.trans ((clear_all none _ out).trans (drop_frame (Membership.formulaPayload f) (payloadBits_no_end _) none tail)))

theorem empty_success (Δ : ZFR.Context) (v : Option Symbol) (src : List Symbol) :
 TM2.Reaches machine
 (config (.uncons .tag0) v (TypedContext.value (.context []) ++ TypedContext.value (.context Δ) ++ src) [] [])
 (config .accept (some .frameEnd) (TypedContext.value (.context Δ) ++ src) [] []) := by
 have h := Routine.lift_embedded_run id Function.injective_id Control.uncons ContextUncons.machine machine agree_uncons (fun _ => [])
   (ContextUncons.uncons_empty v (TypedContext.value (.context Δ) ++ src) []) (by simp [config])
 simp only [embed_uncons] at h
 have hl : TM2.Reaches machine (config (.uncons .empty) (some .frameEnd) (TypedContext.value (.context Δ) ++ src) [] [])
   (config .accept (some .frameEnd) (TypedContext.value (.context Δ) ++ src) [] []) := Relation.ReflTransGen.single rfl
 simpa [TM2.Reaches,List.append_assoc] using h.trans hl

/-- Genuine finite inclusion test for arbitrary contexts. The destination context
and trailing input are preserved; no membership predicate executes at runtime. -/
theorem accepts_subset (Γ Δ : ZFR.Context) (sub : ∀ f ∈ Γ, f ∈ Δ) (v : Option Symbol) (src : List Symbol) :
 TM2.Reaches machine
 (config (.uncons .tag0) v (TypedContext.value (.context Γ) ++ TypedContext.value (.context Δ) ++ src) [] [])
 (config .accept (some .frameEnd) (TypedContext.value (.context Δ) ++ src) [] []) := by
 induction Γ generalizing v with
 | nil => exact empty_success Δ v src
 | cons f Γ ih =>
   exact (head_success f Γ Δ (sub f (by simp)) v src).trans
     (ih (by intro g hg; exact sub g (by simp [hg])) (some .frameEnd))

theorem rejects_nonsubset (Γ Δ : ZFR.Context) (nsub : ¬(∀ f ∈ Γ, f ∈ Δ)) (v : Option Symbol) (src : List Symbol) :
 ∃ left right, TM2.Reaches machine
 (config (.uncons .tag0) v (TypedContext.value (.context Γ) ++ TypedContext.value (.context Δ) ++ src) [] [])
 (config .reject none left [] right) := by
 induction Γ generalizing v with
 | nil => simp at nsub
 | cons f Γ ih =>
   by_cases hf : f ∈ Δ
   · have hn : ¬(∀ g ∈ Γ, g ∈ Δ) := by
       intro h; apply nsub; intro g hg; rcases List.mem_cons.mp hg with rfl | hg; exact hf; exact h g hg
     obtain ⟨left,right,ht⟩ := ih hn (some .frameEnd)
     exact ⟨left,right,(head_success f Γ Δ hf v src).trans ht⟩
   · obtain ⟨out,ht⟩ := head_test f Γ Δ v src
     simp only [hf,↓reduceIte] at ht
     have hl : TM2.Reaches machine
       (config (.member .absent) none (Membership.formulaPayload f ++ .frameEnd :: (TypedContext.value (.context Γ) ++ TypedContext.value (.context Δ) ++ src)) [] out)
       (config .reject none (Membership.formulaPayload f ++ .frameEnd :: (TypedContext.value (.context Γ) ++ TypedContext.value (.context Δ) ++ src)) [] out) := Relation.ReflTransGen.single rfl
     exact ⟨_,out,ht.trans hl⟩

end RosserDirect.ContextInclusion
