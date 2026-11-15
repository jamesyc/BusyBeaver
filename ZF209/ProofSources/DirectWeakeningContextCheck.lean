module
public import DirectContextInclusion
public import DirectOperandSwap
@[expose] public section
namespace RosserDirect.WeakeningContextCheck
open Turing Segment
set_option backward.isDefEq.respectTransparency false
inductive Control where
 | copy (q : Grammar.CopyControl TypedBlock.Control)
 | dropFormula (q : Grammar.DropControl TypedBlock.Control)
 | swap (q : OperandSwap.Control)
 | move (q : Grammar.CopyControl TypedBlock.Control)
 | subset (q : ContextInclusion.Control)
 | dropContext (q : Grammar.DropControl TypedBlock.Control)
 | accept | reject
 deriving DecidableEq, Fintype, Inhabited

def machine : Control → Stmt Control
 | .copy .done => .goto (fun _ => .dropFormula (.scan (.run 0 .start)))
 | .copy q => Routine.relocate id Control.copy ((TypedBlock.machine) q)
 | .dropFormula .done => .goto (fun _ => .swap (.first (.scan (.run 0 .start))))
 | .dropFormula q => Routine.relocate SelectSecond.swap Control.dropFormula ((TypedBlock.dropMachine) q)
 | .swap .done => .goto (fun _ => .move (.scan (.run 1 .start)))
 | .swap q => Routine.relocate SelectSecond.swap Control.swap ((OperandSwap.machine) q)
 | .move .done => .goto (fun _ => .subset (.uncons .tag0))
 | .move q => Routine.relocate SelectSecond.swap Control.move ((TypedBlock.moveMachine) q)
 | .subset .accept => .goto (fun _ => .dropContext (.scan (.run 0 .start)))
 | .subset .reject => .goto (fun _ => .reject)
 | .subset q => Routine.relocate id Control.subset ((ContextInclusion.machine) q)
 | .dropContext .done => .load (fun _ => none) (.goto (fun _ => .accept))
 | .dropContext q => Routine.relocate id Control.dropContext ((TypedBlock.dropMachine) q)
 | .accept | .reject => .halt

theorem agree_copy (q : Grammar.CopyControl TypedBlock.Control) (h : (TypedBlock.machine) q ≠ .halt) :
 machine (.copy q) = Routine.relocate id Control.copy ((TypedBlock.machine) q) := by
 cases q <;> simp_all [machine,TypedBlock.machine,Grammar.copyMachine]

theorem embed_copy (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.copy (config q v a b c) (fun _ => []) = config (.copy q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_dropFormula (q : Grammar.DropControl TypedBlock.Control) (h : (TypedBlock.dropMachine) q ≠ .halt) :
 machine (.dropFormula q) = Routine.relocate SelectSecond.swap Control.dropFormula ((TypedBlock.dropMachine) q) := by
 cases q <;> simp_all [machine,TypedBlock.dropMachine,Grammar.dropMachine]

theorem embed_dropFormula (q : Grammar.DropControl TypedBlock.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed SelectSecond.swap Control.dropFormula (config q v a b c) (fun _ => []) = config (.dropFormula q) v c b a := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_swap (q : OperandSwap.Control) (h : (OperandSwap.machine) q ≠ .halt) :
 machine (.swap q) = Routine.relocate SelectSecond.swap Control.swap ((OperandSwap.machine) q) := by
 cases q <;> simp_all [machine,OperandSwap.machine]

theorem embed_swap (q : OperandSwap.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed SelectSecond.swap Control.swap (config q v a b c) (fun _ => []) = config (.swap q) v c b a := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_move (q : Grammar.CopyControl TypedBlock.Control) (h : (TypedBlock.moveMachine) q ≠ .halt) :
 machine (.move q) = Routine.relocate SelectSecond.swap Control.move ((TypedBlock.moveMachine) q) := by
 cases q <;> simp_all [machine,TypedBlock.moveMachine,GrammarMove.machine]

theorem embed_move (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed SelectSecond.swap Control.move (config q v a b c) (fun _ => []) = config (.move q) v c b a := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_subset (q : ContextInclusion.Control) (h : (ContextInclusion.machine) q ≠ .halt) :
 machine (.subset q) = Routine.relocate id Control.subset ((ContextInclusion.machine) q) := by
 cases q <;> simp_all [machine,ContextInclusion.machine]

theorem embed_subset (q : ContextInclusion.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.subset (config q v a b c) (fun _ => []) = config (.subset q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem agree_dropContext (q : Grammar.DropControl TypedBlock.Control) (h : (TypedBlock.dropMachine) q ≠ .halt) :
 machine (.dropContext q) = Routine.relocate id Control.dropContext ((TypedBlock.dropMachine) q) := by
 cases q <;> simp_all [machine,TypedBlock.dropMachine,Grammar.dropMachine]

theorem embed_dropContext (q : Grammar.DropControl TypedBlock.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Control.dropContext (config q v a b c) (fun _ => []) = config (.dropContext q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

abbrev args (Γ Δ : ZFR.Context) (a : ZFR.Formula) (src : List Symbol) :=
 TypedContext.value (.formula a) ++ TypedContext.value (.context Δ) ++ TypedContext.value (.context Γ) ++ src

theorem prepare (Γ Δ : ZFR.Context) (a : ZFR.Formula) (v : Option Symbol) (src : List Symbol) :
 TM2.Reaches machine
 (config (.copy (.scan (.run 2 .start))) v (args Γ Δ a src) [] [])
 (config (.subset (.uncons .tag0)) none (TypedContext.value (.context Γ) ++ TypedContext.value (.context Δ) ++ args Γ Δ a src) [] []) := by
 let vals := args Γ Δ a src
 have h0 := Routine.lift_embedded_run id Function.injective_id Control.copy TypedBlock.machine machine agree_copy (fun _ => [])
   (TypedBlock.copy_block 2 [.formula a,.context Δ,.context Γ] rfl v src []) (by simp [config])
 simp only [embed_copy] at h0
 have l0 : TM2.Reaches machine
   (config (.copy .done) none vals [] (TypedContext.stack [.formula a,.context Δ,.context Γ]))
   (config (.dropFormula (.scan (.run 0 .start))) none vals [] (TypedContext.stack [.formula a,.context Δ,.context Γ])) := Relation.ReflTransGen.single rfl
 obtain ⟨w,h⟩ := TypedBlock.drop_block 0 [.formula a] rfl none (TypedContext.stack [.context Δ,.context Γ]) [] vals
 have h1 := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective Control.dropFormula TypedBlock.dropMachine machine agree_dropFormula (fun _ => []) h (by simp [config])
 simp only [embed_dropFormula] at h1
 have l1 : TM2.Reaches machine
   (config (.dropFormula .done) w vals [] (TypedContext.stack [.context Δ,.context Γ]))
   (config (.swap (.first (.scan (.run 0 .start)))) w vals [] (TypedContext.stack [.context Δ,.context Γ])) := Relation.ReflTransGen.single rfl
 have h2 := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective Control.swap OperandSwap.machine machine agree_swap (fun _ => [])
   (OperandSwap.swap_fields (.context Γ) (.context Δ) w [] vals) (by simp [config])
 simp only [embed_swap] at h2
 have l2 : TM2.Reaches machine
   (config (.swap .done) none vals [] (TypedContext.stack [.context Γ,.context Δ]))
   (config (.move (.scan (.run 1 .start))) none vals [] (TypedContext.stack [.context Γ,.context Δ])) := Relation.ReflTransGen.single rfl
 have h3 := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective Control.move TypedBlock.moveMachine machine agree_move (fun _ => [])
   (TypedBlock.move_block 1 [.context Γ,.context Δ] rfl none [] vals) (by simp [config])
 simp only [embed_move] at h3
 have l3 : TM2.Reaches machine
   (config (.move .done) none (TypedContext.stack [.context Γ,.context Δ] ++ vals) [] [])
   (config (.subset (.uncons .tag0)) none (TypedContext.stack [.context Γ,.context Δ] ++ vals) [] []) := Relation.ReflTransGen.single rfl
 simp only [TM2.Reaches,vals,args,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] at h0 l0 h1 l1 h2 l2 h3 l3 ⊢
 exact h0.trans (l0.trans (h1.trans (l1.trans (h2.trans (l2.trans (h3.trans l3))))))

/-- Check context inclusion while preserving all original weakening operands. -/
theorem accepts (Γ Δ : ZFR.Context) (a : ZFR.Formula) (sub : ∀ f ∈ Γ, f ∈ Δ)
 (v : Option Symbol) (src : List Symbol) :
 TM2.Reaches machine
 (config (.copy (.scan (.run 2 .start))) v (args Γ Δ a src) [] [])
 (config .accept none (args Γ Δ a src) [] []) := by
 let vals := args Γ Δ a src
 have hp := prepare Γ Δ a v src
 have hs := Routine.lift_embedded_run id Function.injective_id Control.subset ContextInclusion.machine machine agree_subset (fun _ => [])
   (ContextInclusion.accepts_subset Γ Δ sub none vals) (by simp [config])
 simp only [embed_subset] at hs
 have hl : TM2.Reaches machine
   (config (.subset .accept) (some .frameEnd) (TypedContext.value (.context Δ) ++ vals) [] [])
   (config (.dropContext (.scan (.run 0 .start))) (some .frameEnd) (TypedContext.value (.context Δ) ++ vals) [] []) := Relation.ReflTransGen.single rfl
 obtain ⟨w,h⟩ := TypedBlock.drop_block 0 [.context Δ] rfl (some .frameEnd) vals [] []
 have hd := Routine.lift_embedded_run id Function.injective_id Control.dropContext TypedBlock.dropMachine machine agree_dropContext (fun _ => []) h (by simp [config])
 simp only [embed_dropContext] at hd
 have he : TM2.Reaches machine (config (.dropContext .done) w vals [] []) (config .accept none vals [] []) := Relation.ReflTransGen.single rfl
 simp only [TM2.Reaches,vals,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil] at hd
 exact hp.trans (hs.trans (hl.trans (hd.trans he)))

theorem rejects (Γ Δ : ZFR.Context) (a : ZFR.Formula) (nsub : ¬(∀ f ∈ Γ, f ∈ Δ))
 (v : Option Symbol) (src : List Symbol) :
 ∃ left right, TM2.Reaches machine
 (config (.copy (.scan (.run 2 .start))) v (args Γ Δ a src) [] [])
 (config .reject none left [] right) := by
 have hp := prepare Γ Δ a v src
 obtain ⟨left,right,h⟩ := ContextInclusion.rejects_nonsubset Γ Δ nsub none (args Γ Δ a src)
 have hs := Routine.lift_embedded_run id Function.injective_id Control.subset ContextInclusion.machine machine agree_subset (fun _ => []) h (by simp [config])
 simp only [embed_subset] at hs
 have he : TM2.Reaches machine (config (.subset .reject) none left [] right) (config .reject none left [] right) := Relation.ReflTransGen.single rfl
 exact ⟨left,right,hp.trans (hs.trans he)⟩

end RosserDirect.WeakeningContextCheck
