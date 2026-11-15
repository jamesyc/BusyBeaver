module
public import DirectDisjunctionRule
@[expose] public section
namespace RosserDirect.ContextProgram
open Turing Segment
set_option backward.isDefEq.respectTransparency false

theorem agree_pc (q : Peirce.Control) (h : Peirce.machine q ≠ .halt) :
 machine (.pc q) = Routine.relocate constructRoles Control.pc (Peirce.machine q) := by
 cases q <;> simp_all [machine,Peirce.machine]

theorem embed_pc (q : Peirce.Control) (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.pc (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.pc q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem pc_constructor_run (a b : ZFR.Formula) (v : Option Symbol) (p vals rows : List Symbol) :
 TM2.Reaches machine
 (cfg (.pc (.copy0 (.scan (.run 1 .start)))) v p (Peirce.field b ++ Peirce.field a ++ vals) [] [] rows)
 (cfg (.pc .done) none p vals [] (Peirce.field (.imp (.imp (.imp a b) a) a)) rows) := by
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.pc
   Peirce.machine machine agree_pc (storage p [] [] [] rows)
   (Peirce.construct a b v vals []) (by simp [config])
 simpa [embed_pc] using h

/-- The actual finite interpreter constructs the classical Peirce axiom. No
premise row or external proof-checking callback is needed by this rule. -/
theorem execute_pc (Γ : ZFR.Context) (a b : ZFR.Formula) (v : Option Symbol)
 (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
 (cfg (.dispatch .start) v (tokenBits 23 ++ rest) (TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)) [] [] rows)
 (cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ (.imp (.imp (.imp a b) a) a)) ++ rows)) := by
 let vals := TypedContext.stack (.formula b :: .formula a :: .context Γ :: s)
 let tail := TypedContext.stack (.context Γ :: s)
 let f := ZFR.Formula.imp (.imp (.imp a b) a) a
 obtain ⟨w,hd⟩ := dispatch_run 11 v rest vals [] [] rows
 have he : TM2.Reaches machine (cfg (.dispatch (.opcode 11)) w rest vals [] [] rows)
   (cfg (.pc (.copy0 (.scan (.run 1 .start)))) w rest vals [] [] rows) := global_step rfl
 have hc := pc_constructor_run a b w rest tail rows
 have hl : TM2.Reaches machine (cfg (.pc .done) none rest tail [] (Peirce.field f) rows)
   (cfg (.diMove .scan) none rest tail [] (Peirce.field f) rows) := global_step rfl
 have hm := di_move_run f none rest tail rows
 have hml : TM2.Reaches machine
   (cfg (.diMove .done) none rest (Peirce.field f ++ tail) [] [] rows)
   (cfg (.diResult (.formula0 0)) none rest (Peirce.field f ++ tail) [] [] rows) := global_step rfl
 have hr := di_result_run Γ f none rest rows s
 have hrl : TM2.Reaches machine
   (cfg (.diResult .done) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ f) ++ rows))
   (cfg (.dispatch .start) none rest (TypedContext.stack s) [] [] (FramedRow.encode (.seq Γ f) ++ rows)) := global_step rfl
 simp only [TM2.Reaches,vals,tail,f,Peirce.field,TypedContext.stack,List.flatMap_cons,List.append_assoc] at hd he hc hl hm hml hr hrl ⊢
 exact hd.trans (he.trans (hc.trans (hl.trans (hm.trans (hml.trans (hr.trans hrl))))))
end RosserDirect.ContextProgram
