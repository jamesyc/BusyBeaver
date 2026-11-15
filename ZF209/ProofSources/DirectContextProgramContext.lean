module
public import DirectContextProgramMachine
@[expose] public section
namespace RosserDirect.ContextProgram
open Turing Segment
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option synthInstance.maxSize 512

theorem agree_dispatch (q : OpcodeDispatch.Control) (h : OpcodeDispatch.machine q ≠ .halt) :
 machine (.dispatch q) = Routine.relocate dispatchRoles Control.dispatch (OpcodeDispatch.machine q) := by
 cases q <;> simp_all [machine,OpcodeDispatch.machine,OpcodeDispatch.active]

theorem agree_construct (q : TypedContext.Control) (h : TypedContext.machine q ≠ .halt) :
 machine (.construct q) = Routine.relocate constructRoles Control.construct (TypedContext.machine q) := by
 cases q <;> simp_all [machine,TypedContext.machine]

theorem agree_move (q : TypedContext.Control) (h : moveMachine q ≠ .halt) :
 machine (.move q) = Routine.relocate moveRoles Control.move (moveMachine q) := by
 cases q <;> simp_all [machine,moveMachine]

/-- Exact reusable config identities make stack isolation explicit. -/
theorem embed_dispatch (q : OpcodeDispatch.Control) (v : Option Symbol)
    (p vals scr tmp rows : List Symbol) :
 Routine.embed dispatchRoles Control.dispatch (config q v p scr vals) (storage [] [] [] tmp rows) =
 cfg (.dispatch q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem embed_construct (q : TypedContext.Control) (v : Option Symbol)
    (p vals scr tmp rows : List Symbol) :
 Routine.embed constructRoles Control.construct (config q v vals scr tmp) (storage p [] [] [] rows) =
 cfg (.construct q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem embed_move (q : TypedContext.Control) (v : Option Symbol)
    (p vals scr tmp rows : List Symbol) :
 Routine.embed moveRoles Control.move (config q v tmp scr vals) (storage p [] [] [] rows) =
 cfg (.move q) v p vals scr tmp rows := by
 unfold Routine.embed cfg config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl



theorem dispatch_run (op : Fin 42) (v : Option Symbol)
    (rest vals scr tmp rows : List Symbol) :
 ∃ w, TM2.Reaches machine
   (cfg (.dispatch .start) v (tokenBits (2*op.val+1) ++ rest) vals scr tmp rows)
   (cfg (.dispatch (.opcode op)) w rest vals scr tmp rows) := by
 obtain ⟨w,hw⟩ := OpcodeDispatch.dispatch_opcode op v rest scr vals
 have h := Routine.lift_embedded_run dispatchRoles dispatch_injective Control.dispatch
   OpcodeDispatch.machine machine agree_dispatch (storage [] [] [] tmp rows) hw (by simp [config])
 exact ⟨w, by simpa only [embed_dispatch] using h⟩

theorem construct_run (p : List Symbol) (Γ : ZFR.Context) (f : ZFR.Formula)
    (v : Option Symbol) (src dst : List ZFR.TokenVM.Value) (rows : List Symbol) :
 TM2.Reaches machine
   (cfg (.construct .context0) v p (TypedContext.stack (.context Γ :: .formula f :: src)) [] (TypedContext.stack dst) rows)
   (cfg (.construct .done) none p (TypedContext.stack src) [] (TypedContext.stack (.context (f :: Γ) :: dst)) rows) := by
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.construct
   TypedContext.machine machine agree_construct (storage p [] [] [] rows)
   (TypedContext.cons_typed f Γ v src dst) (by simp [config])
 simpa only [embed_construct] using h

theorem empty_run (p : List Symbol) (v : Option Symbol)
    (src dst : List ZFR.TokenVM.Value) (rows : List Symbol) :
 TM2.Reaches machine
   (cfg (.construct .empty) v p (TypedContext.stack src) [] (TypedContext.stack dst) rows)
   (cfg (.construct .done) v p (TypedContext.stack src) [] (TypedContext.stack (.context [] :: dst)) rows) := by
 have h := Routine.lift_embedded_run constructRoles construct_injective Control.construct
   TypedContext.machine machine agree_construct (storage p [] [] [] rows)
   (TypedContext.reach_step (TypedContext.empty_typed v src dst)) (by simp [config])
 simpa only [embed_construct] using h

theorem move_run (p : List Symbol) (Γ : ZFR.Context) (v : Option Symbol)
    (src dst rows : List Symbol) :
 TM2.Reaches machine
   (cfg (.move .context0) v p dst [] (TypedContext.value (.context Γ) ++ src) rows)
   (cfg (.move .done) none p (TypedContext.value (.context Γ) ++ dst) [] src rows) := by
 have h := Routine.lift_embedded_run moveRoles move_injective Control.move
   moveMachine machine agree_move (storage p [] [] [] rows)
   (move_context Γ v src dst) (by simp [config])
 simpa only [embed_move] using h

theorem enter_empty (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 TM2.step machine (cfg (.dispatch (.opcode 8)) v p vals scr tmp rows) =
 some (cfg (.construct .empty) v p vals scr tmp rows) := rfl

theorem enter_cons (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 TM2.step machine (cfg (.dispatch (.opcode 9)) v p vals scr tmp rows) =
 some (cfg (.construct .context0) v p vals scr tmp rows) := rfl

theorem leave_construct (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 TM2.step machine (cfg (.construct .done) v p vals scr tmp rows) =
 some (cfg (.move .context0) v p vals scr tmp rows) := rfl

theorem leave_move (v : Option Symbol) (p vals scr tmp rows : List Symbol) :
 TM2.step machine (cfg (.move .done) v p vals scr tmp rows) =
 some (cfg (.dispatch .start) v p vals scr tmp rows) := rfl

theorem global_step {c d : TM2.Cfg (fun _ : GlobalStack => Symbol) Control (Option Symbol)}
    (h : TM2.step machine c = some d) : TM2.Reaches machine c d :=
 Relation.ReflTransGen.single h

/-- One complete existing VM instruction, from raw token bytes back to the
next token-dispatch entry. Both scratch and temporary stacks are restored. -/
theorem execute_empty (v : Option Symbol) (rest rows : List Symbol) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
   (cfg (.dispatch .start) v (tokenBits 17 ++ rest) (TypedContext.stack s) [] [] rows)
   (cfg (.dispatch .start) none rest (TypedContext.stack (.context [] :: s)) [] [] rows) := by
 obtain ⟨w,hd⟩ := dispatch_run 8 v rest (TypedContext.stack s) [] [] rows
 have he := global_step (enter_empty w rest (TypedContext.stack s) [] [] rows)
 have hc := empty_run rest w s [] rows
 have hl := global_step (leave_construct w rest (TypedContext.stack s) [] (TypedContext.value (.context [])) rows)
 have hm := move_run rest [] w [] (TypedContext.stack s) rows
 have hr := global_step (leave_move none rest (TypedContext.stack (.context [] :: s)) [] [] rows)
 simp only [TM2.Reaches,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil] at hd he hc hl hm hr ⊢
 exact hd.trans (he.trans (hc.trans (hl.trans (hm.trans hr))))

theorem execute_cons (v : Option Symbol) (rest rows : List Symbol)
    (Γ : ZFR.Context) (f : ZFR.Formula) (s : List ZFR.TokenVM.Value) :
 TM2.Reaches machine
   (cfg (.dispatch .start) v (tokenBits 19 ++ rest)
     (TypedContext.stack (.context Γ :: .formula f :: s)) [] [] rows)
   (cfg (.dispatch .start) none rest (TypedContext.stack (.context (f :: Γ) :: s)) [] [] rows) := by
 obtain ⟨w,hd⟩ := dispatch_run 9 v rest (TypedContext.stack (.context Γ :: .formula f :: s)) [] [] rows
 have he := global_step (enter_cons w rest (TypedContext.stack (.context Γ :: .formula f :: s)) [] [] rows)
 have hc := construct_run rest Γ f w s [] rows
 have hl := global_step (leave_construct none rest (TypedContext.stack s) [] (TypedContext.value (.context (f :: Γ))) rows)
 have hm := move_run rest (f :: Γ) none [] (TypedContext.stack s) rows
 have hr := global_step (leave_move none rest (TypedContext.stack (.context (f :: Γ) :: s)) [] [] rows)
 simp only [TM2.Reaches,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil] at hd he hc hl hm hr ⊢
 exact hd.trans (he.trans (hc.trans (hl.trans (hm.trans hr))))

end RosserDirect.ContextProgram
