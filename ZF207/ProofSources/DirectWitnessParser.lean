module
public import DirectSchemaAxiomCheck
public import DirectFixedAxiomCheck
public import DirectSyntaxInterpreter
@[expose] public section
namespace RosserDirect.WitnessParser
open Turing
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 16384

inductive Q where
 | run (q : ContextProgram.Control) | fixed (q : FixedAxiomCheck.Q)
 | schema (q : SchemaAxiomCheck.Q) | accept | reject
 deriving DecidableEq, Fintype, Inhabited
abbrev C := TM2.Cfg (fun _ : ContextProgram.GlobalStack => Symbol) ContextProgram.Control (Option Symbol)
abbrev D := TM2.Cfg (fun _ : ContextProgram.GlobalStack => Symbol) Q (Option Symbol)
abbrev S := TM2.Stmt (fun _ : ContextProgram.GlobalStack => Symbol) Q (Option Symbol)
def cfg (q : Q) (v : Option Symbol) (p a s c rows : List Symbol) : D :=
 ⟨some q,v,ContextProgram.storage p a s c rows⟩
def embedded (c : C) : D := ⟨c.l.map Q.run,c.var,c.stk⟩

def roles : FourStack.K → ContextProgram.GlobalStack
 | .stream => .program | .data => .values | .scratch => .scratch | .output => .temporary

def pushProgram : List Symbol → S → S
 | [], k => k | x::xs,k => pushProgram xs (.push .program (fun _ => x) k)

def special : ContextProgram.Control → Prop
 | .dispatch (.opcode op) => 27 ≤ op.val ∧ op.val < 40
 | _ => False
instance (q : ContextProgram.Control) : Decidable (special q) := by
 cases q <;> (try cases ‹OpcodeDispatch.Control›) <;> unfold special <;> infer_instance

def intercept (op : Fin 42) : S :=
 pushProgram (tokenBits (2*op.val+1))
  (.goto (fun _ => if op.val < 38 then .fixed (.dispatch .start) else .schema (.dispatch .start)))

def machine : Q → S
 | .run q => match q with
   | .dispatch (.opcode op) => if 27 ≤ op.val ∧ op.val < 40 then intercept op else Routine.relocate id Q.run (ContextProgram.machine q)
   | _ => Routine.relocate id Q.run (ContextProgram.machine q)
 | .fixed (.accept _) => .goto (fun _ => .accept)
 | .fixed .reject => .goto (fun _ => .reject)
 | .fixed q => Routine.relocate roles Q.fixed (FixedAxiomCheck.machine q)
 | .schema (.accept _) => .goto (fun _ => .accept)
 | .schema .reject => .goto (fun _ => .reject)
 | .schema q => Routine.relocate roles Q.schema (SchemaAxiomCheck.machine q)
 | .accept | .reject => .halt

theorem ordinary (q : ContextProgram.Control) (h : ¬special q) :
 machine (.run q) = Routine.relocate id Q.run (ContextProgram.machine q) := by
 cases q <;> (try cases ‹OpcodeDispatch.Control›) <;> simp_all [machine,special]

theorem map_aux (s : ContextProgram.GlobalStmt) (v : Option Symbol) (T : ContextProgram.GlobalStack → List Symbol) :
 TM2.stepAux (Routine.relocate id Q.run s) v T = embedded (TM2.stepAux s v T) := by
 induction s generalizing v T with
 | push k f s ih => exact ih _ _
 | peek k f s ih => exact ih _ _
 | pop k f s ih => exact ih _ _
 | load f s ih => exact ih _ _
 | branch f s t ihs iht => cases h : f v <;> simp_all [Routine.relocate,TM2.stepAux]
 | goto f => rfl
 | halt => rfl

theorem ordinary_step {c d : C} (h : TM2.step ContextProgram.machine c = some d)
 (hn : ∀ q, c.l = some q → ¬special q) :
 TM2.step machine (embedded c) = some (embedded d) := by
 rcases c with ⟨l,v,T⟩
 cases l with
 | none => simp [TM2.step] at h
 | some q =>
  have hd : d = TM2.stepAux (ContextProgram.machine q) v T := by simpa [TM2.step] using h.symm
  subst d
  simp only [embedded,Option.map_some,TM2.step,ordinary q (hn q rfl),map_aux]

theorem unsupported_no_return {c d : C} (hc : c.l = some .unsupported)
 (hd : d.l = some (.dispatch .start)) : ¬TM2.Reaches ContextProgram.machine c d := by
 intro h
 rcases c with ⟨l,v,T⟩
 change l = some .unsupported at hc
 subst l
 rcases Relation.ReflTransGen.cases_head h with he | ⟨b,hb,hbd⟩
 · have he' := congrArg TM2.Cfg.l he
   simp [hd] at he'
 · have hs : TM2.step ContextProgram.machine ⟨some .unsupported,v,T⟩ = some ⟨none,v,T⟩ := rfl
   have he : b = ⟨none,v,T⟩ := Option.some.inj (hb.symm.trans hs)
   subst b
   have he' := congrArg TM2.Cfg.l (Routine.dead_reaches ContextProgram.machine rfl hbd)
   simp [hd] at he'

theorem special_successor {c d : C} (q : ContextProgram.Control) (hq : c.l = some q) (h : special q)
 (hs : TM2.step ContextProgram.machine c = some d) : d.l = some .unsupported := by
 cases q <;> simp only [special] at h
 all_goals try contradiction
 rename_i op
 cases op <;> simp only [special] at h
 all_goals try contradiction
 rename_i op
 rcases c with ⟨l,v,T⟩
 change l = some (.dispatch (.opcode op)) at hq
 subst l
 have hd : d = TM2.stepAux (ContextProgram.machine (.dispatch (.opcode op))) v T := by simpa [TM2.step] using hs.symm
 rw [hd]
 have ne (k : Nat) (hk : k < 27) : op.val ≠ k := by omega
 simp [ContextProgram.machine,TM2.stepAux,ne 0 (by decide), ne 1 (by decide), ne 2 (by decide), ne 3 (by decide), ne 4 (by decide), ne 5 (by decide), ne 6 (by decide), ne 7 (by decide), ne 8 (by decide), ne 9 (by decide), ne 10 (by decide), ne 11 (by decide), ne 12 (by decide), ne 13 (by decide), ne 14 (by decide), ne 15 (by decide), ne 16 (by decide), ne 17 (by decide), ne 18 (by decide), ne 19 (by decide), ne 20 (by decide), ne 21 (by decide), ne 22 (by decide), ne 23 (by decide), ne 24 (by decide), ne 25 (by decide), ne 26 (by decide)]

theorem live_run_to_return {c d : C} (h : TM2.Reaches ContextProgram.machine c d)
 (hd : d.l = some (.dispatch .start)) : TM2.Reaches machine (embedded c) (embedded d) := by
 induction h using Relation.ReflTransGen.head_induction_on with
 | refl => exact Relation.ReflTransGen.refl
 | @head a b hab hbd ih =>
  have hn : ∀ q, a.l = some q → ¬special q := by
   intro q hq hs
   exact unsupported_no_return (special_successor q hq hs hab) hd hbd
  have hh : TM2.Reaches machine (embedded a) (embedded b) := Relation.ReflTransGen.single (ordinary_step hab hn)
  exact hh.trans ih

theorem roles_injective : Function.Injective roles := by
 intro a b h; cases a <;> cases b <;> simp_all [roles]

theorem agree_fixed (q : FixedAxiomCheck.Q) (h : FixedAxiomCheck.machine q ≠ .halt) :
 machine (.fixed q) = Routine.relocate roles Q.fixed (FixedAxiomCheck.machine q) := by
 cases q <;> simp_all [machine,FixedAxiomCheck.machine]
theorem agree_schema (q : SchemaAxiomCheck.Q) (h : SchemaAxiomCheck.machine q ≠ .halt) :
 machine (.schema q) = Routine.relocate roles Q.schema (SchemaAxiomCheck.machine q) := by
 cases q <;> simp_all [machine,SchemaAxiomCheck.machine]

theorem embed_fixed (q : FixedAxiomCheck.Q) (v : Option Symbol) (p a s c rows : List Symbol) :
 FourStack.embed4 roles Q.fixed (FourStack.cfg4 q v p a s c) (ContextProgram.storage [] [] [] [] rows) =
 cfg (.fixed q) v p a s c rows := by
 unfold FourStack.embed4 FourStack.cfg4 cfg
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem embed_schema (q : SchemaAxiomCheck.Q) (v : Option Symbol) (p a s c rows : List Symbol) :
 FourStack.embed4 roles Q.schema (FourStack.cfg4 q v p a s c) (ContextProgram.storage [] [] [] [] rows) =
 cfg (.schema q) v p a s c rows := by
 unfold FourStack.embed4 FourStack.cfg4 cfg
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem pushProgram_correct (xs : List Symbol) (k : S) (v : Option Symbol) (p a s c rows : List Symbol) :
 TM2.stepAux (pushProgram xs k) v (ContextProgram.storage p a s c rows) =
 TM2.stepAux k v (ContextProgram.storage (xs++p) a s c rows) := by
 induction xs generalizing k p with
 | nil => rfl
 | cons x xs ih =>
  rw [pushProgram,ih]
  simp only [TM2.stepAux]
  have he : Function.update (ContextProgram.storage (xs++p) a s c rows) ContextProgram.GlobalStack.program (x::(xs++p)) =
   ContextProgram.storage ((x::xs)++p) a s c rows := by
   funext j; cases j <;> rfl
  exact congrArg (TM2.stepAux k v) he

theorem agree_dispatch (q : OpcodeDispatch.Control) (h : OpcodeDispatch.machine q ≠ .halt) :
 machine (.run (.dispatch q)) = Routine.relocate ContextProgram.dispatchRoles (fun q => Q.run (.dispatch q)) (OpcodeDispatch.machine q) := by
 cases q <;> simp_all [machine,ContextProgram.machine,Routine.relocate,OpcodeDispatch.machine,OpcodeDispatch.active]

theorem embed_dispatch (q : OpcodeDispatch.Control) (v : Option Symbol) (p a s c rows : List Symbol) :
 Routine.embed ContextProgram.dispatchRoles (fun q => Q.run (.dispatch q)) (Segment.config q v p s a)
  (ContextProgram.storage [] [] [] c rows) = cfg (.run (.dispatch q)) v p a s c rows := by
 unfold Routine.embed Segment.config cfg
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem dispatch (op : Fin 42) (v : Option Symbol) (p a c rows : List Symbol) :
 ∃ w, TM2.Reaches machine
  (cfg (.run (.dispatch .start)) v (tokenBits (2*op.val+1) ++ p) a [] c rows)
  (cfg (.run (.dispatch (.opcode op))) w p a [] c rows) := by
 obtain ⟨w,hw⟩ := OpcodeDispatch.dispatch_opcode op v p [] a
 have h := Routine.lift_embedded_run ContextProgram.dispatchRoles ContextProgram.dispatch_injective
  (fun q => Q.run (.dispatch q)) OpcodeDispatch.machine machine agree_dispatch
  (ContextProgram.storage [] [] [] c rows) hw (by simp [Segment.config])
 exact ⟨w,by simpa only [embed_dispatch] using h⟩

theorem fixed_entry (i : Fin 11) (v : Option Symbol) (p a c rows : List Symbol) :
 ∃ w, TM2.Reaches machine
  (cfg (.run (.dispatch .start)) v (tokenBits (2*(27+i.val)+1) ++ p) a [] c rows)
  (cfg (.fixed (.dispatch .start)) w (tokenBits (2*(27+i.val)+1) ++ p) a [] c rows) := by
 obtain ⟨w,h0⟩ := dispatch ⟨27+i.val,by omega⟩ v p a c rows
 have h1 : TM2.Reaches machine
  (cfg (.run (.dispatch (.opcode ⟨27+i.val,by omega⟩))) w p a [] c rows)
  (cfg (.fixed (.dispatch .start)) w (tokenBits (2*(27+i.val)+1) ++ p) a [] c rows) := by
  apply Relation.ReflTransGen.single
  simp [machine,intercept,cfg,TM2.step,pushProgram_correct,TM2.stepAux,
   show 27≤27+i.val by omega,show 27+i.val<40 by omega,show 27+i.val<38 by omega]
 exact ⟨w,h0.trans h1⟩

theorem schema_entry (r : Bool) (v : Option Symbol) (p a c rows : List Symbol) :
 ∃ w, TM2.Reaches machine
  (cfg (.run (.dispatch .start)) v (tokenBits (SchemaAxiomCheck.token r) ++ p) a [] c rows)
  (cfg (.schema (.dispatch .start)) w (tokenBits (SchemaAxiomCheck.token r) ++ p) a [] c rows) := by
 obtain ⟨w,h0⟩ := dispatch (SchemaAxiomCheck.opcode r) v p a c rows
 have h1 : TM2.Reaches machine
  (cfg (.run (.dispatch (.opcode (SchemaAxiomCheck.opcode r)))) w p a [] c rows)
  (cfg (.schema (.dispatch .start)) w (tokenBits (SchemaAxiomCheck.token r) ++ p) a [] c rows) := by
  apply Relation.ReflTransGen.single
  cases r <;> simp [machine,intercept,cfg,TM2.step,pushProgram_correct,TM2.stepAux,SchemaAxiomCheck.opcode,SchemaAxiomCheck.token]
 exact ⟨w,h0.trans h1⟩

theorem schema_prefix (r : Bool) (n : Nat) (body candidate : ZFR.Formula) (s : List ZFR.TokenVM.Value)
 (v : Option Symbol) (p rows : List Symbol) :
 ∃ w, TM2.Reaches machine
  (cfg (.run (.dispatch .start)) v (payloadBits (ZFR.TokenVM.emitWitness (SchemaAxiomCheck.witness r n body)) ++ p)
   (TypedContext.stack (.formula candidate :: s)) [] [] rows)
  (cfg (.schema (.dispatch .start)) w (tokenBits (SchemaAxiomCheck.token r) ++ p)
   (TypedContext.stack (.formula body :: .nat n :: .formula candidate :: s)) [] [] rows) := by
 have hn := SyntaxInterpreter.nat_runs n (.formula candidate :: s) v
  (payloadBits (ZFR.TokenVM.emitFormula body) ++ tokenBits (SchemaAxiomCheck.token r) ++ p) rows
 have hn' := live_run_to_return hn rfl
 have hf := SyntaxInterpreter.formula_runs body (.nat n :: .formula candidate :: s) none
  (tokenBits (SchemaAxiomCheck.token r) ++ p) rows
 have hf' := live_run_to_return hf rfl
 obtain ⟨w,he⟩ := schema_entry r none p (TypedContext.stack (.formula body :: .nat n :: .formula candidate :: s)) [] rows
 refine ⟨w,?_⟩
 simp only [List.append_assoc] at hn' hf'
 have h := hn'.trans (hf'.trans he)
 cases r <;> simpa [TM2.Reaches,SchemaAxiomCheck.witness,SchemaAxiomCheck.token,SchemaAxiomCheck.opcode,
  ZFR.TokenVM.emitWitness,payloadBits,List.flatMap_append,List.append_assoc,embedded,ContextProgram.cfg,cfg] using h

theorem fixed_codes (i : Fin 11) :
 payloadBits (ZFR.TokenVM.emitWitness (FixedAxiomCheck.witness i)) = tokenBits (2*(27+i.val)+1) := by
 have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 := by omega
 rcases hi with h | h | h | h | h | h | h | h | h | h | h <;> simp [FixedAxiomCheck.witness,h,ZFR.TokenVM.emitWitness,payloadBits]

theorem fixed_accept (i : Fin 11) (candidate : ZFR.Formula)
 (h : ZFR.ExecutableZF.axiomFormula (FixedAxiomCheck.witness i) = some candidate)
 (s : List ZFR.TokenVM.Value) (v : Option Symbol) (p rows : List Symbol) :
 TM2.Reaches machine
  (cfg (.run (.dispatch .start)) v (payloadBits (ZFR.TokenVM.emitWitness (FixedAxiomCheck.witness i)) ++ p)
   (TypedContext.stack (.formula candidate :: s)) [] [] rows)
  (cfg .accept (some .frameEnd) p (TypedContext.stack s) [] [] rows) := by
 have hc : candidate = FixedAxiomCheck.formula i := by rw [FixedAxiomCheck.formula_spec] at h; exact (Option.some.inj h).symm
 subst candidate
 obtain ⟨w,h0⟩ := fixed_entry i v p (TypedContext.stack (.formula (FixedAxiomCheck.formula i) :: s)) [] rows
 have h1 := FourStack.lift4_run roles roles_injective Q.fixed FixedAxiomCheck.machine machine agree_fixed
  (ContextProgram.storage [] [] [] [] rows)
  (FixedAxiomCheck.accept i w p (TypedContext.stack s) []) (by simp [FourStack.cfg4])
 simp only [embed_fixed] at h1
 have h2 : TM2.Reaches machine
  (cfg (.fixed (.accept i)) (some .frameEnd) p (TypedContext.stack s) [] [] rows)
  (cfg .accept (some .frameEnd) p (TypedContext.stack s) [] [] rows) := Relation.ReflTransGen.single rfl
 simp only [fixed_codes,TypedContext.stack,List.flatMap_cons] at h0 ⊢
 exact h0.trans (h1.trans h2)

theorem schema_accept (r : Bool) (n : Nat) (body candidate : ZFR.Formula)
 (h : ZFR.ExecutableZF.axiomFormula (SchemaAxiomCheck.witness r n body) = some candidate)
 (s : List ZFR.TokenVM.Value) (v : Option Symbol) (p rows : List Symbol) :
 TM2.Reaches machine
  (cfg (.run (.dispatch .start)) v (payloadBits (ZFR.TokenVM.emitWitness (SchemaAxiomCheck.witness r n body)) ++ p)
   (TypedContext.stack (.formula candidate :: s)) [] [] rows)
  (cfg .accept (some .frameEnd) p (TypedContext.stack s) [] [] rows) := by
 obtain ⟨w,h0⟩ := schema_prefix r n body candidate s v p rows
 have h1 := FourStack.lift4_run roles roles_injective Q.schema SchemaAxiomCheck.machine machine agree_schema
  (ContextProgram.storage [] [] [] [] rows)
  ((SchemaAxiomCheck.accepts_iff r n body candidate w p (TypedContext.stack s) []).mpr h) (by simp [FourStack.cfg4])
 simp only [embed_schema] at h1
 have h2 : TM2.Reaches machine
  (cfg (.schema (.accept r)) (some .frameEnd) p (TypedContext.stack s) [] [] rows)
  (cfg .accept (some .frameEnd) p (TypedContext.stack s) [] [] rows) := Relation.ReflTransGen.single rfl
 simp only [TM2.Reaches,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] at h0 h1 h2 ⊢
 exact h0.trans (h1.trans h2)

def RejectTrace (start : D) (rows : List Symbol) : Prop :=
 ∃ v p a c, TM2.Reaches machine start (cfg .reject v p a [] c rows)

theorem fixed_reject (i : Fin 11) (candidate : ZFR.Formula)
 (h : ZFR.ExecutableZF.axiomFormula (FixedAxiomCheck.witness i) ≠ some candidate)
 (s : List ZFR.TokenVM.Value) (v : Option Symbol) (p rows : List Symbol) :
 RejectTrace (cfg (.run (.dispatch .start)) v (payloadBits (ZFR.TokenVM.emitWitness (FixedAxiomCheck.witness i)) ++ p)
   (TypedContext.stack (.formula candidate :: s)) [] [] rows) rows := by
 have hc : candidate ≠ FixedAxiomCheck.formula i := by intro he; subst candidate; exact h (FixedAxiomCheck.formula_spec i)
 obtain ⟨w,h0⟩ := fixed_entry i v p (TypedContext.stack (.formula candidate :: s)) [] rows
 obtain ⟨w',a',c',hr⟩ := FixedAxiomCheck.reject i candidate hc w p (TypedContext.stack s) []
 have h1 := FourStack.lift4_run roles roles_injective Q.fixed FixedAxiomCheck.machine machine agree_fixed
  (ContextProgram.storage [] [] [] [] rows) hr (by simp [FourStack.cfg4])
 simp only [embed_fixed] at h1
 have h2 : TM2.Reaches machine (cfg (.fixed .reject) w' p a' [] c' rows)
  (cfg .reject w' p a' [] c' rows) := Relation.ReflTransGen.single rfl
 refine ⟨w',p,a',c',?_⟩
 simp only [fixed_codes,TypedContext.stack,List.flatMap_cons] at h0 ⊢
 exact h0.trans (h1.trans h2)

theorem schema_reject (r : Bool) (n : Nat) (body candidate : ZFR.Formula)
 (h : ZFR.ExecutableZF.axiomFormula (SchemaAxiomCheck.witness r n body) ≠ some candidate)
 (s : List ZFR.TokenVM.Value) (v : Option Symbol) (p rows : List Symbol) :
 RejectTrace (cfg (.run (.dispatch .start)) v (payloadBits (ZFR.TokenVM.emitWitness (SchemaAxiomCheck.witness r n body)) ++ p)
   (TypedContext.stack (.formula candidate :: s)) [] [] rows) rows := by
 obtain ⟨w,h0⟩ := schema_prefix r n body candidate s v p rows
 obtain ⟨w',p',a',c',hr⟩ := SchemaAxiomCheck.rejects r n body candidate h w p (TypedContext.stack s) []
 have h1 := FourStack.lift4_run roles roles_injective Q.schema SchemaAxiomCheck.machine machine agree_schema
  (ContextProgram.storage [] [] [] [] rows) hr (by simp [FourStack.cfg4])
 simp only [embed_schema] at h1
 have h2 : TM2.Reaches machine (cfg (.schema .reject) w' p' a' [] c' rows)
  (cfg .reject w' p' a' [] c' rows) := Relation.ReflTransGen.single rfl
 refine ⟨w',p',a',c',?_⟩
 simp only [TM2.Reaches,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] at h0 h1 h2 ⊢
 exact h0.trans (h1.trans h2)

theorem accepts (w : ZFR.ExecutableZF.AxiomWitness) (candidate : ZFR.Formula)
 (h : ZFR.ExecutableZF.axiomFormula w = some candidate)
 (s : List ZFR.TokenVM.Value) (v : Option Symbol) (p rows : List Symbol) :
 TM2.Reaches machine
  (cfg (.run (.dispatch .start)) v (payloadBits (ZFR.TokenVM.emitWitness w) ++ p)
   (TypedContext.stack (.formula candidate :: s)) [] [] rows)
  (cfg .accept (some .frameEnd) p (TypedContext.stack s) [] [] rows) := by
 cases w with
 | refl => exact fixed_accept 0 candidate h s v p rows
 | sym => exact fixed_accept 1 candidate h s v p rows
 | trans => exact fixed_accept 2 candidate h s v p rows
 | eqElem => exact fixed_accept 3 candidate h s v p rows
 | ext => exact fixed_accept 4 candidate h s v p rows
 | empty => exact fixed_accept 5 candidate h s v p rows
 | pair => exact fixed_accept 6 candidate h s v p rows
 | union => exact fixed_accept 7 candidate h s v p rows
 | power => exact fixed_accept 8 candidate h s v p rows
 | omega => exact fixed_accept 9 candidate h s v p rows
 | foundation => exact fixed_accept 10 candidate h s v p rows
 | separation n body => exact schema_accept false n body candidate h s v p rows
 | replacement n body => exact schema_accept true n body candidate h s v p rows

theorem rejects (w : ZFR.ExecutableZF.AxiomWitness) (candidate : ZFR.Formula)
 (h : ZFR.ExecutableZF.axiomFormula w ≠ some candidate)
 (s : List ZFR.TokenVM.Value) (v : Option Symbol) (p rows : List Symbol) :
 RejectTrace (cfg (.run (.dispatch .start)) v (payloadBits (ZFR.TokenVM.emitWitness w) ++ p)
   (TypedContext.stack (.formula candidate :: s)) [] [] rows) rows := by
 cases w with
 | refl => exact fixed_reject 0 candidate h s v p rows
 | sym => exact fixed_reject 1 candidate h s v p rows
 | trans => exact fixed_reject 2 candidate h s v p rows
 | eqElem => exact fixed_reject 3 candidate h s v p rows
 | ext => exact fixed_reject 4 candidate h s v p rows
 | empty => exact fixed_reject 5 candidate h s v p rows
 | pair => exact fixed_reject 6 candidate h s v p rows
 | union => exact fixed_reject 7 candidate h s v p rows
 | power => exact fixed_reject 8 candidate h s v p rows
 | omega => exact fixed_reject 9 candidate h s v p rows
 | foundation => exact fixed_reject 10 candidate h s v p rows
 | separation n body => exact schema_reject false n body candidate h s v p rows
 | replacement n body => exact schema_reject true n body candidate h s v p rows

theorem halted_labels (q : Q) (hq : machine q = .halt) (v : Option Symbol) (p a c rows : List Symbol)
 {d : D} (h : TM2.Reaches machine (cfg q v p a [] c rows) d) : d.l = some q ∨ d.l = none := by
 rcases Relation.ReflTransGen.cases_head h with he | ⟨b,hb,hbd⟩
 · exact Or.inl (congrArg TM2.Cfg.l he).symm
 · have hs : TM2.step machine (cfg q v p a [] c rows) = some ⟨none,v,ContextProgram.storage p a [] c rows⟩ := by
    simp [cfg,TM2.step,hq,TM2.stepAux]
   have he : b = ⟨none,v,ContextProgram.storage p a [] c rows⟩ := Option.some.inj (hb.symm.trans hs)
   subst b
   exact Or.inr (congrArg TM2.Cfg.l (Routine.dead_reaches machine rfl hbd))

/-- Parses the literal canonical witness stream, not trusted host-produced
parameters. Every fixed or schema witness is checked against its exact formula. -/
theorem accepts_iff (w : ZFR.ExecutableZF.AxiomWitness) (candidate : ZFR.Formula)
 (s : List ZFR.TokenVM.Value) (v : Option Symbol) (p rows : List Symbol) :
 TM2.Reaches machine
  (cfg (.run (.dispatch .start)) v (payloadBits (ZFR.TokenVM.emitWitness w) ++ p)
   (TypedContext.stack (.formula candidate :: s)) [] [] rows)
  (cfg .accept (some .frameEnd) p (TypedContext.stack s) [] [] rows) ↔
 ZFR.ExecutableZF.axiomFormula w = some candidate := by
 constructor
 · intro ha
   by_contra hn
   obtain ⟨v',p',a',c',hr⟩ := rejects w candidate hn s v p rows
   have hu : Relator.RightUnique (fun a b : D => TM2.step machine a = some b) := by
    intro a b c hab hac
    exact Option.some.inj (hab.symm.trans hac)
   rcases Relation.ReflTransGen.total_of_right_unique hu hr ha with h | h
   · rcases halted_labels .reject rfl v' p' a' c' rows h with he | he
     all_goals simp [cfg] at he
   · rcases halted_labels .accept rfl (some .frameEnd) p (TypedContext.stack s) [] rows h with he | he
     all_goals simp [cfg] at he
 · intro h
   exact accepts w candidate h s v p rows

end RosserDirect.WitnessParser
