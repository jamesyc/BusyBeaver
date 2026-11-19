module
public import DirectSchemaConstruct
public import DirectSchemaScope
@[expose] public section
namespace RosserDirect.SchemaAxiomCheck
open Turing Segment FourStack
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 16384

def opcode (r : Bool) : Fin 42 := if r then 39 else 38
def token (r : Bool) := 2*(opcode r).val+1

def witness (r : Bool) (n : Nat) (f : ZFR.Formula) : ZFR.ExecutableZF.AxiomWitness :=
 if r then .replacement n f else .separation n f

theorem axiom_spec (r : Bool) (n : Nat) (f candidate : ZFR.Formula) :
 ZFR.ExecutableZF.axiomFormula (witness r n f) = some candidate ↔
 ZFR.Bound f (SchemaScope.cutoff r n) ∧ candidate = SchemaConstruct.schema r n f := by
 cases r <;> simp only [witness,SchemaScope.cutoff,SchemaConstruct.schema,Bool.false_eq_true,ite_false,ite_true]
 all_goals
  simp only [ZFR.ExecutableZF.axiomFormula,ZFR.ExecutableZF.checkAxiom]
  split_ifs with h
  · simp [← ZFR.ExecutableZF.boundCheck_iff,h,eq_comm]
  · simp [← ZFR.ExecutableZF.boundCheck_iff,h]

inductive Q where
 | dispatch (q : OpcodeDispatch.Control) | copy (r : Bool) (q : Grammar.CopyControl TypedBlock.Control)
 | scope (r : Bool) (q : SchemaScope.Q) | build (r : Bool) (q : SchemaConstruct.Q)
 | compare (r : Bool) (q : RosserDirectEquality.Label) | accept (r : Bool) | reject
 deriving DecidableEq, Fintype, Inhabited

def select (op : Fin 42) : Q :=
 if op.val = 38 then .copy false (.scan (.run 1 .start))
 else if op.val = 39 then .copy true (.scan (.run 1 .start)) else .reject

def machine : Q → Stmt4 Q
 | .dispatch (.opcode op) => .goto (fun _ => select op)
 | .dispatch q => Routine.relocate readRoles Q.dispatch (OpcodeDispatch.machine q)
 | .copy r .done => .goto (fun _ => .scope r (.save .scan))
 | .copy r q => Routine.relocate dataRoles (Q.copy r) (TypedBlock.machine q)
 | .scope r .accept => .goto (fun _ => .build r .start)
 | .scope _ .reject => .goto (fun _ => .reject)
 | .scope r q => Routine.relocate ScopeGuard.swap (Q.scope r) (SchemaScope.machine r q)
 | .build r .done => .goto (fun _ => .compare r .scan)
 | .build r q => Routine.relocate id (Q.build r) (SchemaConstruct.machine r q)
 | .compare r .equal => .goto (fun _ => .accept r)
 | .compare _ .different => .goto (fun _ => .reject)
 | .compare r q => Routine.relocate dataRoles (Q.compare r) (RosserDirectEquality.machine q)
 | .accept _ | .reject => .halt

theorem agree_dispatch (q : OpcodeDispatch.Control) (h : OpcodeDispatch.machine q ≠ .halt) :
 machine (.dispatch q) = Routine.relocate readRoles Q.dispatch (OpcodeDispatch.machine q) := by
 cases q <;> simp_all [machine,OpcodeDispatch.machine,OpcodeDispatch.active]
theorem agree_copy (r : Bool) (q : Grammar.CopyControl TypedBlock.Control) (h : TypedBlock.machine q ≠ .halt) :
 machine (.copy r q) = Routine.relocate dataRoles (Q.copy r) (TypedBlock.machine q) := by
 cases q <;> simp_all [machine,TypedBlock.machine,Grammar.copyMachine]
theorem agree_scope (r : Bool) (q : SchemaScope.Q) (h : SchemaScope.machine r q ≠ .halt) :
 machine (.scope r q) = Routine.relocate ScopeGuard.swap (Q.scope r) (SchemaScope.machine r q) := by
 cases q <;> simp_all [machine,SchemaScope.machine]
theorem agree_build (r : Bool) (q : SchemaConstruct.Q) (h : SchemaConstruct.machine r q ≠ .halt) :
 machine (.build r q) = Routine.relocate id (Q.build r) (SchemaConstruct.machine r q) := by
 cases q <;> simp_all [machine,SchemaConstruct.machine]
theorem agree_compare (r : Bool) (q : RosserDirectEquality.Label) (h : RosserDirectEquality.machine q ≠ .halt) :
 machine (.compare r q) = Routine.relocate dataRoles (Q.compare r) (RosserDirectEquality.machine q) := by
 cases q <;> simp_all [machine,RosserDirectEquality.machine]

theorem dispatch (r : Bool) (v : Option Symbol) (p a c : List Symbol) :
 ∃ w, TM2.Reaches machine
  (cfg4 (.dispatch .start) v (tokenBits (token r) ++ p) a [] c)
  (cfg4 (.copy r (.scan (.run 1 .start))) w p a [] c) := by
 obtain ⟨w,hw⟩ := OpcodeDispatch.dispatch_opcode (opcode r) v p [] a
 have h0 := Routine.lift_embedded_run readRoles read_injective Q.dispatch
  OpcodeDispatch.machine machine agree_dispatch (fun _ => c) hw (by simp [config])
 simp only [embed_read] at h0
 have he : select (opcode r) = .copy r (.scan (.run 1 .start)) := by cases r <;> rfl
 have h1 : TM2.Reaches machine (cfg4 (.dispatch (.opcode (opcode r))) w p a [] c)
  (cfg4 (.copy r (.scan (.run 1 .start))) w p a [] c) := by
  apply Relation.ReflTransGen.single
  simp [machine,he,cfg4,TM2.step,TM2.stepAux]
 exact ⟨w,h0.trans h1⟩

theorem embed_scope (r : Bool) (q : SchemaScope.Q) (v : Option Symbol) (p a s c : List Symbol) :
 embed4 ScopeGuard.swap (Q.scope r) (cfg4 q v p a s c) (fun _ => []) = cfg4 (.scope r q) v p c s a := by
 unfold embed4 cfg4
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem copy (r : Bool) (n : Nat) (f : ZFR.Formula) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches machine
  (cfg4 (.copy r (.scan (.run 1 .start))) v p (TypedContext.stack [.formula f,.nat n] ++ a) [] c)
  (cfg4 (.scope r (.save .scan)) none p (TypedContext.stack [.formula f,.nat n] ++ a) [] (TypedContext.stack [.formula f,.nat n] ++ c)) := by
 have h0 := Routine.lift_embedded_run dataRoles data_injective (Q.copy r)
  TypedBlock.machine machine (agree_copy r) (fun _ => p)
  (TypedBlock.copy_block 1 [.formula f,.nat n] rfl v a c) (by simp [config])
 simp only [embed_data] at h0
 have h1 : TM2.Reaches machine
  (cfg4 (.copy r .done) none p (TypedContext.stack [.formula f,.nat n] ++ a) [] (TypedContext.stack [.formula f,.nat n] ++ c))
  (cfg4 (.scope r (.save .scan)) none p (TypedContext.stack [.formula f,.nat n] ++ a) [] (TypedContext.stack [.formula f,.nat n] ++ c)) := Relation.ReflTransGen.single rfl
 exact h0.trans h1

theorem prepare (r : Bool) (n : Nat) (f : ZFR.Formula) (hf : ZFR.Bound f (SchemaScope.cutoff r n))
 (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches machine
  (cfg4 (.dispatch .start) v (tokenBits (token r) ++ p) (TypedContext.stack [.formula f,.nat n] ++ a) [] c)
  (cfg4 (.compare r .scan) none p a [] (TypedContext.value (.formula (SchemaConstruct.schema r n f)) ++ c)) := by
 obtain ⟨w,h0⟩ := dispatch r v p (TypedContext.stack [.formula f,.nat n] ++ a) c
 have h1 := copy r n f w p a c
 have h2 := FourStack.lift4_run ScopeGuard.swap ScopeGuard.swap_injective (Q.scope r) (SchemaScope.machine r) machine (agree_scope r)
  (fun _ => []) (SchemaScope.accept r f n hf none p c (TypedContext.stack [.formula f,.nat n] ++ a)) (by simp [cfg4])
 simp only [embed_scope] at h2
 have h3 : TM2.Reaches machine
  (cfg4 (.scope r .accept) none p (TypedContext.stack [.formula f,.nat n] ++ a) [] c)
  (cfg4 (.build r .start) none p (TypedContext.stack [.formula f,.nat n] ++ a) [] c) := Relation.ReflTransGen.single rfl
 have h4 := FourStack.relabel_run (Q.build r) (SchemaConstruct.machine r) machine (agree_build r)
  _ _ _ _ _ _ _ _ _ _ _ _ (SchemaConstruct.construct r n f none p a c)
 have h5 : TM2.Reaches machine
  (cfg4 (.build r .done) none p a [] (TypedContext.value (.formula (SchemaConstruct.schema r n f)) ++ c))
  (cfg4 (.compare r .scan) none p a [] (TypedContext.value (.formula (SchemaConstruct.schema r n f)) ++ c)) := Relation.ReflTransGen.single rfl
 exact h0.trans (h1.trans (h2.trans (h3.trans (h4.trans h5))))

theorem embed_compare (r : Bool) (q : RosserDirectEquality.Label) (v : Option Symbol) (p a s c : List Symbol) :
 Routine.embed dataRoles (Q.compare r) (RosserDirectEquality.cfg q v a s c) (fun _ => p) = cfg4 (.compare r q) v p a s c := by
 unfold Routine.embed RosserDirectEquality.cfg cfg4
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem accept (r : Bool) (n : Nat) (f : ZFR.Formula) (hf : ZFR.Bound f (SchemaScope.cutoff r n))
 (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches machine
  (cfg4 (.dispatch .start) v (tokenBits (token r) ++ p)
   (TypedContext.stack [.formula f,.nat n,.formula (SchemaConstruct.schema r n f)] ++ a) [] c)
  (cfg4 (.accept r) (some .frameEnd) p a [] c) := by
 have h0 := prepare r n f hf v p (TypedContext.value (.formula (SchemaConstruct.schema r n f)) ++ a) c
 have h1 := Routine.lift_embedded_run dataRoles data_injective (Q.compare r)
  RosserDirectEquality.machine machine (agree_compare r) (fun _ => p)
  (RosserDirectEquality.equal_frames (ScopeCheck.payload (SchemaConstruct.schema r n f)) (payloadBits_no_end _) none a [] c)
  (by simp [RosserDirectEquality.cfg])
 simp only [embed_compare] at h1
 have h2 : TM2.Reaches machine (cfg4 (.compare r .equal) (some .frameEnd) p a [] c)
  (cfg4 (.accept r) (some .frameEnd) p a [] c) := Relation.ReflTransGen.single rfl
 have h12 : TM2.Reaches machine
  (cfg4 (.compare r .scan) none p (TypedContext.value (.formula (SchemaConstruct.schema r n f)) ++ a) []
   (TypedContext.value (.formula (SchemaConstruct.schema r n f)) ++ c)) (cfg4 (.accept r) (some .frameEnd) p a [] c) := by
  simpa only [TM2.Reaches,ScopeCheck.value_formula,List.append_assoc,List.cons_append,List.nil_append] using h1.trans h2
 simpa only [TM2.Reaches,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] using h0.trans h12

def RejectTrace (cfg : Cfg4 Q) : Prop := ∃ w p a c, TM2.Reaches machine cfg (cfg4 .reject w p a [] c)

theorem reject_scope (r : Bool) (n : Nat) (f : ZFR.Formula) (hf : ¬ ZFR.Bound f (SchemaScope.cutoff r n))
 (v : Option Symbol) (p a c : List Symbol) :
 RejectTrace (cfg4 (.dispatch .start) v (tokenBits (token r) ++ p) (TypedContext.stack [.formula f,.nat n] ++ a) [] c) := by
 obtain ⟨w,h0⟩ := dispatch r v p (TypedContext.stack [.formula f,.nat n] ++ a) c
 have h1 := copy r n f w p a c
 obtain ⟨w',p',c',hr⟩ := SchemaScope.reject r f n hf none p c (TypedContext.stack [.formula f,.nat n] ++ a)
 have h2 := FourStack.lift4_run ScopeGuard.swap ScopeGuard.swap_injective (Q.scope r) (SchemaScope.machine r) machine (agree_scope r)
  (fun _ => []) hr (by simp [cfg4])
 simp only [embed_scope] at h2
 have h3 : TM2.Reaches machine (cfg4 (.scope r .reject) w' p' (TypedContext.stack [.formula f,.nat n] ++ a) [] c')
  (cfg4 .reject w' p' (TypedContext.stack [.formula f,.nat n] ++ a) [] c') := Relation.ReflTransGen.single rfl
 exact ⟨w',p',_,c',h0.trans (h1.trans (h2.trans h3))⟩

theorem reject_formula (r : Bool) (n : Nat) (f candidate : ZFR.Formula)
 (hf : ZFR.Bound f (SchemaScope.cutoff r n)) (hne : candidate ≠ SchemaConstruct.schema r n f)
 (v : Option Symbol) (p a c : List Symbol) :
 RejectTrace (cfg4 (.dispatch .start) v (tokenBits (token r) ++ p)
   (TypedContext.stack [.formula f,.nat n,.formula candidate] ++ a) [] c) := by
 have neq : ScopeCheck.payload candidate ≠ ScopeCheck.payload (SchemaConstruct.schema r n f) := by
  intro h
  exact hne (emitFormula_injective (List.cons.inj (payloadBits_injective h)).2)
 have h0 := prepare r n f hf v p (TypedContext.value (.formula candidate) ++ a) c
 obtain ⟨w,a',c',hr⟩ := RosserDirectEquality.unequal_frames
  (ScopeCheck.payload candidate) (ScopeCheck.payload (SchemaConstruct.schema r n f))
  (payloadBits_no_end _) (payloadBits_no_end _) neq none a [] c
 have h1 := Routine.lift_embedded_run dataRoles data_injective (Q.compare r)
  RosserDirectEquality.machine machine (agree_compare r) (fun _ => p) hr (by simp [RosserDirectEquality.cfg])
 simp only [embed_compare] at h1
 have h2 : TM2.Reaches machine (cfg4 (.compare r .different) w p a' [] c')
  (cfg4 .reject w p a' [] c') := Relation.ReflTransGen.single rfl
 have h12 : TM2.Reaches machine
  (cfg4 (.compare r .scan) none p (TypedContext.value (.formula candidate) ++ a) []
   (TypedContext.value (.formula (SchemaConstruct.schema r n f)) ++ c)) (cfg4 .reject w p a' [] c') := by
  simpa only [TM2.Reaches,ScopeCheck.value_formula,List.append_assoc,List.cons_append,List.nil_append] using h1.trans h2
 refine ⟨w,p,a',c',?_⟩
 simpa only [TM2.Reaches,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] using h0.trans h12

theorem rejects (r : Bool) (n : Nat) (f candidate : ZFR.Formula)
 (h : ZFR.ExecutableZF.axiomFormula (witness r n f) ≠ some candidate)
 (v : Option Symbol) (p a c : List Symbol) :
 RejectTrace (cfg4 (.dispatch .start) v (tokenBits (token r) ++ p)
  (TypedContext.stack [.formula f,.nat n,.formula candidate] ++ a) [] c) := by
 by_cases hf : ZFR.Bound f (SchemaScope.cutoff r n)
 · have he : candidate ≠ SchemaConstruct.schema r n f := by
    intro he
    exact h ((axiom_spec r n f candidate).mpr ⟨hf,he⟩)
   exact reject_formula r n f candidate hf he v p a c
 · simpa only [RejectTrace,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
    using reject_scope r n f hf v p (TypedContext.value (.formula candidate) ++ a) c

theorem halted_labels (q : Q) (hq : machine q = .halt) (v : Option Symbol) (p a c : List Symbol)
 {d : Cfg4 Q} (h : TM2.Reaches machine (cfg4 q v p a [] c) d) : d.l = some q ∨ d.l = none := by
 rcases Relation.ReflTransGen.cases_head h with he | ⟨b,hb,hbd⟩
 · exact Or.inl (congrArg TM2.Cfg.l he).symm
 · have hs : TM2.step machine (cfg4 q v p a [] c) = some ⟨none,v,store4 p a [] c⟩ := by
    simp [cfg4,TM2.step,hq,TM2.stepAux]
   have he : b = ⟨none,v,store4 p a [] c⟩ := Option.some.inj (hb.symm.trans hs)
   subst b
   exact Or.inr (congrArg TM2.Cfg.l (Routine.dead_reaches machine rfl hbd))

/-- Exact finite-machine schema-witness validation for canonical parsed fields.
Parameters/body must still be parsed from the witness stream by the caller. -/
theorem accepts_iff (r : Bool) (n : Nat) (f candidate : ZFR.Formula)
 (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches machine
  (cfg4 (.dispatch .start) v (tokenBits (token r) ++ p)
   (TypedContext.stack [.formula f,.nat n,.formula candidate] ++ a) [] c)
  (cfg4 (.accept r) (some .frameEnd) p a [] c) ↔
 ZFR.ExecutableZF.axiomFormula (witness r n f) = some candidate := by
 constructor
 · intro ha
   by_contra hn
   obtain ⟨w,p',a',c',hr⟩ := rejects r n f candidate hn v p a c
   have hu : Relator.RightUnique (fun a b : Cfg4 Q => TM2.step machine a = some b) := by
    intro a b c hab hac
    exact Option.some.inj (hab.symm.trans hac)
   rcases Relation.ReflTransGen.total_of_right_unique hu hr ha with h | h
   · rcases halted_labels .reject rfl w p' a' c' h with he | he
     all_goals simp [cfg4] at he
   · rcases halted_labels (.accept r) rfl (some .frameEnd) p a c h with he | he
     all_goals simp [cfg4] at he
 · intro h
   obtain ⟨hf,he⟩ := (axiom_spec r n f candidate).mp h
   subst candidate
   exact accept r n f hf v p a c


end RosserDirect.SchemaAxiomCheck
