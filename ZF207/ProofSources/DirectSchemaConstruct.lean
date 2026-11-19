module
public import DirectReplacementBodies
public import DirectSchemaTemplates
public import DirectSchemaPrefix
@[expose] public section
namespace RosserDirect.SchemaConstruct
open Turing Segment FourStack
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

def template (r : Bool) := if r then SchemaTemplates.replacementProgram else SchemaTemplates.separationProgram
def baseFormula (r : Bool) (f : ZFR.Formula) :=
 if r then ZFR.replacementFormula (ReplacementBodies.A f) (ReplacementBodies.B f) (ReplacementBodies.C f)
 else ZFR.separationFormula (ZFR.rename ZFR.sepIndex f)
def schema (r : Bool) (n : Nat) (f : ZFR.Formula) := if r then ZFR.replacementSchema n f else ZFR.separationSchema n f

inductive Q where
 | start | sepRename (q : SchemaRenameMachine.Q) | backSep (q : Label)
 | repBodies (q : ReplacementBodies.Q) | template (q : FormulaTemplate.Q)
 | backTemplate (q : Label) | prefix (q : SchemaPrefix.Q) | done
 deriving DecidableEq, Fintype, Inhabited

def machine (r : Bool) : Q → Stmt4 Q
 | .start => .goto (fun _ => if r then .repBodies (.duplicate false (.first (.scan (.run 0 .start)))) else .sepRename (.start 0))
 | .sepRename .done => .goto (fun _ => .backSep .scan)
 | .sepRename q => Routine.relocate id Q.sepRename (SchemaRenameMachine.machine .separation q)
 | .backSep .done => .goto (fun _ => .template (.run 0))
 | .backSep q => Routine.relocate outputRoles Q.backSep (RosserDirect.machine q)
 | .repBodies .done => .goto (fun _ => .template (.run 0))
 | .repBodies q => Routine.relocate id Q.repBodies (ReplacementBodies.machine q)
 | .template .done => .goto (fun _ => .backTemplate .scan)
 | .template q => Routine.relocate id Q.template (FormulaTemplate.machine (template r) q)
 | .backTemplate .done => .goto (fun _ => .prefix (.prepare .formulaTag))
 | .backTemplate q => Routine.relocate outputRoles Q.backTemplate (RosserDirect.machine q)
 | .prefix .done => .goto (fun _ => .done)
 | .prefix q => Routine.relocate id Q.prefix (SchemaPrefix.machine q)
 | .done => .halt

theorem agree_sep (r : Bool) (q : SchemaRenameMachine.Q) (h : SchemaRenameMachine.machine .separation q ≠ .halt) :
 machine r (.sepRename q) = Routine.relocate id Q.sepRename (SchemaRenameMachine.machine .separation q) := by
 cases q <;> simp_all [machine,SchemaRenameMachine.machine]
theorem agree_backSep (r : Bool) (q : Label) (h : RosserDirect.machine q ≠ .halt) :
 machine r (.backSep q) = Routine.relocate outputRoles Q.backSep (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]
theorem agree_rep (r : Bool) (q : ReplacementBodies.Q) (h : ReplacementBodies.machine q ≠ .halt) :
 machine r (.repBodies q) = Routine.relocate id Q.repBodies (ReplacementBodies.machine q) := by
 cases q <;> simp_all [machine,ReplacementBodies.machine]
theorem agree_template (r : Bool) (q : FormulaTemplate.Q) (h : FormulaTemplate.machine (template r) q ≠ .halt) :
 machine r (.template q) = Routine.relocate id Q.template (FormulaTemplate.machine (template r) q) := by
 cases q <;> simp_all [machine,FormulaTemplate.machine]
theorem agree_backTemplate (r : Bool) (q : Label) (h : RosserDirect.machine q ≠ .halt) :
 machine r (.backTemplate q) = Routine.relocate outputRoles Q.backTemplate (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]
theorem agree_prefix (r : Bool) (q : SchemaPrefix.Q) (h : SchemaPrefix.machine q ≠ .halt) :
 machine r (.prefix q) = Routine.relocate id Q.prefix (SchemaPrefix.machine q) := by
 cases q <;> simp_all [machine,SchemaPrefix.machine]

theorem base (r : Bool) (f : ZFR.Formula) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches (machine r)
  (cfg4 .start v p (TypedContext.value (.formula f) ++ a) [] c)
  (cfg4 (.template .done) none p a [] (TypedContext.value (.formula (baseFormula r f)) ++ c)) := by
 cases r with
 | false =>
  have h0 : TM2.Reaches (machine false)
   (cfg4 .start v p (TypedContext.value (.formula f) ++ a) [] c)
   (cfg4 (.sepRename (.start 0)) v p (TypedContext.value (.formula f) ++ a) [] c) := Relation.ReflTransGen.single rfl
  have h1 := FourStack.relabel_run Q.sepRename (SchemaRenameMachine.machine .separation) (machine false) (agree_sep false)
   _ _ _ _ _ _ _ _ _ _ _ _ (SchemaRenameMachine.execute .separation f v p a c)
  have h2 : TM2.Reaches (machine false)
   (cfg4 (.sepRename .done) none p a [] (TypedContext.value (.formula (ZFR.rename ZFR.sepIndex f)) ++ c))
   (cfg4 (.backSep .scan) none p a [] (TypedContext.value (.formula (ZFR.rename ZFR.sepIndex f)) ++ c)) := Relation.ReflTransGen.single rfl
  have h3 := Routine.lift_embedded_run outputRoles output_injective Q.backSep
   RosserDirect.machine (machine false) (agree_backSep false) (fun _ => p)
   (AllIntroPremise.move_formula (ZFR.rename ZFR.sepIndex f) none c a) (by simp [config])
  simp only [embed_output] at h3
  have h4 : TM2.Reaches (machine false)
   (cfg4 (.backSep .done) none p (TypedContext.value (.formula (ZFR.rename ZFR.sepIndex f)) ++ a) [] c)
   (cfg4 (.template (.run 0)) none p (TypedContext.value (.formula (ZFR.rename ZFR.sepIndex f)) ++ a) [] c) := Relation.ReflTransGen.single rfl
  have h5 := FourStack.relabel_run Q.template (FormulaTemplate.machine (template false)) (machine false) (agree_template false)
   _ _ _ _ _ _ _ _ _ _ _ _ (SchemaTemplates.separation (ZFR.rename ZFR.sepIndex f) none p a c)
  exact h0.trans (h1.trans (h2.trans (h3.trans (h4.trans h5))))
 | true =>
  have h0 : TM2.Reaches (machine true)
   (cfg4 .start v p (TypedContext.value (.formula f) ++ a) [] c)
   (cfg4 (.repBodies (.duplicate false (.first (.scan (.run 0 .start))))) v p (TypedContext.value (.formula f) ++ a) [] c) := Relation.ReflTransGen.single rfl
  have h1 := FourStack.relabel_run Q.repBodies ReplacementBodies.machine (machine true) (agree_rep true)
   _ _ _ _ _ _ _ _ _ _ _ _ (ReplacementBodies.construct f v p a c)
  have h2 : TM2.Reaches (machine true)
   (cfg4 (.repBodies .done) none p (TypedContext.stack [.formula (ReplacementBodies.C f),.formula (ReplacementBodies.B f),.formula (ReplacementBodies.A f)] ++ a) [] c)
   (cfg4 (.template (.run 0)) none p (TypedContext.stack [.formula (ReplacementBodies.C f),.formula (ReplacementBodies.B f),.formula (ReplacementBodies.A f)] ++ a) [] c) := Relation.ReflTransGen.single rfl
  have h3 := FourStack.relabel_run Q.template (FormulaTemplate.machine (template true)) (machine true) (agree_template true)
   _ _ _ _ _ _ _ _ _ _ _ _ (SchemaTemplates.replacement (ReplacementBodies.C f) (ReplacementBodies.B f) (ReplacementBodies.A f) none p a c)
  simp only [TM2.Reaches,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] at h0 h1 h2 h3 ⊢
  exact h0.trans (h1.trans (h2.trans h3))

/-- Actual finite four-stack construction of both exact source ZF schemas,
including every parameter binder; no unbounded formula callback. -/
theorem construct (r : Bool) (n : Nat) (f : ZFR.Formula) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches (machine r)
  (cfg4 .start v p (TypedContext.stack [.formula f,.nat n] ++ a) [] c)
  (cfg4 .done none p a [] (TypedContext.value (.formula (schema r n f)) ++ c)) := by
 have h0 := base r f v p (TypedContext.value (.nat n) ++ a) c
 have h1 : TM2.Reaches (machine r)
  (cfg4 (.template .done) none p (TypedContext.value (.nat n) ++ a) [] (TypedContext.value (.formula (baseFormula r f)) ++ c))
  (cfg4 (.backTemplate .scan) none p (TypedContext.value (.nat n) ++ a) [] (TypedContext.value (.formula (baseFormula r f)) ++ c)) := Relation.ReflTransGen.single rfl
 have h2 := Routine.lift_embedded_run outputRoles output_injective Q.backTemplate
  RosserDirect.machine (machine r) (agree_backTemplate r) (fun _ => p)
  (AllIntroPremise.move_formula (baseFormula r f) none c (TypedContext.value (.nat n) ++ a)) (by simp [config])
 simp only [embed_output] at h2
 have h3 : TM2.Reaches (machine r)
  (cfg4 (.backTemplate .done) none p (TypedContext.value (.formula (baseFormula r f)) ++ TypedContext.value (.nat n) ++ a) [] c)
  (cfg4 (.prefix (.prepare .formulaTag)) none p (TypedContext.value (.formula (baseFormula r f)) ++ TypedContext.value (.nat n) ++ a) [] c) := Relation.ReflTransGen.single rfl
 have h4 := FourStack.relabel_run Q.prefix SchemaPrefix.machine (machine r) (agree_prefix r)
  _ _ _ _ _ _ _ _ _ _ _ _ (SchemaPrefix.construct n (baseFormula r f) none p a c)
 have h5 : TM2.Reaches (machine r)
  (cfg4 (.prefix .done) none p a [] (TypedContext.value (.formula (ZFR.allPrefix n (baseFormula r f))) ++ c))
  (cfg4 .done none p a [] (TypedContext.value (.formula (ZFR.allPrefix n (baseFormula r f))) ++ c)) := Relation.ReflTransGen.single rfl
 have eqf : ZFR.allPrefix n (baseFormula r f) = schema r n f := by cases r <;> rfl
 simp only [TM2.Reaches,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] at h0 h1 h2 h3 h4 h5 ⊢
 simpa only [eqf] using h0.trans (h1.trans (h2.trans (h3.trans (h4.trans h5))))

end RosserDirect.SchemaConstruct
