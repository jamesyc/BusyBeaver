module
public import SchemaRenameIdentities
public import DirectAllIntroPremise
@[expose] public section
namespace RosserDirect.FixedTransform
open Turing Segment FourStack
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

inductive Action where
 | shift1 | shift2 | subst0 | subst2 | subst3
 deriving DecidableEq, Fintype, Inhabited

def isShift : Action → Bool
 | .shift1 | .shift2 => true | _ => false

def argument : Action → Nat
 | .shift1 => 1 | .shift2 | .subst2 => 2 | .subst0 => 0 | .subst3 => 3

def result (act : Action) (f : ZFR.Formula) : ZFR.Formula :=
 if isShift act then DepthShift.shifted (argument act) f else ZFR.subst (argument act) f

def args (act : Action) : List Symbol :=
 TypedContext.value (.nat (argument act)) ++ if isShift act then [.frameEnd] else []

inductive Q where
 | save (q : Label) | setup | restore (q : Label)
 | shift (q : DepthShift.Q) | subst (q : SubstTraversal.Q) | done
 deriving DecidableEq, Fintype, Inhabited

def pushData : List Symbol → Stmt4 Q → Stmt4 Q
 | [], k => k
 | x::xs,k => pushData xs (.push .data (fun _ => x) k)

def entry (act : Action) : Q :=
 if isShift act then .shift (.prepare .formulaTag) else .subst (.prepare (.reverse .formulaTag))

def machine (act : Action) : Q → Stmt4 Q
 | .save .done => .goto (fun _ => .setup)
 | .save q => Routine.relocate prepareRoles Q.save (RosserDirect.machine q)
 | .setup => pushData (args act) (.goto (fun _ => .restore .scan))
 | .restore .done => .goto (fun _ => entry act)
 | .restore q => Routine.relocate readRoles Q.restore (RosserDirect.machine q)
 | .shift .done => .goto (fun _ => .done)
 | .shift q => Routine.relocate id Q.shift (DepthShift.machine q)
 | .subst .done => .goto (fun _ => .done)
 | .subst q => Routine.relocate id Q.subst (SubstTraversal.machine q)
 | .done => .halt

theorem agree_save (act : Action) (q : Label) (h : RosserDirect.machine q ≠ .halt) :
 machine act (.save q) = Routine.relocate prepareRoles Q.save (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]
theorem agree_restore (act : Action) (q : Label) (h : RosserDirect.machine q ≠ .halt) :
 machine act (.restore q) = Routine.relocate readRoles Q.restore (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]
theorem agree_shift (act : Action) (q : DepthShift.Q) (h : DepthShift.machine q ≠ .halt) :
 machine act (.shift q) = Routine.relocate id Q.shift (DepthShift.machine q) := by
 cases q <;> simp_all [machine,DepthShift.machine]
theorem agree_subst (act : Action) (q : SubstTraversal.Q) (h : SubstTraversal.machine q ≠ .halt) :
 machine act (.subst q) = Routine.relocate id Q.subst (SubstTraversal.machine q) := by
 cases q <;> simp_all [machine,SubstTraversal.machine]

theorem pushData_correct (xs : List Symbol) (k : Stmt4 Q) (v : Option Symbol) (p a s c : List Symbol) :
 TM2.stepAux (pushData xs k) v (store4 p a s c) = TM2.stepAux k v (store4 p (xs++a) s c) := by
 induction xs generalizing k a with
 | nil => rfl
 | cons x xs ih =>
  rw [pushData,ih]
  simp only [TM2.stepAux]
  have he : Function.update (store4 p (xs++a) s c) K.data (x::(xs++a)) = store4 p ((x::xs)++a) s c := by
   funext j; cases j <;> rfl
  exact congrArg (TM2.stepAux k v) he

theorem setup_step (act : Action) (v : Option Symbol) (p a s c : List Symbol) :
 TM2.step (machine act) (cfg4 .setup v p a s c) =
 some (cfg4 (.restore .scan) v p (args act ++ a) s c) := by
 simp [machine,cfg4,TM2.step,pushData_correct,TM2.stepAux]

theorem prepare (act : Action) (f : ZFR.Formula) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches (machine act)
  (cfg4 (.save .scan) v p (TypedContext.value (.formula f) ++ a) [] c)
  (cfg4 (entry act) none p (TypedContext.value (.formula f) ++ args act ++ a) [] c) := by
 have h0 := Routine.lift_embedded_run prepareRoles prepare_injective Q.save
  RosserDirect.machine (machine act) (agree_save act) (fun _ => c)
  (AllIntroPremise.move_formula f v a p) (by simp [config])
 simp only [embed_prepare] at h0
 have h1 : TM2.Reaches (machine act)
  (cfg4 (.save .done) none (TypedContext.value (.formula f) ++ p) a [] c)
  (cfg4 .setup none (TypedContext.value (.formula f) ++ p) a [] c) := Relation.ReflTransGen.single rfl
 have h2 : TM2.Reaches (machine act) _ _ := Relation.ReflTransGen.single
  (setup_step act none (TypedContext.value (.formula f) ++ p) a [] c)
 have h3 := Routine.lift_embedded_run readRoles read_injective Q.restore
  RosserDirect.machine (machine act) (agree_restore act) (fun _ => c)
  (AllIntroPremise.move_formula f none p (args act ++ a)) (by simp [config])
 simp only [embed_read] at h3
 have h4 : TM2.Reaches (machine act)
  (cfg4 (.restore .done) none p (TypedContext.value (.formula f) ++ (args act ++ a)) [] c)
  (cfg4 (entry act) none p (TypedContext.value (.formula f) ++ (args act ++ a)) [] c) := Relation.ReflTransGen.single rfl
 simpa only [TM2.Reaches,List.append_assoc] using h0.trans (h1.trans (h2.trans (h3.trans h4)))

theorem execute (act : Action) (f : ZFR.Formula) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches (machine act)
  (cfg4 (.save .scan) v p (TypedContext.value (.formula f) ++ a) [] c)
  (cfg4 .done none p a [] (TypedContext.value (.formula (result act f)) ++ c)) := by
 have h0 := prepare act f v p a c
 by_cases hs : isShift act = true
 · have h1 := FourStack.relabel_run Q.shift DepthShift.machine (machine act) (agree_shift act)
    _ _ _ _ _ _ _ _ _ _ _ _ (DepthShift.shift_formula f (argument act) none p a c)
   have h2 : TM2.Reaches (machine act)
    (cfg4 (.shift .done) none p a [] (TypedContext.value (.formula (DepthShift.shifted (argument act) f)) ++ c))
    (cfg4 .done none p a [] (TypedContext.value (.formula (DepthShift.shifted (argument act) f)) ++ c)) := Relation.ReflTransGen.single rfl
   apply h0.trans
   simpa only [entry,args,result,hs,ite_true,List.append_assoc,List.singleton_append] using h1.trans h2
 · have hs : isShift act = false := Bool.eq_false_iff.mpr hs
   have h1 := FourStack.relabel_run Q.subst SubstTraversal.machine (machine act) (agree_subst act)
    _ _ _ _ _ _ _ _ _ _ _ _ (SubstTraversal.subst_formula f (argument act) none p a c)
   have h2 : TM2.Reaches (machine act)
    (cfg4 (.subst .done) none p a [] (TypedContext.value (.formula (ZFR.subst (argument act) f)) ++ c))
    (cfg4 .done none p a [] (TypedContext.value (.formula (ZFR.subst (argument act) f)) ++ c)) := Relation.ReflTransGen.single rfl
   apply h0.trans
   simpa only [entry,args,result,hs,Bool.false_eq_true,ite_false,List.append_assoc,List.append_nil] using h1.trans h2

end RosserDirect.FixedTransform
