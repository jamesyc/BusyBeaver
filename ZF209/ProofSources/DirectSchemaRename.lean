module
public import DirectFixedTransform
@[expose] public section
namespace RosserDirect.SchemaRenameMachine
open Turing Segment FourStack
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

inductive Mode where
 | separation | replacementA | replacementB | replacementC
 deriving DecidableEq, Fintype, Inhabited

def actions : Mode → List FixedTransform.Action
 | .separation => [.shift1,.shift1]
 | .replacementA => [.shift2,.shift1,.subst2]
 | .replacementB => [.shift2,.shift2,.shift1,.subst3,.subst0]
 | .replacementC => [.shift2,.shift2]

def action (m : Mode) (i : Fin 6) := (actions m)[i.val]?
def bump (i : Fin 6) : Fin 6 := ⟨(i.val+1)%6,Nat.mod_lt _ (by decide)⟩

def result : Mode → ZFR.Formula → ZFR.Formula
 | .separation,f => ZFR.rename ZFR.sepIndex f
 | .replacementA,f => ZFR.rename ZFR.repAIndex f
 | .replacementB,f => ZFR.rename ZFR.repBIndex f
 | .replacementC,f => ZFR.rename ZFR.repCIndex f

inductive Q where
 | start (i : Fin 6) | run (i : Fin 6) (q : FixedTransform.Q)
 | back (i : Fin 6) (q : Label) | finish (q : Label) | done
 deriving DecidableEq, Fintype, Inhabited

def machine (m : Mode) : Q → Stmt4 Q
 | .start i => .goto (fun _ => if (action m i).isSome then .run i (.save .scan) else .finish .scan)
 | .run i .done => .goto (fun _ => .back i .scan)
 | .run i q => Routine.relocate id (Q.run i) (FixedTransform.machine ((action m i).getD .shift1) q)
 | .back i .done => .goto (fun _ => .start (bump i))
 | .back i q => Routine.relocate outputRoles (Q.back i) (RosserDirect.machine q)
 | .finish .done => .goto (fun _ => .done)
 | .finish q => Routine.relocate dataRoles Q.finish (RosserDirect.machine q)
 | .done => .halt

theorem agree_run (m : Mode) (i : Fin 6) (q : FixedTransform.Q)
 (h : FixedTransform.machine ((action m i).getD .shift1) q ≠ .halt) :
 machine m (.run i q) = Routine.relocate id (Q.run i) (FixedTransform.machine ((action m i).getD .shift1) q) := by
 cases q <;> simp_all [machine,FixedTransform.machine]
theorem agree_back (m : Mode) (i : Fin 6) (q : Label) (h : RosserDirect.machine q ≠ .halt) :
 machine m (.back i q) = Routine.relocate outputRoles (Q.back i) (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]
theorem agree_finish (m : Mode) (q : Label) (h : RosserDirect.machine q ≠ .halt) :
 machine m (.finish q) = Routine.relocate dataRoles Q.finish (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]

theorem execute_one (m : Mode) (i : Fin 6) (op : FixedTransform.Action) (hi : action m i = some op)
 (f : ZFR.Formula) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches (machine m)
  (cfg4 (.start i) v p (TypedContext.value (.formula f) ++ a) [] c)
  (cfg4 (.start (bump i)) none p (TypedContext.value (.formula (FixedTransform.result op f)) ++ a) [] c) := by
 have h0 : TM2.Reaches (machine m)
  (cfg4 (.start i) v p (TypedContext.value (.formula f) ++ a) [] c)
  (cfg4 (.run i (.save .scan)) v p (TypedContext.value (.formula f) ++ a) [] c) := by
  apply Relation.ReflTransGen.single
  simp [machine,hi,cfg4,TM2.step,TM2.stepAux]
 have h1 := FourStack.relabel_run (Q.run i) (FixedTransform.machine ((action m i).getD .shift1)) (machine m) (agree_run m i)
  _ _ _ _ _ _ _ _ _ _ _ _ (FixedTransform.execute ((action m i).getD .shift1) f v p a c)
 simp only [hi,Option.getD_some] at h1
 have h2 : TM2.Reaches (machine m)
  (cfg4 (.run i .done) none p a [] (TypedContext.value (.formula (FixedTransform.result op f)) ++ c))
  (cfg4 (.back i .scan) none p a [] (TypedContext.value (.formula (FixedTransform.result op f)) ++ c)) := Relation.ReflTransGen.single rfl
 have h3 := Routine.lift_embedded_run outputRoles output_injective (Q.back i)
  RosserDirect.machine (machine m) (agree_back m i) (fun _ => p)
  (AllIntroPremise.move_formula (FixedTransform.result op f) none c a) (by simp [config])
 simp only [embed_output] at h3
 have h4 : TM2.Reaches (machine m)
  (cfg4 (.back i .done) none p (TypedContext.value (.formula (FixedTransform.result op f)) ++ a) [] c)
  (cfg4 (.start (bump i)) none p (TypedContext.value (.formula (FixedTransform.result op f)) ++ a) [] c) := Relation.ReflTransGen.single rfl
 exact h0.trans (h1.trans (h2.trans (h3.trans h4)))

theorem finish (m : Mode) (i : Fin 6) (hi : action m i = none)
 (f : ZFR.Formula) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches (machine m)
  (cfg4 (.start i) v p (TypedContext.value (.formula f) ++ a) [] c)
  (cfg4 .done none p a [] (TypedContext.value (.formula f) ++ c)) := by
 have h0 : TM2.Reaches (machine m)
  (cfg4 (.start i) v p (TypedContext.value (.formula f) ++ a) [] c)
  (cfg4 (.finish .scan) v p (TypedContext.value (.formula f) ++ a) [] c) := by
  apply Relation.ReflTransGen.single
  simp [machine,hi,cfg4,TM2.step,TM2.stepAux]
 have h1 := Routine.lift_embedded_run dataRoles data_injective Q.finish
  RosserDirect.machine (machine m) (agree_finish m) (fun _ => p)
  (AllIntroPremise.move_formula f v a c) (by simp [config])
 simp only [embed_data] at h1
 have h2 : TM2.Reaches (machine m)
  (cfg4 (.finish .done) none p a [] (TypedContext.value (.formula f) ++ c))
  (cfg4 .done none p a [] (TypedContext.value (.formula f) ++ c)) := Relation.ReflTransGen.single rfl
 exact h0.trans (h1.trans h2)

theorem execute (m : Mode) (f : ZFR.Formula) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches (machine m)
  (cfg4 (.start 0) v p (TypedContext.value (.formula f) ++ a) [] c)
  (cfg4 .done none p a [] (TypedContext.value (.formula (result m f)) ++ c)) := by
 cases m with
 | separation =>
  have h0 := execute_one .separation 0 .shift1 rfl f v p a c
  have h1 := execute_one .separation 1 .shift1 rfl (FixedTransform.result .shift1 (f)) none p a c
  have h2 := finish .separation 2 rfl (FixedTransform.result .shift1 (FixedTransform.result .shift1 (f))) none p a c
  simpa only [TM2.Reaches,bump,FixedTransform.result,FixedTransform.isShift,FixedTransform.argument,
   ite_true,result,SchemaRename.separation] using h0.trans (h1.trans h2)
 | replacementC =>
  have h0 := execute_one .replacementC 0 .shift2 rfl f v p a c
  have h1 := execute_one .replacementC 1 .shift2 rfl (FixedTransform.result .shift2 (f)) none p a c
  have h2 := finish .replacementC 2 rfl (FixedTransform.result .shift2 (FixedTransform.result .shift2 (f))) none p a c
  simpa only [TM2.Reaches,bump,FixedTransform.result,FixedTransform.isShift,FixedTransform.argument,
   ite_true,result,SchemaRename.replacementC] using h0.trans (h1.trans h2)
 | replacementA =>
  have h0 := execute_one .replacementA 0 .shift2 rfl f v p a c
  have h1 := execute_one .replacementA 1 .shift1 rfl (FixedTransform.result .shift2 (f)) none p a c
  have h2 := execute_one .replacementA 2 .subst2 rfl (FixedTransform.result .shift1 (FixedTransform.result .shift2 (f))) none p a c
  have h3 := finish .replacementA 3 rfl (FixedTransform.result .subst2 (FixedTransform.result .shift1 (FixedTransform.result .shift2 (f)))) none p a c
  simpa only [TM2.Reaches,bump,FixedTransform.result,FixedTransform.isShift,FixedTransform.argument,
   Bool.false_eq_true,ite_false,ite_true,result,SchemaRename.replacementA] using h0.trans (h1.trans (h2.trans h3))
 | replacementB =>
  have h0 := execute_one .replacementB 0 .shift2 rfl f v p a c
  have h1 := execute_one .replacementB 1 .shift2 rfl (FixedTransform.result .shift2 (f)) none p a c
  have h2 := execute_one .replacementB 2 .shift1 rfl (FixedTransform.result .shift2 (FixedTransform.result .shift2 (f))) none p a c
  have h3 := execute_one .replacementB 3 .subst3 rfl (FixedTransform.result .shift1 (FixedTransform.result .shift2 (FixedTransform.result .shift2 (f)))) none p a c
  have h4 := execute_one .replacementB 4 .subst0 rfl (FixedTransform.result .subst3 (FixedTransform.result .shift1 (FixedTransform.result .shift2 (FixedTransform.result .shift2 (f))))) none p a c
  have h5 := finish .replacementB 5 rfl (FixedTransform.result .subst0 (FixedTransform.result .subst3 (FixedTransform.result .shift1 (FixedTransform.result .shift2 (FixedTransform.result .shift2 (f)))))) none p a c
  simpa only [TM2.Reaches,bump,FixedTransform.result,FixedTransform.isShift,FixedTransform.argument,
   Bool.false_eq_true,ite_false,ite_true,result,SchemaRename.replacementB] using h0.trans (h1.trans (h2.trans (h3.trans (h4.trans h5))))

end RosserDirect.SchemaRenameMachine
