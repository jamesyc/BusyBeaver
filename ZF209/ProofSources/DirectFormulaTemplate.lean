module
public import DirectFormulaPayloadCopy
@[expose] public section
namespace RosserDirect.FormulaTemplate
open Turing Segment FourStack
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

inductive Cmd where
 | literal (xs : List Symbol) | copy | drop

inductive Q where
 | run (i : Fin 16) | copy (i : Fin 16) (q : FormulaPayloadCopy.Q)
 | drop (i : Fin 16) (q : Grammar.DropControl TypedBlock.Control) | done
 deriving DecidableEq, Fintype, Inhabited

def pushOutput : List Symbol → Stmt4 Q → Stmt4 Q
 | [], s => s
 | x::xs,s => pushOutput xs (.push .output (fun _ => x) s)

def machine (program : List Cmd) : Q → Stmt4 Q
 | .run i => match program[i.val]? with
   | none => .goto (fun _ => .done)
   | some (.literal xs) => pushOutput xs (.load (fun _ => none) (.goto (fun _ => .run (i+1))))
   | some .copy => .goto (fun _ => .copy i .tag0)
   | some .drop => .goto (fun _ => .drop i (.scan (.run 0 .start)))
 | .copy i .done => .load (fun _ => none) (.goto (fun _ => .run (i+1)))
 | .copy i q => Routine.relocate dataRoles (Q.copy i) (FormulaPayloadCopy.machine q)
 | .drop i .done => .load (fun _ => none) (.goto (fun _ => .run (i+1)))
 | .drop i q => Routine.relocate dataRoles (Q.drop i) (TypedBlock.dropMachine q)
 | .done => .halt

theorem agree_copy (program : List Cmd) (i : Fin 16) (q : FormulaPayloadCopy.Q)
 (h : FormulaPayloadCopy.machine q ≠ .halt) :
 machine program (.copy i q) = Routine.relocate dataRoles (Q.copy i) (FormulaPayloadCopy.machine q) := by
 cases q <;> simp_all [machine,FormulaPayloadCopy.machine]
theorem agree_drop (program : List Cmd) (i : Fin 16) (q : Grammar.DropControl TypedBlock.Control)
 (h : TypedBlock.dropMachine q ≠ .halt) :
 machine program (.drop i q) = Routine.relocate dataRoles (Q.drop i) (TypedBlock.dropMachine q) := by
 cases q <;> simp_all [machine,TypedBlock.dropMachine,Grammar.dropMachine]

theorem pushOutput_correct (xs : List Symbol) (s : Stmt4 Q) (v : Option Symbol) (p a b c : List Symbol) :
 TM2.stepAux (pushOutput xs s) v (store4 p a b c) = TM2.stepAux s v (store4 p a b (xs ++ c)) := by
 induction xs generalizing s c with
 | nil => rfl
 | cons x xs ih =>
  rw [pushOutput,ih]
  simp only [TM2.stepAux]
  have he : Function.update (store4 p a b (xs ++ c)) K.output (x::(xs ++ c)) = store4 p a b ((x::xs)++c) := by
   funext k;cases k <;>rfl
  exact congrArg (TM2.stepAux s v) he

theorem literal (program : List Cmd) (i : Fin 16) (xs : List Symbol)
 (hi : program[i.val]? = some (.literal xs)) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches (machine program) (cfg4 (.run i) v p a [] c)
  (cfg4 (.run (i+1)) none p a [] (xs ++ c)) := by
 apply Relation.ReflTransGen.single
 simp [machine,hi,cfg4,TM2.step,pushOutput_correct,TM2.stepAux]

theorem copy (program : List Cmd) (i : Fin 16)
 (hi : program[i.val]? = some .copy) (f : ZFR.Formula)
 (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches (machine program)
  (cfg4 (.run i) v p (TypedContext.value (.formula f) ++ a) [] c)
  (cfg4 (.run (i+1)) none p (TypedContext.value (.formula f) ++ a) []
   (payloadBits (ZFR.TokenVM.emitFormula f) ++ c)) := by
 have h0 : TM2.Reaches (machine program)
  (cfg4 (.run i) v p (TypedContext.value (.formula f) ++ a) [] c)
  (cfg4 (.copy i .tag0) v p (TypedContext.value (.formula f) ++ a) [] c) := by
  apply Relation.ReflTransGen.single
  simp [machine,hi,cfg4,TM2.step,TM2.stepAux]
 have h1 := Routine.lift_embedded_run dataRoles data_injective (Q.copy i)
  FormulaPayloadCopy.machine (machine program) (agree_copy program i) (fun _ => p)
  (FormulaPayloadCopy.copy_formula f v a c) (by simp [config])
 simp only [embed_data] at h1
 have h2 : TM2.Reaches (machine program)
  (cfg4 (.copy i .done) none p (TypedContext.value (.formula f) ++ a) []
   (payloadBits (ZFR.TokenVM.emitFormula f) ++ c))
  (cfg4 (.run (i+1)) none p (TypedContext.value (.formula f) ++ a) []
   (payloadBits (ZFR.TokenVM.emitFormula f) ++ c)) := Relation.ReflTransGen.single rfl
 exact h0.trans (h1.trans h2)

theorem drop (program : List Cmd) (i : Fin 16)
 (hi : program[i.val]? = some .drop) (f : ZFR.Formula)
 (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches (machine program)
  (cfg4 (.run i) v p (TypedContext.value (.formula f) ++ a) [] c)
  (cfg4 (.run (i+1)) none p a [] c) := by
 have h0 : TM2.Reaches (machine program)
  (cfg4 (.run i) v p (TypedContext.value (.formula f) ++ a) [] c)
  (cfg4 (.drop i (.scan (.run 0 .start))) v p (TypedContext.value (.formula f) ++ a) [] c) := by
  apply Relation.ReflTransGen.single
  simp [machine,hi,cfg4,TM2.step,TM2.stepAux]
 obtain ⟨w,hw⟩ := TypedBlock.drop_block 0 [.formula f] rfl v a [] c
 have h1 := Routine.lift_embedded_run dataRoles data_injective (Q.drop i)
  TypedBlock.dropMachine (machine program) (agree_drop program i) (fun _ => p) hw (by simp [config])
 simp only [embed_data,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil] at h1
 have h2 : TM2.Reaches (machine program)
  (cfg4 (.drop i .done) w p a [] c)
  (cfg4 (.run (i+1)) none p a [] c) := Relation.ReflTransGen.single rfl
 exact h0.trans (h1.trans h2)

theorem finish (program : List Cmd) (i : Fin 16)
 (hi : program[i.val]? = none) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches (machine program) (cfg4 (.run i) v p a [] c) (cfg4 .done v p a [] c) := by
 apply Relation.ReflTransGen.single
 simp [machine,hi,cfg4,TM2.step,TM2.stepAux]

end RosserDirect.FormulaTemplate
