module
public import DirectScopeCheck
@[expose] public section
namespace RosserDirect.FixedAxiomCheck
open Turing Segment FourStack
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

def witness (i : Fin 11) : ZFR.ExecutableZF.AxiomWitness :=
 match i.val with
 | 0 => .refl | 1 => .sym | 2 => .trans | 3 => .eqElem | 4 => .ext
 | 5 => .empty | 6 => .pair | 7 => .union | 8 => .power | 9 => .omega | _ => .foundation

def formula (i : Fin 11) : ZFR.Formula :=
 match i.val with
 | 0 => ZFR.fixedRefl | 1 => ZFR.fixedSym | 2 => ZFR.fixedTrans | 3 => ZFR.fixedEqElem
 | 4 => ZFR.fixedExt | 5 => ZFR.fixedEmpty | 6 => ZFR.fixedPair | 7 => ZFR.fixedUnion
 | 8 => ZFR.fixedPower | 9 => ZFR.fixedOmega | _ => ZFR.fixedFoundation

theorem formula_spec (i : Fin 11) : ZFR.ExecutableZF.axiomFormula (witness i) = some (formula i) := by
 have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 := by omega
 rcases hi with h | h | h | h | h | h | h | h | h | h | h <;> simp [witness,formula,h,ZFR.ExecutableZF.axiomFormula,ZFR.ExecutableZF.checkAxiom]

inductive Q where
 | dispatch (q : OpcodeDispatch.Control) | emit (i : Fin 11)
 | compare (i : Fin 11) (q : RosserDirectEquality.Label)
 | accept (i : Fin 11) | reject
 deriving DecidableEq, Fintype, Inhabited

def pushOutput : List Symbol → Stmt4 Q → Stmt4 Q
 | [], k => k
 | x :: xs, k => pushOutput xs (.push .output (fun _ => x) k)

def select (op : Fin 42) : Q :=
 if h : 27 ≤ op.val ∧ op.val < 38 then .emit ⟨op.val-27,by omega⟩ else .reject

def machine : Q → Stmt4 Q
 | .dispatch (.opcode op) => .goto (fun _ => select op)
 | .dispatch q => Routine.relocate readRoles Q.dispatch (OpcodeDispatch.machine q)
 | .emit i => pushOutput (TypedContext.value (.formula (formula i))) (.goto (fun _ => .compare i .scan))
 | .compare i .equal => .goto (fun _ => .accept i)
 | .compare _ .different => .goto (fun _ => .reject)
 | .compare i q => Routine.relocate dataRoles (Q.compare i) (RosserDirectEquality.machine q)
 | .accept _ | .reject => .halt

theorem agree_dispatch (q : OpcodeDispatch.Control) (h : OpcodeDispatch.machine q ≠ .halt) :
 machine (.dispatch q) = Routine.relocate readRoles Q.dispatch (OpcodeDispatch.machine q) := by
 cases q <;> simp_all [machine,OpcodeDispatch.machine,OpcodeDispatch.active]

theorem agree_compare (i : Fin 11) (q : RosserDirectEquality.Label) (h : RosserDirectEquality.machine q ≠ .halt) :
 machine (.compare i q) = Routine.relocate dataRoles (Q.compare i) (RosserDirectEquality.machine q) := by
 cases q <;> simp_all [machine,RosserDirectEquality.machine]

theorem pushOutput_correct (xs : List Symbol) (k : Stmt4 Q) (v : Option Symbol) (p a s c : List Symbol) :
 TM2.stepAux (pushOutput xs k) v (store4 p a s c) = TM2.stepAux k v (store4 p a s (xs ++ c)) := by
 induction xs generalizing k c with
 | nil => rfl
 | cons x xs ih =>
  rw [pushOutput,ih]
  simp only [TM2.stepAux]
  have he : Function.update (store4 p a s (xs ++ c)) K.output (x :: (xs ++ c)) = store4 p a s ((x::xs)++c) := by
   funext j; cases j <;> rfl
  exact congrArg (TM2.stepAux k v) he

theorem emit (i : Fin 11) (v : Option Symbol) (p a s c : List Symbol) :
 TM2.step machine (cfg4 (.emit i) v p a s c) =
 some (cfg4 (.compare i .scan) v p a s (TypedContext.value (.formula (formula i)) ++ c)) := by
 simp [machine,cfg4,TM2.step,pushOutput_correct,TM2.stepAux]

theorem dispatch (i : Fin 11) (v : Option Symbol) (p a c : List Symbol) :
 ∃ w, TM2.Reaches machine
  (cfg4 (.dispatch .start) v (tokenBits (2*(27+i.val)+1) ++ p) a [] c)
  (cfg4 (.emit i) w p a [] c) := by
 obtain ⟨w,hw⟩ := OpcodeDispatch.dispatch_opcode ⟨27+i.val,by omega⟩ v p [] a
 have h0 := Routine.lift_embedded_run readRoles read_injective Q.dispatch
  OpcodeDispatch.machine machine agree_dispatch (fun _ => c) hw (by simp [config])
 simp only [embed_read] at h0
 have hi : select ⟨27+i.val,by omega⟩ = .emit i := by
  simp [select,show 27+i.val<38 by omega,show 27≤27+i.val by omega]
 have h1 : TM2.Reaches machine
  (cfg4 (.dispatch (.opcode ⟨27+i.val,by omega⟩)) w p a [] c)
  (cfg4 (.emit i) w p a [] c) := by
  apply Relation.ReflTransGen.single
  simp [machine,hi,cfg4,TM2.step,TM2.stepAux]
 exact ⟨w,h0.trans h1⟩

theorem embed_compare (i : Fin 11) (q : RosserDirectEquality.Label) (v : Option Symbol) (p a s c : List Symbol) :
 Routine.embed dataRoles (Q.compare i) (RosserDirectEquality.cfg q v a s c) (fun _ => p) =
 cfg4 (.compare i q) v p a s c := by
 unfold Routine.embed RosserDirectEquality.cfg cfg4
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem accept (i : Fin 11) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches machine
  (cfg4 (.dispatch .start) v (tokenBits (2*(27+i.val)+1) ++ p)
   (TypedContext.value (.formula (formula i)) ++ a) [] c)
  (cfg4 (.accept i) (some .frameEnd) p a [] c) := by
 obtain ⟨w,h0⟩ := dispatch i v p (TypedContext.value (.formula (formula i)) ++ a) c
 have h1 : TM2.Reaches machine _ _ := Relation.ReflTransGen.single
  (emit i w p (TypedContext.value (.formula (formula i)) ++ a) [] c)
 have h2 := Routine.lift_embedded_run dataRoles data_injective (Q.compare i)
  RosserDirectEquality.machine machine (agree_compare i) (fun _ => p)
  (RosserDirectEquality.equal_frames (ScopeCheck.payload (formula i)) (payloadBits_no_end _) w a [] c)
  (by simp [RosserDirectEquality.cfg])
 simp only [embed_compare] at h2
 have h3 : TM2.Reaches machine
  (cfg4 (.compare i .equal) (some .frameEnd) p a [] c)
  (cfg4 (.accept i) (some .frameEnd) p a [] c) := Relation.ReflTransGen.single rfl
 apply h0.trans (h1.trans ?_)
 simpa only [ScopeCheck.value_formula,List.append_assoc,List.cons_append,List.nil_append] using h2.trans h3

theorem reject (i : Fin 11) (f : ZFR.Formula) (hf : f ≠ formula i)
 (v : Option Symbol) (p a c : List Symbol) :
 ∃ w a' c', TM2.Reaches machine
  (cfg4 (.dispatch .start) v (tokenBits (2*(27+i.val)+1) ++ p)
   (TypedContext.value (.formula f) ++ a) [] c)
  (cfg4 .reject w p a' [] c') := by
 have neq : ScopeCheck.payload f ≠ ScopeCheck.payload (formula i) := by
  intro h
  exact hf (emitFormula_injective (List.cons.inj (payloadBits_injective h)).2)
 obtain ⟨w,h0⟩ := dispatch i v p (TypedContext.value (.formula f) ++ a) c
 have h1 : TM2.Reaches machine _ _ := Relation.ReflTransGen.single
  (emit i w p (TypedContext.value (.formula f) ++ a) [] c)
 obtain ⟨w',a',c',hr⟩ := RosserDirectEquality.unequal_frames
  (ScopeCheck.payload f) (ScopeCheck.payload (formula i)) (payloadBits_no_end _) (payloadBits_no_end _) neq w a [] c
 have h2 := Routine.lift_embedded_run dataRoles data_injective (Q.compare i)
  RosserDirectEquality.machine machine (agree_compare i) (fun _ => p) hr (by simp [RosserDirectEquality.cfg])
 simp only [embed_compare] at h2
 have h3 : TM2.Reaches machine (cfg4 (.compare i .different) w' p a' [] c')
  (cfg4 .reject w' p a' [] c') := Relation.ReflTransGen.single rfl
 refine ⟨w',a',c',h0.trans (h1.trans ?_)⟩
 simpa only [ScopeCheck.value_formula,List.append_assoc,List.cons_append,List.nil_append] using h2.trans h3

end RosserDirect.FixedAxiomCheck
