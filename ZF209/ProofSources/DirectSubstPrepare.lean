module
public import DirectShiftTraversal
public import DirectReturnBlock
@[expose] public section
namespace RosserDirect.SubstPrepare
open Turing Segment FourStack
set_option backward.isDefEq.respectTransparency false

inductive Q where
 | reverse (q : ReverseTokens.Q) | save (q : Label) | marker | restore (q : Label) | seed | done
 deriving DecidableEq, Fintype, Inhabited

def machine : Q → Stmt4 Q
 | .reverse .done => .goto (fun _ => .save .scan)
 | .reverse q => Routine.relocate prepareRoles Q.reverse (ReverseTokens.machine q)
 | .save .done => .goto (fun _ => .marker)
 | .save q => Routine.relocate dataRoles Q.save (RosserDirect.machine q)
 | .marker => .push .data (fun _ => .frameEnd) (.goto (fun _ => .restore .scan))
 | .restore .done => .goto (fun _ => .seed)
 | .restore q => Routine.relocate outputRoles Q.restore (RosserDirect.machine q)
 | .seed => .push .data (fun _ => .frameEnd)
   (.push .data (fun _ => .tokenEnd) (.push .data (fun _ => .tokenEnd)
    (.push .output (fun _ => .frameEnd) (.goto (fun _ => .done)))))
 | .done => .halt

theorem agree_reverse (q : ReverseTokens.Q) (h : ReverseTokens.machine q ≠ .halt) :
 machine (.reverse q) = Routine.relocate prepareRoles Q.reverse (ReverseTokens.machine q) := by
 cases q <;> simp_all [machine,ReverseTokens.machine]
theorem agree_save (q : Label) (h : RosserDirect.machine q ≠ .halt) :
 machine (.save q) = Routine.relocate dataRoles Q.save (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]
theorem agree_restore (q : Label) (h : RosserDirect.machine q ≠ .halt) :
 machine (.restore q) = Routine.relocate outputRoles Q.restore (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]

theorem move_nat (t : Nat) (v : Option Symbol) (a c : List Symbol) :
 TM2.Reaches RosserDirect.machine (config Label.scan v (TypedContext.value (.nat t) ++ a) [] c)
  (config Label.done none a [] (TypedContext.value (.nat t) ++ c)) := by
 have h := RosserDirect.move_frame (tokenBits 0 ++ tokenBits (2*t))
   (by intro x hx; simp only [List.mem_append] at hx; rcases hx with hx | hx <;> exact tokenBits_no_end _ x hx) v a c
 simpa [TM2.Reaches,cfg,config,TypedContext.value,List.append_assoc] using h

/-- Prepare an arbitrary substitution argument alongside a binary depth-zero
job. Original persistent formula/natural ABI and all surrounding tails remain
unchanged. This is a finite staging operation, not the substitution itself. -/
theorem prepare (f : ZFR.Formula) (t : Nat) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches machine
  (cfg4 (.reverse .formulaTag) v p (TypedContext.value (.formula f) ++ TypedContext.value (.nat t) ++ a) [] c)
  (cfg4 .done none (ShiftTraversal.rev f ++ .frameEnd :: p)
    (TypedContext.value (.nat 0) ++ TypedContext.value (.nat t) ++ .frameEnd :: a) [] (.frameEnd :: c)) := by
 have h0 := Routine.lift_embedded_run prepareRoles prepare_injective Q.reverse
   ReverseTokens.machine machine agree_reverse (fun _ => c)
   (ReverseTokens.reverse_formula f v (TypedContext.value (.nat t) ++ a) p) (by simp [config])
 simp only [embed_prepare] at h0
 have h1 : TM2.Reaches machine
   (cfg4 (.reverse .done) none (ShiftTraversal.rev f ++ .frameEnd :: p) (TypedContext.value (.nat t) ++ a) [] c)
   (cfg4 (.save .scan) none (ShiftTraversal.rev f ++ .frameEnd :: p) (TypedContext.value (.nat t) ++ a) [] c) := Relation.ReflTransGen.single rfl
 have h2 := Routine.lift_embedded_run dataRoles data_injective Q.save
   RosserDirect.machine machine agree_save (fun _ => ShiftTraversal.rev f ++ .frameEnd :: p)
   (move_nat t none a c) (by simp [config])
 simp only [embed_data] at h2
 have h3 : TM2.Reaches machine
   (cfg4 (.save .done) none (ShiftTraversal.rev f ++ .frameEnd :: p) a [] (TypedContext.value (.nat t) ++ c))
   (cfg4 .marker none (ShiftTraversal.rev f ++ .frameEnd :: p) a [] (TypedContext.value (.nat t) ++ c)) := Relation.ReflTransGen.single rfl
 have h4 : TM2.Reaches machine
   (cfg4 .marker none (ShiftTraversal.rev f ++ .frameEnd :: p) a [] (TypedContext.value (.nat t) ++ c))
   (cfg4 (.restore .scan) none (ShiftTraversal.rev f ++ .frameEnd :: p) (.frameEnd :: a) [] (TypedContext.value (.nat t) ++ c)) := by
   apply Relation.ReflTransGen.single
   simp [machine,cfg4,TM2.step,TM2.stepAux,store4,Function.update]
   funext k; cases k <;> rfl
 have h5 := Routine.lift_embedded_run outputRoles output_injective Q.restore
   RosserDirect.machine machine agree_restore (fun _ => ShiftTraversal.rev f ++ .frameEnd :: p)
   (move_nat t none c (.frameEnd :: a)) (by simp [config])
 simp only [embed_output] at h5
 have h6 : TM2.Reaches machine
   (cfg4 (.restore .done) none (ShiftTraversal.rev f ++ .frameEnd :: p) (TypedContext.value (.nat t) ++ .frameEnd :: a) [] c)
   (cfg4 .seed none (ShiftTraversal.rev f ++ .frameEnd :: p) (TypedContext.value (.nat t) ++ .frameEnd :: a) [] c) := Relation.ReflTransGen.single rfl
 have h7 : TM2.Reaches machine
   (cfg4 .seed none (ShiftTraversal.rev f ++ .frameEnd :: p) (TypedContext.value (.nat t) ++ .frameEnd :: a) [] c)
   (cfg4 .done none (ShiftTraversal.rev f ++ .frameEnd :: p)
    (TypedContext.value (.nat 0) ++ TypedContext.value (.nat t) ++ .frameEnd :: a) [] (.frameEnd :: c)) := by
   apply Relation.ReflTransGen.single
   simp [machine,cfg4,TM2.step,TM2.stepAux,store4,Function.update,TypedContext.value,tokenBits,Nat.zero_bits,List.append_assoc]
   funext k; cases k <;> rfl
 simp only [TM2.Reaches,List.append_assoc] at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
 exact h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7))))))

end RosserDirect.SubstPrepare
