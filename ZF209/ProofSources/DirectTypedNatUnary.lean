module
public import DirectBinaryPredecessor
public import DirectOperandSwap
@[expose] public section
namespace RosserDirect.TypedNatUnary
open Turing Segment
set_option backward.isDefEq.respectTransparency false

inductive Control (Q : Type) where
 | start | first (q : Q) | second (q : Q) | move (q : Label) | done | reject
 deriving DecidableEq, Fintype, Inhabited

variable {Q : Type} [DecidableEq Q]
variable (M : Q → Stmt Q) (entry finish : Q)

/-- Two binary steps implement successor or predecessor in the 2*n natural ABI. The intermediate
result is returned through the opposite stack. No unary expansion occurs. -/
def machine : Control Q → Stmt (Control Q)
 | .start => TypedContext.expect .tokenEnd (.first entry) .reject
 | .first q => if q = finish then .goto (fun _ => .second entry)
   else Routine.relocate id Control.first (M q)
 | .second q => if q = finish then .goto (fun _ => .move .scan)
   else Routine.relocate SelectSecond.swap Control.second (M q)
 | .move .done => .push .output (fun _ => .tokenEnd) (.goto (fun _ => .done))
 | .move q => Routine.relocate id Control.move (RosserDirect.machine q)
 | .done | .reject => .halt

theorem agree_first (hf : M finish = .halt) (q : Q) (h : M q ≠ .halt) :
 machine M entry finish (.first q) = Routine.relocate id Control.first (M q) := by
 have hn : q ≠ finish := by intro he; subst q; exact h hf
 simp [machine,hn]
theorem agree_second (hf : M finish = .halt) (q : Q) (h : M q ≠ .halt) :
 machine M entry finish (.second q) = Routine.relocate SelectSecond.swap Control.second (M q) := by
 have hn : q ≠ finish := by intro he; subst q; exact h hf
 simp [machine,hn]
theorem agree_move (q : Label) (h : RosserDirect.machine q ≠ .halt) :
 machine M entry finish (.move q) = Routine.relocate id Control.move (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]

theorem embed_first (q : Q) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id (Control.first (Q := Q)) (config q v a b c) (fun _ => []) = config (.first q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem embed_second (q : Q) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed SelectSecond.swap (Control.second (Q := Q)) (config q v a b c) (fun _ => []) = config (.second q) v c b a := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem embed_move (q : Label) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id (Control.move (Q := Q)) (config q v a b c) (fun _ => []) = config (.move q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

/-- Generic ABI wrapper, with exact preservation of arbitrary surrounding data. -/
theorem run_twice (f g : Nat → Nat) (hf : M finish = .halt)
    (run : ∀ n v src dst, TM2.Reaches M (config entry v (tokenBits n ++ src) [] dst)
      (config finish none src [] (tokenBits (f n) ++ dst)))
    (exactValue : ∀ n, f (f (2*n)) = 2*g n)
    (n : Nat) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches (machine M entry finish)
  (config .start v (TypedContext.value (.nat n) ++ src) [] dst)
  (config .done none src [] (TypedContext.value (.nat (g n)) ++ dst)) := by
 have h0 : TM2.Reaches (machine M entry finish)
   (config .start v (.tokenEnd :: (tokenBits (2*n) ++ .frameEnd :: src)) [] dst)
   (config (.first entry) (some .tokenEnd) (tokenBits (2*n) ++ .frameEnd :: src) [] dst) :=
   Relation.ReflTransGen.single (TypedContext.expect_step (machine M entry finish) .start (.first entry) .reject .tokenEnd rfl v _ [] dst)
 have h1 := Routine.lift_embedded_run id Function.injective_id Control.first
   M (machine M entry finish) (agree_first M entry finish hf) (fun _ => [])
   (run (2*n) (some .tokenEnd) (.frameEnd :: src) dst) (by simp [config])
 simp only [embed_first] at h1
 have h12 : TM2.Reaches (machine M entry finish)
   (config (.first finish) none (.frameEnd :: src) [] (tokenBits (f (2*n)) ++ dst))
   (config (.second entry) none (.frameEnd :: src) [] (tokenBits (f (2*n)) ++ dst)) := by
   apply Relation.ReflTransGen.single
   simp [machine,config,TM2.step,TM2.stepAux]
 have h2 := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective Control.second
   M (machine M entry finish) (agree_second M entry finish hf) (fun _ => [])
   (run (f (2*n)) none dst (.frameEnd :: src)) (by simp [config])
 simp only [embed_second] at h2
 have h23 : TM2.Reaches (machine M entry finish)
   (config (.second finish) none (tokenBits (f (f (2*n))) ++ .frameEnd :: src) [] dst)
   (config (.move .scan) none (tokenBits (f (f (2*n))) ++ .frameEnd :: src) [] dst) := by
   apply Relation.ReflTransGen.single
   simp [machine,config,TM2.step,TM2.stepAux]
 have h3 := Routine.lift_embedded_run id Function.injective_id Control.move
   RosserDirect.machine (machine M entry finish) (agree_move M entry finish) (fun _ => [])
   (RosserDirect.move_frame (tokenBits (f (f (2*n)))) (tokenBits_no_end _) none src dst) (by simp [cfg])
 change TM2.Reaches _ (Routine.embed _ _ (config Label.scan _ _ _ _) _) (Routine.embed _ _ (config Label.done _ _ _ _) _) at h3
 simp only [embed_move] at h3
 have h4 : TM2.Reaches (machine M entry finish)
   (config (.move .done) none src [] (tokenBits (f (f (2*n))) ++ .frameEnd :: dst))
   (config .done none src [] (.tokenEnd :: (tokenBits (f (f (2*n))) ++ .frameEnd :: dst))) := by
   apply Relation.ReflTransGen.single
   simp [machine,config,TM2.step,TM2.stepAux,storage,Function.update]
   funext k; cases k <;> rfl
 have h := h0.trans (h1.trans (h12.trans (h2.trans (h23.trans (h3.trans h4)))))
 simpa [TM2.Reaches,TypedContext.value,tokenBits,Nat.zero_bits,List.append_assoc,exactValue] using h

theorem successor (n : Nat) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches (machine BinarySuccessor.machine .carry .done)
  (config .start v (TypedContext.value (.nat n) ++ src) [] dst)
  (config .done none src [] (TypedContext.value (.nat (n+1)) ++ dst)) :=
 run_twice _ _ _ (fun n => n+1) (fun n => n+1) rfl BinarySuccessor.successor (by intro n; omega) n v src dst

theorem predecessor (n : Nat) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches (machine BinaryPredecessor.machine .borrow .done)
  (config .start v (TypedContext.value (.nat n) ++ src) [] dst)
  (config .done none src [] (TypedContext.value (.nat (n-1)) ++ dst)) :=
 run_twice _ _ _ (fun n => n-1) (fun n => n-1) rfl BinaryPredecessor.predecessor (by intro n; omega) n v src dst

end RosserDirect.TypedNatUnary
