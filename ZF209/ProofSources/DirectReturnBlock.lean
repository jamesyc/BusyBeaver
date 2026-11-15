module
public import DirectShiftIndex
public import DirectNatUnframe
@[expose] public section
namespace RosserDirect.ReturnBlock
open Turing Segment
set_option backward.isDefEq.respectTransparency false

inductive Q (L : Type) where
 | first (q : L) | back (q : Grammar.CopyControl TypedBlock.Control) | done
 deriving DecidableEq, Fintype, Inhabited

variable {L : Type} [DecidableEq L] (M : L → Stmt L) (finish : L) (n : Fin 6)

def machine : Q L → Stmt (Q L)
 | .first q => if q = finish then .goto (fun _ => .back (.scan (.run n .start)))
   else Routine.relocate id Q.first (M q)
 | .back .done => .goto (fun _ => .done)
 | .back q => Routine.relocate SelectSecond.swap Q.back (TypedBlock.moveMachine q)
 | .done => .halt

theorem agree_first (hf : M finish = .halt) (q : L) (h : M q ≠ .halt) :
 machine M finish n (.first q) = Routine.relocate id Q.first (M q) := by
 have hn : q ≠ finish := by intro he; subst q; exact h hf
 simp [machine,hn]
theorem agree_back (q : Grammar.CopyControl TypedBlock.Control) (h : TypedBlock.moveMachine q ≠ .halt) :
 machine M finish n (.back q) = Routine.relocate SelectSecond.swap Q.back (TypedBlock.moveMachine q) := by
 cases q <;> simp_all [machine,TypedBlock.moveMachine,GrammarMove.machine]

theorem embed_first (q : L) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id (Q.first (L := L)) (config q v a b c) (fun _ => []) = config (.first q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem embed_back (q : Grammar.CopyControl TypedBlock.Control) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed SelectSecond.swap (Q.back (L := L)) (config q v a b c) (fun _ => []) = config (.back q) v c b a := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

/-- Move a verified subroutine result back above its surviving input. Used to
update the traversal's depth-job stack without touching its output accumulator. -/
theorem run (entry : L) (hf : M finish = .halt) (ws : List ZFR.TokenVM.Value) (len : ws.length = n.val+1)
 (v : Option Symbol) (input rest out : List Symbol)
 (h : TM2.Reaches M (config entry v input [] out)
    (config finish none rest [] (TypedContext.stack ws ++ out))) :
 TM2.Reaches (machine M finish n) (config (.first entry) v input [] out)
   (config .done none (TypedContext.stack ws ++ rest) [] out) := by
 have h0 := Routine.lift_embedded_run id Function.injective_id Q.first
   M (machine M finish n) (agree_first M finish n hf) (fun _ => []) h (by simp [config])
 simp only [embed_first] at h0
 have h1 : TM2.Reaches (machine M finish n)
   (config (.first finish) none rest [] (TypedContext.stack ws ++ out))
   (config (.back (.scan (.run n .start))) none rest [] (TypedContext.stack ws ++ out)) := by
   apply Relation.ReflTransGen.single
   simp [machine,config,TM2.step,TM2.stepAux]
 have h2 := Routine.lift_embedded_run SelectSecond.swap SelectSecond.swap_injective Q.back
   TypedBlock.moveMachine (machine M finish n) (agree_back M finish n) (fun _ => [])
   (TypedBlock.move_block n ws len none out rest) (by simp [config])
 simp only [embed_back,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil] at h2
 have h3 : TM2.Reaches (machine M finish n)
   (config (.back .done) none (TypedContext.stack ws ++ rest) [] out)
   (config .done none (TypedContext.stack ws ++ rest) [] out) := Relation.ReflTransGen.single rfl
 exact h0.trans (h1.trans (h2.trans h3))

def duplicatePairMachine := machine TypedBlock.machine .done 1

theorem duplicate_pair (x y : ZFR.TokenVM.Value) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches duplicatePairMachine
  (config (.first (.scan (.run 1 .start))) v (TypedContext.value x ++ TypedContext.value y ++ src) [] dst)
  (config .done none (TypedContext.value x ++ TypedContext.value y ++ TypedContext.value x ++ TypedContext.value y ++ src) [] dst) := by
 have h := TypedBlock.copy_block 1 [x,y] rfl v src dst
 have r := run TypedBlock.machine .done 1 _ rfl [x,y] rfl v _ _ dst h
 simpa [duplicatePairMachine,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_assoc] using r

end RosserDirect.ReturnBlock
