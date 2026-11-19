module
public import DirectBinaryAddition
public import DirectTypedBlockMove
@[expose] public section
namespace RosserDirect.TypedNatAddition
open Turing Segment
set_option backward.isDefEq.respectTransparency false
inductive Q where
 | first (q : Grammar.CopyControl TypedBlock.Control) | strip
 | add (q : BinaryAddition.Q) | finish | done | reject
 deriving DecidableEq, Fintype, Inhabited

def machine : Q → Stmt Q
 | .first .done => .goto (fun _ => .strip)
 | .first q => Routine.relocate id Q.first (TypedBlock.moveMachine q)
 | .strip => .pop .input (fun _ x => x)
   (.branch (fun x => x == some .tokenEnd)
    (.pop .output (fun _ x => x) (.branch (fun x => x == some .tokenEnd)
      (.goto (fun _ => .add (.scan false))) (.goto (fun _ => .reject)))) (.goto (fun _ => .reject)))
 | .add .done => .goto (fun _ => .finish)
 | .add q => Routine.relocate id Q.add (BinaryAddition.machine q)
 | .finish => .pop .input (fun _ x => x)
   (.branch (fun x => x == some .frameEnd)
    (.push .output (fun _ => .tokenEnd) (.load (fun _ => none) (.goto (fun _ => .done)))) (.goto (fun _ => .reject)))
 | .done | .reject => .halt

theorem agree_first (q : Grammar.CopyControl TypedBlock.Control) (h : TypedBlock.moveMachine q ≠ .halt) :
 machine (.first q) = Routine.relocate id Q.first (TypedBlock.moveMachine q) := by
 cases q <;> simp_all [machine,TypedBlock.moveMachine,GrammarMove.machine]
theorem agree_add (q : BinaryAddition.Q) (h : BinaryAddition.machine q ≠ .halt) :
 machine (.add q) = Routine.relocate id Q.add (BinaryAddition.machine q) := by
 cases q <;> simp_all [machine,BinaryAddition.machine]

theorem embed_id {L : Type} (labels : L → Q) (q : L) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id labels (config q v a b c) (fun _ => []) = config (labels q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem strip_step (v : Option Symbol) (src dst : List Symbol) :
 TM2.step machine (config .strip v (.tokenEnd :: src) [] (.tokenEnd :: dst)) =
 some (config (.add (.scan false)) (some .tokenEnd) src [] dst) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage]
 funext k; cases k <;> rfl

theorem finish_step (v : Option Symbol) (src dst : List Symbol) :
 TM2.step machine (config .finish v (.frameEnd :: src) [] dst) =
 some (config .done none src [] (.tokenEnd :: dst)) := by
 simp [machine,config,TM2.step,TM2.stepAux,storage]
 funext k; cases k <;> rfl

/-- Typed binary addition consumes m,n and returns n+m, preserving the 2*n ABI. -/
theorem addition (n m : Nat) (v : Option Symbol) (src dst : List Symbol) :
 TM2.Reaches machine
 (config (.first (.scan (.run 0 .start))) v (TypedContext.value (.nat m) ++ TypedContext.value (.nat n) ++ src) [] dst)
 (config .done none src [] (TypedContext.value (.nat (n+m)) ++ dst)) := by
 have h0 := Routine.lift_embedded_run id Function.injective_id Q.first TypedBlock.moveMachine machine agree_first (fun _ => [])
   (TypedBlock.move_block 0 [.nat m] rfl v (TypedContext.value (.nat n) ++ src) dst) (by simp [config])
 simp only [embed_id] at h0
 have l0 : TM2.Reaches machine
   (config (.first .done) none (TypedContext.value (.nat n) ++ src) [] (TypedContext.value (.nat m) ++ dst))
   (config .strip none (TypedContext.value (.nat n) ++ src) [] (TypedContext.value (.nat m) ++ dst)) := Relation.ReflTransGen.single rfl
 have hs := TypedContext.reach_step (strip_step none (tokenBits (2*n) ++ .frameEnd :: src) (tokenBits (2*m) ++ .frameEnd :: dst))
 have h1 := Routine.lift_embedded_run id Function.injective_id Q.add BinaryAddition.machine machine agree_add (fun _ => [])
   (BinaryAddition.addition (2*n) (2*m) (some .tokenEnd) (.frameEnd :: src) (.frameEnd :: dst)) (by simp [config])
 simp only [embed_id] at h1
 have l1 : TM2.Reaches machine
   (config (.add .done) none (.frameEnd :: src) [] (tokenBits (2*n+2*m) ++ .frameEnd :: dst))
   (config .finish none (.frameEnd :: src) [] (tokenBits (2*n+2*m) ++ .frameEnd :: dst)) := Relation.ReflTransGen.single rfl
 have he := TypedContext.reach_step (finish_step none src (tokenBits (2*n+2*m) ++ .frameEnd :: dst))
 have hz : tokenBits 0 = [.tokenEnd] := rfl
 simp only [TM2.Reaches,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,
   TypedContext.value,hz,List.cons_append,List.nil_append,List.singleton_append,List.append_assoc,Nat.mul_add] at h0 l0 hs h1 l1 he ⊢
 exact h0.trans (l0.trans (hs.trans (h1.trans (l1.trans he))))

end RosserDirect.TypedNatAddition
