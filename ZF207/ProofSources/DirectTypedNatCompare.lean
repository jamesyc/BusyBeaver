module
public import DirectBinaryCompare
@[expose] public section
namespace RosserDirect.TypedNatCompare
open Turing Segment
set_option backward.isDefEq.respectTransparency false

inductive Q where
 | leftTag | rightTag | core (q : BinaryCompare.Q)
 | leftFrame (o : Ordering) | rightFrame (o : Ordering) | done (o : Ordering) | reject
 deriving DecidableEq, Fintype, Inhabited

def expectAt (k : Stack) (x : Symbol) (next : Q) : Stmt Q :=
 .pop k (fun _ y => y) (.branch (fun y => y == some x)
  (.load (fun _ => none) (.goto (fun _ => next))) (.goto (fun _ => .reject)))

def machine : Q → Stmt Q
 | .leftTag => expectAt .input .tokenEnd .rightTag
 | .rightTag => expectAt .output .tokenEnd (.core (.scan .eq))
 | .core (.done o) => .goto (fun _ => .leftFrame o)
 | .core q => Routine.relocate id Q.core (BinaryCompare.machine q)
 | .leftFrame o => expectAt .input .frameEnd (.rightFrame o)
 | .rightFrame o => expectAt .output .frameEnd (.done o)
 | .done _ | .reject => .halt

theorem expect_input (M : Q → Stmt Q) (q next : Q) (x : Symbol)
 (h : M q = expectAt .input x next) (v : Option Symbol) (a s c : List Symbol) :
 TM2.step M (config q v (x :: a) s c) = some (config next none a s c) := by
 cases x <;> simp [h,expectAt,config,TM2.step,TM2.stepAux,storage,Function.update]
 all_goals funext k; cases k <;> rfl

theorem expect_output (M : Q → Stmt Q) (q next : Q) (x : Symbol)
 (h : M q = expectAt .output x next) (v : Option Symbol) (a s c : List Symbol) :
 TM2.step M (config q v a s (x :: c)) = some (config next none a s c) := by
 cases x <;> simp [h,expectAt,config,TM2.step,TM2.stepAux,storage,Function.update]
 all_goals funext k; cases k <;> rfl

theorem agree (q : BinaryCompare.Q) (h : BinaryCompare.machine q ≠ .halt) :
 machine (.core q) = Routine.relocate id Q.core (BinaryCompare.machine q) := by
 cases q <;> simp_all [machine,BinaryCompare.machine]

theorem embed (q : BinaryCompare.Q) (v : Option Symbol) (a b c : List Symbol) :
 Routine.embed id Q.core (config q v a b c) (fun _ => []) = config (.core q) v a b c := by
 unfold Routine.embed config
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem compare_values (n m : Nat) (v : Option Symbol) (a s c : List Symbol) :
 TM2.Reaches machine
  (config .leftTag v (TypedContext.value (.nat n) ++ a) s (TypedContext.value (.nat m) ++ c))
  (config (.done (BinaryCompare.order .eq n m)) none a s c) := by
 let o := BinaryCompare.order .eq (2*n) (2*m)
 have ho : o = BinaryCompare.order .eq n m := by simp [o,BinaryCompare.order]
 have h0 : TM2.Reaches machine _ _ := Relation.ReflTransGen.single
   (expect_input machine .leftTag .rightTag .tokenEnd rfl v
    (tokenBits (2*n) ++ .frameEnd :: a) s (.tokenEnd :: (tokenBits (2*m) ++ .frameEnd :: c)))
 have h1 : TM2.Reaches machine _ _ := Relation.ReflTransGen.single
   (expect_output machine .rightTag (.core (.scan .eq)) .tokenEnd rfl none
    (tokenBits (2*n) ++ .frameEnd :: a) s (tokenBits (2*m) ++ .frameEnd :: c))
 have h2 := Routine.lift_embedded_run id Function.injective_id Q.core
   BinaryCompare.machine machine agree (fun _ => [])
   (BinaryCompare.compare_nats (2*n) (2*m) none (.frameEnd :: a) s (.frameEnd :: c)) (by simp [config])
 simp only [embed] at h2
 have h3 : TM2.Reaches machine
   (config (.core (.done o)) none (.frameEnd :: a) s (.frameEnd :: c))
   (config (.leftFrame o) none (.frameEnd :: a) s (.frameEnd :: c)) := Relation.ReflTransGen.single rfl
 have h4 : TM2.Reaches machine _ _ := Relation.ReflTransGen.single
   (expect_input machine (.leftFrame o) (.rightFrame o) .frameEnd rfl none a s (.frameEnd :: c))
 have h5 : TM2.Reaches machine _ _ := Relation.ReflTransGen.single
   (expect_output machine (.rightFrame o) (.done o) .frameEnd rfl none a s c)
 have h := h0.trans (h1.trans (h2.trans (h3.trans (h4.trans h5))))
 simpa [TM2.Reaches,TypedContext.value,tokenBits,Nat.zero_bits,List.append_assoc,ho] using h

end RosserDirect.TypedNatCompare
