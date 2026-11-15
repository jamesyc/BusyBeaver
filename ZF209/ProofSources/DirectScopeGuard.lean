module
public import DirectScopeCheck
public import DirectFourStackLink
@[expose] public section
namespace RosserDirect.ScopeGuard
open Turing Segment FourStack
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

def swap : K → K
 | .stream => .stream | .data => .output | .scratch => .scratch | .output => .data

theorem swap_injective : Function.Injective swap := by
 intro a b h; cases a <;> cases b <;> simp_all [swap]

inductive Q where
 | start | copy (q : Grammar.CopyControl TypedBlock.Control)
 | check (q : ScopeCheck.Q) | accept | reject
 deriving DecidableEq, Fintype, Inhabited

def machine : Q → Stmt4 Q
 | .start => .push .output (fun _ => .frameEnd) (.goto (fun _ => .copy (.scan (.run 1 .start))))
 | .copy .done => .goto (fun _ => .check (.copy .scan))
 | .copy q => Routine.relocate dataRoles Q.copy (TypedBlock.machine q)
 | .check .accept => .goto (fun _ => .accept)
 | .check .reject => .goto (fun _ => .reject)
 | .check q => Routine.relocate swap Q.check (ScopeCheck.machine q)
 | .accept | .reject => .halt

theorem agree_copy (q : Grammar.CopyControl TypedBlock.Control) (h : TypedBlock.machine q ≠ .halt) :
 machine (.copy q) = Routine.relocate dataRoles Q.copy (TypedBlock.machine q) := by
 cases q <;> simp_all [machine,TypedBlock.machine,Grammar.copyMachine]
theorem agree_check (q : ScopeCheck.Q) (h : ScopeCheck.machine q ≠ .halt) :
 machine (.check q) = Routine.relocate swap Q.check (ScopeCheck.machine q) := by
 cases q <;> simp_all [machine,ScopeCheck.machine]

theorem embed_check (q : ScopeCheck.Q) (v : Option Symbol) (p a s c : List Symbol) :
 embed4 swap Q.check (cfg4 q v p a s c) (fun _ => []) = cfg4 (.check q) v p c s a := by
 unfold embed4 cfg4
 simp only [Option.map_some]
 congr 1
 funext k; cases k <;> rfl

theorem prepare (f : ZFR.Formula) (n : Nat) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches machine
  (cfg4 .start v p (TypedContext.stack [.formula f,.nat n] ++ a) [] c)
  (cfg4 (.check (.copy .scan)) none p (TypedContext.stack [.formula f,.nat n] ++ a) []
   (TypedContext.stack [.formula f,.nat n] ++ .frameEnd :: c)) := by
 have h0 : TM2.Reaches machine
  (cfg4 .start v p (TypedContext.stack [.formula f,.nat n] ++ a) [] c)
  (cfg4 (.copy (.scan (.run 1 .start))) v p (TypedContext.stack [.formula f,.nat n] ++ a) [] (.frameEnd :: c)) := by
  apply Relation.ReflTransGen.single
  simp [machine,cfg4,TM2.step,TM2.stepAux,store4,Function.update]
  funext k; cases k <;> rfl
 have h1 := Routine.lift_embedded_run dataRoles data_injective Q.copy
  TypedBlock.machine machine agree_copy (fun _ => p)
  (TypedBlock.copy_block 1 [.formula f,.nat n] rfl v a (.frameEnd :: c)) (by simp [config])
 simp only [embed_data] at h1
 have h2 : TM2.Reaches machine
  (cfg4 (.copy .done) none p (TypedContext.stack [.formula f,.nat n] ++ a) []
   (TypedContext.stack [.formula f,.nat n] ++ .frameEnd :: c))
  (cfg4 (.check (.copy .scan)) none p (TypedContext.stack [.formula f,.nat n] ++ a) []
   (TypedContext.stack [.formula f,.nat n] ++ .frameEnd :: c)) := Relation.ReflTransGen.single rfl
 exact h0.trans (h1.trans h2)

/-- Non-destructive canonical scope guard, standard two-field ABI.
No caller-supplied duplicate or internal sentinel is trusted. -/
theorem accept (f : ZFR.Formula) (n : Nat) (hf : ZFR.Bound f n)
 (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches machine
  (cfg4 .start v p (TypedContext.stack [.formula f,.nat n] ++ a) [] c)
  (cfg4 .accept (some .frameEnd) p (TypedContext.stack [.formula f,.nat n] ++ a) [] c) := by
 have h0 := prepare f n v p a c
 have h1 := FourStack.lift4_run swap swap_injective Q.check ScopeCheck.machine machine agree_check
  (fun _ => []) (ScopeCheck.accept f n hf none p c (TypedContext.stack [.formula f,.nat n] ++ a)) (by simp [cfg4])
 simp only [embed_check] at h1
 have h2 : TM2.Reaches machine
  (cfg4 (.check .accept) (some .frameEnd) p (TypedContext.stack [.formula f,.nat n] ++ a) [] c)
  (cfg4 .accept (some .frameEnd) p (TypedContext.stack [.formula f,.nat n] ++ a) [] c) := Relation.ReflTransGen.single rfl
 apply h0.trans
 simpa only [TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] using h1.trans h2

theorem reject (f : ZFR.Formula) (n : Nat) (hf : ¬ZFR.Bound f n)
 (v : Option Symbol) (p a c : List Symbol) :
 ∃ w p' a', TM2.Reaches machine
  (cfg4 .start v p (TypedContext.stack [.formula f,.nat n] ++ a) [] c)
  (cfg4 .reject w p' a' [] c) := by
 obtain ⟨w,p',a',hr⟩ := ScopeCheck.reject f n hf none p c (TypedContext.stack [.formula f,.nat n] ++ a)
 have h1 := FourStack.lift4_run swap swap_injective Q.check ScopeCheck.machine machine agree_check (fun _ => []) hr (by simp [cfg4])
 simp only [embed_check] at h1
 have h2 : TM2.Reaches machine (cfg4 (.check .reject) w p' a' [] c)
  (cfg4 .reject w p' a' [] c) := Relation.ReflTransGen.single rfl
 refine ⟨w,p',a',(prepare f n v p a c).trans ?_⟩
 simpa only [TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] using h1.trans h2

end RosserDirect.ScopeGuard
