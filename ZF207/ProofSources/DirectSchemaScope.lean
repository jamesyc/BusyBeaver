module
public import DirectScopeGuard
public import DirectAllIntroPremise
@[expose] public section
namespace RosserDirect.SchemaScope
open Turing Segment FourStack
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

def cutoff (replacement : Bool) (n : Nat) := if replacement then n+2 else n+1
inductive Q where
 | save (q : Label) | increment (second : Bool) (q : ReturnValue.Q (TypedNatUnary.Control BinarySuccessor.Q))
 | restore (q : Label) | check (q : ScopeGuard.Q)
 | discard (q : Grammar.DropControl TypedBlock.Control) | accept | reject
 deriving DecidableEq, Fintype, Inhabited

def machine (rep : Bool) : Q → Stmt4 Q
 | .save .done => .goto (fun _ => .increment false (.first .start))
 | .save q => Routine.relocate prepareRoles Q.save (RosserDirect.machine q)
 | .increment false .done => .goto (fun _ => if rep then .increment true (.first .start) else .restore .scan)
 | .increment true .done => .goto (fun _ => .restore .scan)
 | .increment second q => Routine.relocate dataRoles (Q.increment second) (ReturnValue.incrementMachine q)
 | .restore .done => .goto (fun _ => .check .start)
 | .restore q => Routine.relocate readRoles Q.restore (RosserDirect.machine q)
 | .check .accept => .goto (fun _ => .discard (.scan (.run 1 .start)))
 | .check .reject => .goto (fun _ => .reject)
 | .check q => Routine.relocate id Q.check (ScopeGuard.machine q)
 | .discard .done => .load (fun _ => none) (.goto (fun _ => .accept))
 | .discard q => Routine.relocate dataRoles Q.discard (TypedBlock.dropMachine q)
 | .accept | .reject => .halt

theorem agree_save (r : Bool) (q : Label) (h : RosserDirect.machine q ≠ .halt) :
 machine r (.save q) = Routine.relocate prepareRoles Q.save (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]
theorem agree_increment (r s : Bool) (q : ReturnValue.Q (TypedNatUnary.Control BinarySuccessor.Q))
 (h : ReturnValue.incrementMachine q ≠ .halt) :
 machine r (.increment s q) = Routine.relocate dataRoles (Q.increment s) (ReturnValue.incrementMachine q) := by
 cases q <;> cases s <;> simp_all [machine,ReturnValue.incrementMachine,ReturnValue.machine]
theorem agree_restore (r : Bool) (q : Label) (h : RosserDirect.machine q ≠ .halt) :
 machine r (.restore q) = Routine.relocate readRoles Q.restore (RosserDirect.machine q) := by
 cases q <;> simp_all [machine,RosserDirect.machine]
theorem agree_check (r : Bool) (q : ScopeGuard.Q) (h : ScopeGuard.machine q ≠ .halt) :
 machine r (.check q) = Routine.relocate id Q.check (ScopeGuard.machine q) := by
 cases q <;> simp_all [machine,ScopeGuard.machine]
theorem agree_discard (r : Bool) (q : Grammar.DropControl TypedBlock.Control) (h : TypedBlock.dropMachine q ≠ .halt) :
 machine r (.discard q) = Routine.relocate dataRoles Q.discard (TypedBlock.dropMachine q) := by
 cases q <;> simp_all [machine,TypedBlock.dropMachine,Grammar.dropMachine]

theorem increment (r : Bool) (n : Nat) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches (machine r)
  (cfg4 (.increment false (.first .start)) v p (TypedContext.value (.nat n) ++ a) [] c)
  (cfg4 (.restore .scan) none p (TypedContext.value (.nat (cutoff r n)) ++ a) [] c) := by
 have h0 := Routine.lift_embedded_run dataRoles data_injective (Q.increment false)
  ReturnValue.incrementMachine (machine r) (agree_increment r false) (fun _ => p)
  (ReturnValue.increment n v a c) (by simp [config])
 simp only [embed_data] at h0
 cases r with
 | false =>
  have h1 : TM2.Reaches (machine false)
   (cfg4 (.increment false .done) none p (TypedContext.value (.nat (n+1)) ++ a) [] c)
   (cfg4 (.restore .scan) none p (TypedContext.value (.nat (n+1)) ++ a) [] c) := Relation.ReflTransGen.single rfl
  exact h0.trans h1
 | true =>
  have h1 : TM2.Reaches (machine true)
   (cfg4 (.increment false .done) none p (TypedContext.value (.nat (n+1)) ++ a) [] c)
   (cfg4 (.increment true (.first .start)) none p (TypedContext.value (.nat (n+1)) ++ a) [] c) := Relation.ReflTransGen.single rfl
  have h2 := Routine.lift_embedded_run dataRoles data_injective (Q.increment true)
   ReturnValue.incrementMachine (machine true) (agree_increment true true) (fun _ => p)
   (ReturnValue.increment (n+1) none a c) (by simp [config])
  simp only [embed_data] at h2
  have h3 : TM2.Reaches (machine true)
   (cfg4 (.increment true .done) none p (TypedContext.value (.nat (n+2)) ++ a) [] c)
   (cfg4 (.restore .scan) none p (TypedContext.value (.nat (n+2)) ++ a) [] c) := Relation.ReflTransGen.single rfl
  exact h0.trans (h1.trans (h2.trans h3))

theorem prepare (r : Bool) (f : ZFR.Formula) (n : Nat) (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches (machine r)
  (cfg4 (.save .scan) v p (TypedContext.stack [.formula f,.nat n] ++ a) [] c)
  (cfg4 (.check .start) none p (TypedContext.stack [.formula f,.nat (cutoff r n)] ++ a) [] c) := by
 have h0 := Routine.lift_embedded_run prepareRoles prepare_injective Q.save
  RosserDirect.machine (machine r) (agree_save r) (fun _ => c)
  (AllIntroPremise.move_formula f v (TypedContext.value (.nat n) ++ a) p) (by simp [config])
 simp only [embed_prepare] at h0
 have h1 : TM2.Reaches (machine r)
  (cfg4 (.save .done) none (TypedContext.value (.formula f) ++ p) (TypedContext.value (.nat n) ++ a) [] c)
  (cfg4 (.increment false (.first .start)) none (TypedContext.value (.formula f) ++ p) (TypedContext.value (.nat n) ++ a) [] c) := Relation.ReflTransGen.single rfl
 have h2 := increment r n none (TypedContext.value (.formula f) ++ p) a c
 have h3 := Routine.lift_embedded_run readRoles read_injective Q.restore
  RosserDirect.machine (machine r) (agree_restore r) (fun _ => c)
  (AllIntroPremise.move_formula f none p (TypedContext.value (.nat (cutoff r n)) ++ a)) (by simp [config])
 simp only [embed_read] at h3
 have h4 : TM2.Reaches (machine r)
  (cfg4 (.restore .done) none p (TypedContext.value (.formula f) ++ TypedContext.value (.nat (cutoff r n)) ++ a) [] c)
  (cfg4 (.check .start) none p (TypedContext.value (.formula f) ++ TypedContext.value (.nat (cutoff r n)) ++ a) [] c) := Relation.ReflTransGen.single rfl
 simp only [List.append_assoc] at h4
 simpa only [TM2.Reaches,TypedContext.stack,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
  using h0.trans (h1.trans (h2.trans (h3.trans h4)))

theorem accept (r : Bool) (f : ZFR.Formula) (n : Nat) (hf : ZFR.Bound f (cutoff r n))
 (v : Option Symbol) (p a c : List Symbol) :
 TM2.Reaches (machine r)
  (cfg4 (.save .scan) v p (TypedContext.stack [.formula f,.nat n] ++ a) [] c)
  (cfg4 .accept none p a [] c) := by
 have h0 := prepare r f n v p a c
 have h1 := FourStack.relabel_run Q.check ScopeGuard.machine (machine r) (agree_check r)
  _ _ _ _ _ _ _ _ _ _ _ _ (ScopeGuard.accept f (cutoff r n) hf none p a c)
 have h2 : TM2.Reaches (machine r)
  (cfg4 (.check .accept) (some .frameEnd) p (TypedContext.stack [.formula f,.nat (cutoff r n)] ++ a) [] c)
  (cfg4 (.discard (.scan (.run 1 .start))) (some .frameEnd) p (TypedContext.stack [.formula f,.nat (cutoff r n)] ++ a) [] c) := Relation.ReflTransGen.single rfl
 obtain ⟨w,hw⟩ := TypedBlock.drop_block 1 [.formula f,.nat (cutoff r n)] rfl (some .frameEnd) a [] c
 have h3 := Routine.lift_embedded_run dataRoles data_injective Q.discard
  TypedBlock.dropMachine (machine r) (agree_discard r) (fun _ => p)
  hw (by simp [config])
 simp only [embed_data] at h3
 have h4 : TM2.Reaches (machine r) (cfg4 (.discard .done) w p a [] c)
  (cfg4 .accept none p a [] c) := Relation.ReflTransGen.single rfl
 exact h0.trans (h1.trans (h2.trans (h3.trans h4)))

theorem reject (r : Bool) (f : ZFR.Formula) (n : Nat) (hf : ¬ZFR.Bound f (cutoff r n))
 (v : Option Symbol) (p a c : List Symbol) :
 ∃ w p' a', TM2.Reaches (machine r)
  (cfg4 (.save .scan) v p (TypedContext.stack [.formula f,.nat n] ++ a) [] c)
  (cfg4 .reject w p' a' [] c) := by
 obtain ⟨w,p',a',hr⟩ := ScopeGuard.reject f (cutoff r n) hf none p a c
 have h1 := FourStack.relabel_run Q.check ScopeGuard.machine (machine r) (agree_check r)
  _ _ _ _ _ _ _ _ _ _ _ _ hr
 have h2 : TM2.Reaches (machine r) (cfg4 (.check .reject) w p' a' [] c)
  (cfg4 .reject w p' a' [] c) := Relation.ReflTransGen.single rfl
 exact ⟨w,p',a',(prepare r f n v p a c).trans (h1.trans h2)⟩

end RosserDirect.SchemaScope
