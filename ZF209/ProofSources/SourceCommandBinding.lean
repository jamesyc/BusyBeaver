module
public import SourceSchedulerCommands
public import PrimitiveAXCommand
@[expose] public section
namespace C209Search.Primitive.SourceScheduler
open M209.Source M209.SourceSimulation M6.Source.Enumeration M6.Source.Cantor

def regs (n l a : Nat) (s : CommandStore) : Registers := fun r =>
 if r=6 then n else if r=1 then l else if r=2 then s.t else if r=0 then s.w
 else if r=3 then s.d else if r=7 then s.h else if r=4 then a else 0

def configStore (pc n l a : Nat) (s : CommandStore) : Configuration := ⟨pc,regs n l a s⟩
private theorem mp_start (n l : Nat) (s : CommandStore) :
 MP.config 4222 s.t s.w s.d s.h l (fun r => if r=6 then n else 0)=configStore 4222 n l 0 s := by
 unfold MP.config configStore
 congr 1
 funext r
 by_cases h0:r=0 <;> by_cases h1:r=1 <;> by_cases h2:r=2 <;> by_cases h3:r=3 <;>
 by_cases h4:r=4 <;> by_cases h5:r=5 <;> by_cases h6:r=6 <;> by_cases h7:r=7 <;> by_cases h8:r=8 <;>
 simp_all [MP.registers,regs]
private theorem mp_end (n l : Nat) (s : CommandStore) :
 MP.config 25 s.t s.w s.d s.h l (fun r => if r=6 then n else 0)=boundary n l s := by
 unfold MP.config boundary
 congr 1
 funext r
 by_cases h0:r=0 <;> by_cases h1:r=1 <;> by_cases h2:r=2 <;> by_cases h3:r=3 <;>
 by_cases h4:r=4 <;> by_cases h5:r=5 <;> by_cases h6:r=6 <;> by_cases h7:r=7 <;> by_cases h8:r=8 <;>
 simp_all [MP.registers]

theorem mp_contract (n x tail : Nat) (s : CommandStore) :
 ∃k,0<k ∧ runSource k (configStore 4222 n (pair x tail) 0 s)=
 (commandEval (.mp x) s).map (boundary n tail) := by
 obtain ⟨k,hk,hr⟩ := MP.run_command_field s.t s.w s.d s.h x tail (fun r => if r=6 then n else 0)
 rw [mp_start] at hr
 have he := mp_end n tail (⟨if C209Soundness.impCode s.t (s.d+x)=s.h then s.d+x else 0,
 if C209Soundness.impCode s.t (s.d+x)=s.h then pair 0 s.w else s.w,s.d+x,0⟩ : CommandStore)
 simp only at he
 rw [he] at hr
 refine ⟨k,hk,?_⟩
 by_cases h : C209Soundness.impCode s.t (s.d+x)=s.h <;> simpa [commandEval,h] using hr

private theorem ax_start (n a x y tail : Nat) (s : CommandStore) :
 AXMacro.configAt 50 (AXCommand.input s.t a s.d s.h x y tail) s.w (fun r => if r=6 then n else 0) =
 configStore 50 n (pair y (pair x tail)) a s := by
 unfold AXMacro.configAt configStore
 congr 1
 funext r
 by_cases h0:r=0 <;> by_cases h1:r=1 <;> by_cases h2:r=2 <;> by_cases h3:r=3 <;>
 by_cases h4:r=4 <;> by_cases h5:r=5 <;> by_cases h6:r=6 <;> by_cases h7:r=7 <;> by_cases h8:r=8 <;>
 simp_all [AXMacro.registers,AXCommand.input,AXMacro.stackCode,regs]

private theorem ax_end (n a x y tail : Nat) (s : CommandStore) :
 AXMacro.configAt 25 (AXCommand.result s.t a s.d s.h x y tail) s.w (fun r => if r=6 then n else 0) =
 boundary n tail ⟨C209Search.gate a (s.d+x) (s.h+y),
 (heads a (s.d+x) (s.h+y) s.d s.h ++ [s.t]).foldr pair s.w,0,0⟩ := by
 unfold AXMacro.configAt boundary
 congr 1
 funext r
 by_cases h0:r=0 <;> by_cases h1:r=1 <;> by_cases h2:r=2 <;> by_cases h3:r=3 <;>
 by_cases h4:r=4 <;> by_cases h5:r=5 <;> by_cases h6:r=6 <;> by_cases h7:r=7 <;> by_cases h8:r=8 <;>
 simp_all [AXMacro.registers,AXCommand.result,AXMacro.stackCode]

theorem ax_contract (n a x y tail : Nat) (s : CommandStore) :
 ∃k,0<k ∧ runSource k (configStore 50 n (pair y (pair x tail)) a s)=
 (commandEval (.ax a x y) s).map (boundary n tail) := by
 obtain ⟨k,hk,hr⟩ := AXCommand.run_command s.t a s.d s.h x y tail s.w (fun r => if r=6 then n else 0)
 rw [ax_start,ax_end] at hr
 exact ⟨k,hk,hr⟩

private theorem shift_start (n l : Nat) (s : CommandStore) :
 SCommand.start s.t s.h s.w (regs n l 0 s) = configStore 4329 n l 0 s := by
 unfold SCommand.start SStage.configAt configStore
 congr 1
 funext r
 by_cases h0:r=0 <;> by_cases h1:r=1 <;> by_cases h2:r=2 <;> by_cases h3:r=3 <;>
 by_cases h4:r=4 <;> by_cases h5:r=5 <;> by_cases h6:r=6 <;> by_cases h7:r=7 <;> by_cases h8:r=8 <;>
 simp_all [SStage.registers,SCommand.frame,write,regs]
private theorem shift_end (n l : Nat) (s : CommandStore) :
 SCommand.output s.h s.w (regs n l 0 s) =
 boundary n l ⟨s.h,(M6.Source.Cantor.decode s.w).2,s.d,(M6.Source.Cantor.decode s.w).1⟩ := by
 unfold SCommand.output Unpair.exitAt boundary
 congr 1
 funext r
 by_cases h0:r=0 <;> by_cases h1:r=1 <;> by_cases h2:r=2 <;> by_cases h3:r=3 <;>
 by_cases h4:r=4 <;> by_cases h5:r=5 <;> by_cases h6:r=6 <;> by_cases h7:r=7 <;> by_cases h8:r=8 <;>
 simp_all [Unpair.registers,SCommand.frame,write,regs]

theorem shift_contract (n l : Nat) (s : CommandStore) :
 match commandEval .shift s with
 | none => Terminates (scalarNext program) (configStore 4329 n l 0 s)
 | some out => ∃k,0<k ∧ runSource k (configStore 4329 n l 0 s)=some (boundary n l out) := by
 by_cases he : s.t+s.h=1
 · simp only [commandEval,he,ite_true]
   have h := SCommand.halts_of_sum_one s.t s.h s.w (regs n l 0 s) he
   rw [shift_start] at h
   exact h
 · simp only [commandEval,he,ite_false]
   obtain ⟨k,hk⟩ := SCommand.run_of_sum_ne_one s.t s.h s.w (regs n l 0 s) he
   rw [shift_start,shift_end] at hk
   refine ⟨k,?_,hk⟩
   cases k with
   | zero => simp [runSource,configStore,boundary] at hk
   | succ k => omega

end C209Search.Primitive.SourceScheduler
