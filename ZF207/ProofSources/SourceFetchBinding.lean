module
public import SourceCommandBinding
@[expose] public section
namespace C207Search.Primitive.SourceScheduler
open M207.Source M207.SourceSimulation M6.Source.Enumeration M6.Source.Cantor

private theorem fetch_regs (n l a n0 l0 : Nat) (s : CommandStore) :
 Fetch.registers n l a (regs n0 l0 0 s) = regs n l a s := by
 funext r
 by_cases h0:r=0 <;> by_cases h1:r=1 <;> by_cases h2:r=2 <;> by_cases h3:r=3 <;>
 by_cases h4:r=4 <;> by_cases h5:r=5 <;> by_cases h6:r=6 <;> by_cases h7:r=7 <;> by_cases h8:r=8 <;>
 simp_all [Fetch.registers,Residual.registers,regs,write]

private theorem fetch_start (n l : Nat) (s : CommandStore) :
 Fetch.start n l (regs n l 0 s)=boundary n l s := by
 unfold Fetch.start
 rw [fetch_regs]
 unfold boundary
 congr 1
 funext r
 simp [regs]

private theorem fetch_end (n l : Nat) (s : CommandStore) :
 FetchDispatch.commandEntry n l (regs n l 0 s)=
 configStore (Dispatch.target (M6.Source.Cantor.decode (FetchDispatch.seed n l)).1)
 (FetchDispatch.nextN n l) (M6.Source.Cantor.decode (FetchDispatch.seed n l)).2
 ((M6.Source.Cantor.decode (FetchDispatch.seed n l)).1-2) s := by
 unfold FetchDispatch.commandEntry configStore
 dsimp only
 rw [fetch_regs]

private theorem dec_live (pc : Nat) (r : Fin 9) (z p : Nat) (f : Registers)
 (h : program pc=some (.dec r z p)) : scalarNext program ⟨pc,f⟩ ≠ none := by
 unfold scalarNext
 rw [h]
 simp only [Option.bind_some,scalarExecute]
 split <;> simp

private theorem entry_live (c n l : Nat) (s : CommandStore) :
 scalarNext program (configStore (Dispatch.target c) n l (c-2) s) ≠ none := by
 cases c with
 | zero => exact dec_live 4329 2 4332 4330 _ (by decide +kernel)
 | succ c =>
   cases c with
   | zero => exact dec_live 4222 1 4230 4223 _ (by decide +kernel)
   | succ c =>
     have ht : Dispatch.target (c+2)=50 := by simp [Dispatch.target]
     rw [ht]
     exact dec_live 50 2 53 51 _ (by decide +kernel)

private theorem parsed_contract (n seed : Nat) (s : CommandStore) :
 match commandEval (parse seed).command s with
 | none => Terminates (scalarNext program)
   (configStore (Dispatch.target (M6.Source.Cantor.decode seed).1) n (M6.Source.Cantor.decode seed).2 ((M6.Source.Cantor.decode seed).1-2) s)
 | some out => ∃k,0<k ∧ runSource k
   (configStore (Dispatch.target (M6.Source.Cantor.decode seed).1) n (M6.Source.Cantor.decode seed).2 ((M6.Source.Cantor.decode seed).1-2) s)=some (boundary n (parse seed).next out) := by
 cases hd : M6.Source.Cantor.decode seed with
 | mk c l =>
  unfold parse
  rw [hd]
  cases c with
  | zero =>
      have hs := shift_contract n l s
      cases he : commandEval .shift s <;> simp only [he] at hs ⊢ <;>
       simpa only [Dispatch.target,ite_true,Nat.zero_sub] using hs
  | succ c =>
    cases c with
    | zero =>
      have hm := mp_contract n (M6.Source.Cantor.decode l).1 (M6.Source.Cantor.decode l).2 s
      rw [pair_decode] at hm
      by_cases h : C207Soundness.impCode s.t (s.d+(M6.Source.Cantor.decode l).1)=s.h <;> simpa [Dispatch.target,commandEval,h] using hm
    | succ c =>
      have hm := ax_contract n c (M6.Source.Cantor.decode (M6.Source.Cantor.decode l).2).1 (M6.Source.Cantor.decode l).1 (M6.Source.Cantor.decode (M6.Source.Cantor.decode l).2).2 s
      rw [pair_decode,pair_decode] at hm
      have ht : Dispatch.target (c+2)=50 := by simp [Dispatch.target]
      simpa only [ht,show c+1+1-2=c by omega,commandEval,Option.map_some] using hm

theorem literal_fetch_command_contract : FetchCommandContract := by
 intro n l s
 obtain ⟨k,hk,hs⟩ := FetchDispatch.total n l (regs n l 0 s)
 rw [fetch_start,fetch_end] at hs
 have hr := steps_real k _ _ hs (entry_live _ _ _ s)
 have hc := parsed_contract (FetchDispatch.nextN n l) (FetchDispatch.seed n l) s
 cases he : commandEval (parse (FetchDispatch.seed n l)).command s with
 | none =>
   simp only [he] at hc ⊢
   exact prefix_terminates hr hc
 | some out =>
   simp only [he] at hc ⊢
   obtain ⟨m,hm,hc⟩ := hc
   exact ⟨k+m,by omega,by rw [run_add,hr];exact hc⟩

theorem literal_source_scheduler_iff (n : Nat) (s : CommandStore) :
 Terminates (scalarNext program) (boundary n 0 s) ↔ SequentialSearchHalts n s :=
 source_scheduler_iff literal_fetch_command_contract n s
end C207Search.Primitive.SourceScheduler
