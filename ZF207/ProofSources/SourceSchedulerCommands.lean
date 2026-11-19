module
public import SourceScheduler
@[expose] public section
namespace C207Search.Primitive.SourceScheduler
open M207.Source M207.SourceSimulation M6.Source.Enumeration

def boundary (n l : Nat) (s : CommandStore) : Configuration :=
 ⟨25,fun r => if r=6 then n else if r=1 then l else if r=2 then s.t
 else if r=0 then s.w else if r=3 then s.d else if r=7 then s.h else 0⟩

/-- One concrete fetch, parse and command, preserving the retained store. -/
def FetchCommandContract : Prop := ∀n l s,
 let p := parse (FetchDispatch.seed n l)
 match commandEval p.command s with
 | none => Terminates (scalarNext program) (boundary n l s)
 | some out => ∃k,0<k ∧ runSource k (boundary n l s)=some (boundary (FetchDispatch.nextN n l) p.next out)

theorem residual_contract (hc : FetchCommandContract) (l n : Nat) (s : CommandStore) :
 match commandsEval (residual l) s with
 | none => Terminates (scalarNext program) (boundary n l s)
 | some out => ∃k,runSource k (boundary n l s)=some (boundary n 0 out) := by
 induction l using Nat.strongRecOn generalizing n s with
 | ind l ih =>
  cases l with
  | zero => simp only [residual,commandsEval]; exact ⟨0,rfl⟩
  | succ l =>
    have ha := hc n (l+1) s
    simp only [FetchDispatch.seed,FetchDispatch.nextN,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,ite_false,Nat.add_sub_cancel] at ha
    rw [residual]
    simp only [commandsEval]
    cases he : commandEval (parse l).command s with
    | none => simpa only [he,Option.bind_none] using ha
    | some out =>
      simp only [he] at ha
      obtain ⟨k,hk,hr⟩ := ha
      have hb := ih (parse l).next (Nat.lt_succ_of_le (parse_next_le l)) n out
      cases hf : commandsEval (residual (parse l).next) out with
      | none =>
        simp only [hf] at hb
        simpa only [he,Option.bind_some,hf] using prefix_terminates hr hb
      | some last =>
        simp only [hf] at hb
        obtain ⟨m,hm⟩ := hb
        simp only [he,Option.bind_some,hf]
        exact ⟨k+m,by rw [run_add,hr];exact hm⟩

theorem candidate_contract_of_fetch (hc : FetchCommandContract) :
 CandidateContract (fun n s => boundary n 0 s) := by
 intro n s
 have ha := hc n 0 s
 simp only [FetchDispatch.seed,FetchDispatch.nextN,ite_true] at ha
 unfold word
 simp only [commandsEval]
 cases he : commandEval (parse n).command s with
 | none => simpa only [he,Option.bind_none] using ha
 | some out =>
   simp only [he] at ha
   obtain ⟨k,hk,hr⟩ := ha
   have hb := residual_contract hc (parse n).next (n+1) out
   cases hf : commandsEval (residual (parse n).next) out with
   | none =>
     simp only [hf] at hb
     simpa only [he,Option.bind_some,hf] using prefix_terminates hr hb
   | some last =>
     simp only [hf] at hb
     obtain ⟨m,hm⟩ := hb
     simp only [he,Option.bind_some,hf]
     exact ⟨k+m,by omega,by rw [run_add,hr];exact hm⟩

theorem source_scheduler_iff (hc : FetchCommandContract) (n : Nat) (s : CommandStore) :
 Terminates (scalarNext program) (boundary n 0 s) ↔ SequentialSearchHalts n s :=
 source_iff_sequential _ (candidate_contract_of_fetch hc) n s

end C207Search.Primitive.SourceScheduler
