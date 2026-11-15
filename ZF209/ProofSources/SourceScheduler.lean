module
public import PrimitiveFetchDispatch
public import PrimitiveSEndpoint
public import PrimitiveMPCommand
public import SearchScheduler
@[expose] public section
namespace C209Search.Primitive.SourceScheduler
open M209.Source M209.SourceSimulation M6.Source.Enumeration

theorem run_add (a b : Nat) (s : Configuration) :
 runSource (a+b) s = (runSource a s).bind (runSource b) := by
 induction a generalizing s with
 | zero => simp [runSource]
 | succ a ih =>
  simp only [Nat.succ_add,runSource]
  cases h : scalarNext program s <;> simp [h,ih]

theorem run_prefix_some {k : Nat} {s t : Configuration}
 (h : runSource k s = some t) (n : Nat) (hn : n≤k) : ∃u,runSource n s=some u := by
 have he := run_add n (k-n) s
 rw [Nat.add_sub_of_le hn,h] at he
 cases hh : runSource n s with
 | none => simp [hh] at he
 | some u => exact ⟨u,rfl⟩

theorem terminates_iff_run_none (s : Configuration) :
 Terminates (scalarNext program) s ↔ ∃n,runSource n s=none := by
 constructor
 · intro h
   induction h with
   | done h => exact ⟨1,by simp [runSource,h]⟩
   | more h ht ih =>
     obtain ⟨n,hn⟩ := ih
     exact ⟨n+1,by simp [runSource,h,hn]⟩
 · rintro ⟨n,hn⟩
   induction n generalizing s with
   | zero => simp [runSource] at hn
   | succ n ih =>
    cases hs : scalarNext program s with
    | none => exact .done hs
    | some t =>
      apply Terminates.more hs
      apply ih
      simpa [runSource,hs] using hn

theorem prefix_terminates {k : Nat} {s t : Configuration}
 (h : runSource k s=some t) (ht : Terminates (scalarNext program) t) :
 Terminates (scalarNext program) s := by
 obtain ⟨n,hn⟩ := (terminates_iff_run_none t).mp ht
 apply (terminates_iff_run_none s).mpr
 exact ⟨k+n,by rw [run_add,h]; exact hn⟩

/-- Positive source progress makes an abstract nonhalting invariant genuinely
nonterminating; a zero-step self-loop would not suffice. -/
theorem no_termination_of_progress (Inv : Configuration→Prop)
 (progress : ∀s, Inv s → ∃k t, 0<k ∧ runSource k s=some t ∧ Inv t)
 (s : Configuration) (hs : Inv s) : ¬ Terminates (scalarNext program) s := by
 intro ht
 obtain ⟨n,hn⟩ := (terminates_iff_run_none s).mp ht
 have aux : ∀n s, Inv s → runSource n s ≠ none := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro s hs hh
    obtain ⟨k,t,hk,hr,hit⟩ := progress s hs
    by_cases hkn : n≤k
    · obtain ⟨u,hu⟩ := run_prefix_some hr n hkn
      rw [hu] at hh
      cases hh
    · have hlt : n-k<n := by omega
      apply ih (n-k) hlt t hit
      have hle : k≤n := by omega
      have he := run_add k (n-k) s
      rw [Nat.add_sub_of_le hle,hh,hr] at he
      exact he.symm
 exact aux n s hs hn

/-- A complete candidate contract preserves the entire returned command store. -/
def CandidateContract (frame : Nat→CommandStore→Configuration) : Prop :=
 ∀n s, match commandsEval (word n) s with
 | none => Terminates (scalarNext program) (frame n s)
 | some out => ∃k,0<k ∧ runSource k (frame n s)=some (frame (n+1) out)

theorem source_iff_sequential (frame : Nat→CommandStore→Configuration)
 (hc : CandidateContract frame) (n : Nat) (s : CommandStore) :
 Terminates (scalarNext program) (frame n s) ↔ SequentialSearchHalts n s := by
 constructor
 · intro ht
   apply Classical.byContradiction
   intro hno
   let Inv : Configuration→Prop := fun c => ∃n s,c=frame n s ∧ ¬SequentialSearchHalts n s
   have progress : ∀c,Inv c → ∃k t,0<k ∧ runSource k c=some t ∧ Inv t := by
    rintro c ⟨n,s,rfl,hn⟩
    have hc' := hc n s
    cases he : commandsEval (word n) s with
    | none =>
      exfalso
      apply hn
      exact ⟨1,by simp [searchRun,he]⟩
    | some out =>
      simp only [he] at hc'
      obtain ⟨k,hk,hr⟩ := hc'
      refine ⟨k,frame (n+1) out,hk,hr,n+1,out,rfl,?_⟩
      rintro ⟨fuel,hf⟩
      apply hn
      exact ⟨fuel+1,by simpa [searchRun,he] using hf⟩
   exact no_termination_of_progress Inv progress (frame n s) ⟨n,s,rfl,hno⟩ ht
 · rintro ⟨fuel,hf⟩
   induction fuel generalizing n s with
   | zero => simp [searchRun] at hf
   | succ fuel ih =>
    have hc' := hc n s
    cases he : commandsEval (word n) s with
    | none => simpa only [he] using hc'
    | some out =>
      simp only [he] at hc'
      obtain ⟨k,hk,hr⟩ := hc'
      apply prefix_terminates hr
      apply ih (n+1) out
      simpa [searchRun,he] using hf
end C209Search.Primitive.SourceScheduler
