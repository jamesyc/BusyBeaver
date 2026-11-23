module
public import I3_334.Search.SchedulerInput
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (LineRuns prefixSummary ifZero)

structure TrialHeader where
  proposal : Nat
  context : Nat
  dictionary : Nat
  selectors : Nat

def TrialHeader.decode (input : Nat) : TrialHeader :=
  let (proposal, afterProposal) := Cantor.unpair input
  let (context, afterContext) := Cantor.unpair afterProposal
  let (dictionary, selectors) := Cantor.unpair afterContext
  ⟨proposal,context,dictionary,selectors⟩

def TrialHeader.encode (h : TrialHeader) : Nat :=
  Cantor.pair h.proposal (Cantor.pair h.context (Cantor.pair h.dictionary h.selectors))

theorem TrialHeader.decode_encode (h : TrialHeader) : decode h.encode = h := by
  cases h
  simp [decode,encode,Cantor.unpair_pair]

def TrialHeader.reverse (h : TrialHeader) : Bool := h.context % 2 == 1

def TrialHeader.position (h : TrialHeader) : Nat := h.context / 2

def TrialHeader.prefix (h : TrialHeader) (current : Nat) : Bool × (Nat × Nat) :=
  prefixSummary h.position current h.proposal

theorem TrialHeader.context_value (h : TrialHeader) :
    h.context = 2*h.position + h.reverse.toNat := by
  have cases : h.context % 2 = 0 ∨ h.context % 2 = 1 := Nat.mod_two_eq_zero_or_one _
  rcases cases with w | w <;>
    simp [TrialHeader.position,TrialHeader.reverse,w] <;> omega

theorem TrialHeader.selectors_le (h : Nat) : (decode h).selectors ≤ h := by
  let step := fun n : Nat => (Cantor.unpair n).2
  have smaller (n : Nat) : step n ≤ n := by
    simpa only [step,Cantor.pair_unpair] using
      Cantor.right_le (Cantor.unpair n).1 (Cantor.unpair n).2
  exact Nat.le_trans (smaller (step (step h))) (Nat.le_trans (smaller (step h)) (smaller h))

def TrieInput (s : Scheduler) (h : TrialHeader) : Store :=
  let (valid,left,right) := h.prefix s.incumbent
  (((((s.store.set pl h.selectors).set fr (if h.reverse then right else left)).set lv
    (if h.reverse then left else right)).set dc h.dictionary).set gues
      (markedIf h.proposal (valid = true)))

theorem TrieInput.scratch (s : Scheduler) (h : TrialHeader) : Scratch (TrieInput s h) := by
  refine ⟨?_,?_,?_⟩ <;>
    simp [TrieInput,Scheduler.store,Store.set,np,pl,fr,lv,dc,tmp,gues,tok,expected,u]

theorem run_trialHeader (s : Scheduler) :
    LineRuns [produce,read goal,contextScan,read dc] s.store (TrieInput s (TrialHeader.decode s.pending)) := by
  let h := TrialHeader.decode s.pending
  let unpaired := produceEffect s.store
  let loaded := (unpaired.set pl (Cantor.unpair (unpaired pl)).2).set goal
    (unpaired goal + (Cantor.unpair (unpaired pl)).1)
  let compared := contextResult h.position h.reverse loaded
  have proposal : Executes produce s.store .normal unpaired :=
    run_produce s.store s.scratch
      (by simp [Scheduler.store,Store.set,np,pl,fr,tmp,gues])
      (by simp [Scheduler.store,Store.set,np,pl,fr,tmp,lv])
  have clean₁ : Scratch unpaired := by
    refine ⟨?_,?_,?_⟩ <;>
      simp [unpaired,produceEffect,Scheduler.store,Store.set,goal,np,pl,fr,tmp,gues,lv,expected,tok,u]
  have setup : Executes (read goal) unpaired .normal loaded :=
    run_read (by decide) (by decide) unpaired clean₁.tokenEmpty clean₁.auxiliaryEmpty
  have clean₂ : Scratch loaded := by
    refine ⟨?_,?_,?_⟩ <;>
      simp [loaded,unpaired,produceEffect,Scheduler.store,Store.set,goal,np,pl,fr,tmp,gues,lv,expected,tok,u]
  have code : loaded goal = 2*h.position+h.reverse.toNat := by
    rw [← h.context_value]
    simp [loaded,unpaired,produceEffect,h,TrialHeader.decode,Scheduler.store,Store.set,goal,np,pl,fr,tmp,gues,lv]
  have context : Executes contextScan loaded .normal compared := run_context _ _ _ clean₂ code
  have clean₃ : Scratch compared := by
    refine ⟨?_,?_,?_⟩ <;>
      simp [compared,contextResult,loaded,unpaired,produceEffect,Scheduler.store,Store.set,
        goal,np,pl,fr,tmp,gues,lv,expected,tok,u]
  have readDict := run_read (target := dc) (by decide) (by decide) compared
    clean₃.tokenEmpty clean₃.auxiliaryEmpty
  have output : ((compared.set pl (Cantor.unpair (compared pl)).2).set dc
        (compared dc + (Cantor.unpair (compared pl)).1)) = TrieInput s h := by
    funext r
    by_cases q : r = pl <;> by_cases l : r = fr <;> by_cases b : r = lv <;>
      by_cases g : r = gues <;> by_cases d : r = dc <;> by_cases a : r = goal <;>
      simp [TrieInput,compared,contextResult,loaded,unpaired,produceEffect,
        TrialHeader.prefix,h,TrialHeader.decode,Scheduler.store,Store.set,
        q,l,b,g,d,a,goal,np,pl,fr,tmp,gues,lv,dc]
  rw [output] at readDict
  exact .cons proposal (.cons setup (.cons context (.cons readDict .nil)))

theorem run_mainInput (s : Scheduler) :
    LineRuns [ifZero pl restart,produce,read goal,contextScan,read dc] s.store
      (TrieInput s.begin (TrialHeader.decode s.begin.pending)) := by
  exact .cons (run_begin s) (run_trialHeader s.begin)

end PalomarI3334.SearchProgram
