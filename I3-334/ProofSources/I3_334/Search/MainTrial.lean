module
public import I3_334.Search.TrialOutput
public import I3_334.Search.TrialFronts
public import I3_334.Simulation.MachineSimulation
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (LineRuns prefixSummary_correct)
open Templates (equations equationInstructions)
open Relation (ReflTransGen)

def TrialHeader.check (h : TrialHeader) (e : Templates.Equation) (old : Nat) : Bool :=
  checkTrial e h.reverse h.position h.dictionary old h.proposal

def TrialHeader.mark (h : TrialHeader) (e : Templates.Equation) (old : Nat) : Nat :=
  markedIf h.proposal (h.check e old = true)

theorem check_after_context (h : TrialHeader) (e : Templates.Equation) (s : Scheduler) :
    h.check e s.incumbent =
      ((h.prefix s.incumbent).1 &&
        frontsAccept e (Dictionary.decode h.dictionary) (TrieInput s h fr) (TrieInput s h lv)) := by
  let view := h.prefix s.incumbent
  have prefixEq := prefixSummary_correct h.position s.incumbent h.proposal
  change comparePrefix _ _ _ = (if view.1 then some view.2 else none) at prefixEq
  unfold TrialHeader.check checkTrial acceptMatched
  rw [prefixEq]
  cases good : view.1
  · simp [view,good]
  · cases direction : h.reverse <;>
      simp only [view,good,↓reduceIte,TrieInput,Store.set,fr,lv,dc,gues,pl,
        Nat.reduceEqDiff, sides, Bool.false_eq_true, Bool.true_and, direction, frontsAccept_exact]
    case false => rfl
    case true =>
      simp only [Prod.swap]
      cases left : matchTokens (e.1.instantiate (Dictionary.decode h.dictionary).capture).tokens view.2.2 <;>
      cases right : matchTokens (e.2.instantiate (Dictionary.decode h.dictionary).capture).tokens view.2.1 <;>
        simp [view] at left right ⊢ <;> simp [left,right,BEq.comm]

theorem trial_row_mark (h : TrialHeader) (e : Templates.Equation) (s : Scheduler) {output : Store}
    (view : FrontBounds (instructionsEffect (equationInstructions e) (TrieInput s h)) output) :
    finalMark output = h.mark e s.incumbent := by
  let start := TrieInput s h
  have row := row_fronts e start
  let a := scanMatch (e.1.instantiate (Dictionary.decode (start dc)).capture).tokens (start fr)
  let b := scanMatch (e.2.instantiate (Dictionary.decode (start dc)).capture).tokens (start lv)
  have left : output lv = a.rest := view.right.trans row.1
  have right : output fr = b.rest := view.left.trans row.2.1
  have mark : output gues = markedIf (start gues) (a.valid = true ∧ b.valid = true) :=
    view.marker.trans row.2.2.1
  have dict : start dc = h.dictionary := by
    simp [start,TrieInput,Store.set,dc,gues]
  have seed : start gues = markedIf h.proposal ((h.prefix s.incumbent).1 = true) := by
    simp [start,TrieInput,Store.set,gues]
  rw [finalMark,left,right,mark,seed,markedIf_and,markedIf_and,TrialHeader.mark,
    check_after_context]
  have cond : frontsAccept e (Dictionary.decode h.dictionary) (start fr) (start lv) = true ↔
      (a.valid = true ∧ b.valid = true) ∧ b.rest = a.rest := by
    unfold frontsAccept
    rw [← dict]
    change ((a.valid && b.valid && (a.rest == b.rest)) = true) ↔ _
    simp only [Bool.and_eq_true,beq_iff_eq]
    exact and_congr_right (fun _ => eq_comm)
  simp only [Bool.and_eq_true]
  change markedIf h.proposal
      ((h.prefix s.incumbent).1 = true ∧ (a.valid = true ∧ b.valid = true) ∧ b.rest = a.rest) =
    markedIf h.proposal ((h.prefix s.incumbent).1 = true ∧
      frontsAccept e (Dictionary.decode h.dictionary) (start fr) (start lv) = true)
  simp only [cond, and_assoc]

def templateTable : List (List Templates.Instruction) := equations.map equationInstructions

def templateFuel : Nat := templateTable.foldl (fun n line => max n line.length) 0

theorem templateCovered : ∀ line ∈ templateTable, line.length ≤ templateFuel := by
  intro line listed
  have verified : (templateTable.all fun line => decide (line.length ≤ templateFuel)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp verified _ listed)

theorem rows_run (s : Store) (scratch : Scratch s) :
    ∃ e ∈ equations, ∃ t, LineRuns rows s t ∧ Scratch t ∧
      FrontBounds (instructionsEffect (equationInstructions e) s) t ∧ t pl ≤ s pl := by
  obtain ⟨result⟩ := trie_runs templateFuel templateTable s scratch (by decide +kernel) templateCovered
  obtain ⟨e, listed, eq⟩ := List.mem_map.mp result.listed
  exact ⟨e,listed,result.finish,result.executed,result.scratch,eq.symm ▸ result.observed,result.pending⟩

def trialFlow {V : Type} [OfNat V 1] [DecidableEq V] (marker : V) : Flow := if marker = 1 then .halt else .normal

def Scheduler.finish {V : Type} [OfNat V 0] [OfNat V 1] [OfNat V 4]
    [DecidableEq V] [Add V] [Sub V] (s : Scheduler V) (pending marker scratchWord : V) : Scheduler V :=
  ⟨s.begin.index,pending,if marker = 1 then 0 else marker,scratchWord⟩

/-- Finish the body for any selected template. This is shared by the
soundness argument and the construction of a chosen proof stream. -/
theorem finish_trial (s : Scheduler) (e : Templates.Equation) (t : Store)
    (ran : LineRuns rows (TrieInput s.begin (TrialHeader.decode s.begin.pending)) t)
    (ready : Scratch t)
    (view : FrontBounds
      (instructionsEffect (equationInstructions e) (TrieInput s.begin (TrialHeader.decode s.begin.pending))) t) :
    let mark := (TrialHeader.decode s.begin.pending).mark e s.begin.incumbent
    Executes main s.store (trialFlow mark) (s.finish (t pl) mark (t tmp)).store := by
  let h := TrialHeader.decode s.begin.pending
  let first := TrieInput s.begin h
  let mark := h.mark e s.begin.incumbent
  have check : finalMark t = mark := trial_row_mark h e s.begin view
  have semantics := row_fronts e first
  have index : t np = s.begin.index := by
    rw [view.word,semantics.2.2.2.2]
    simp [first,TrieInput,Scheduler.store,Store.set,np,pl,fr,lv,dc,tmp,gues]
  have unused : t 11 = 0 := by
    rw [view.unused, instructions_unused]
    simp [TrieInput,Scheduler.store,Store.set,np,pl,fr,lv,dc,tmp,gues]
  have endRun := run_output t ready unused
  rw [check,index] at endRun
  have assembled := ((run_mainInput s).append ran).append endRun
  change Executes main s.store (trialFlow mark) (s.finish (t pl) mark (t tmp)).store
  by_cases stops : mark = 1
  · have terminal := run_accept_halt s.begin.index (t pl) (t tmp)
    rw [stops] at endRun
    have complete := ((run_mainInput s).append ran).append endRun
    simpa [main,trialFlow,Scheduler.finish,stops,List.append_assoc] using
      complete.finish terminal rfl
  · have continuing := run_accept_continue s.begin.index (t pl) mark (t tmp) stops
    simpa [main,trialFlow,Scheduler.finish,stops,List.append_assoc] using
      assembled.finish continuing rfl

end PalomarI3334.SearchProgram
