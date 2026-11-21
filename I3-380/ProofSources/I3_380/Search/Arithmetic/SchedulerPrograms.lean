module
public import I3_380.Search.Arithmetic.TrieCover
public import I3_380.Search.Compiler.SchedulerState
@[expose] public section

namespace PalomarI3380.Compiler.Source

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open ArithmeticMachine.SourceCantor (pairValue decodeLeft decodeRight decode_pairValue)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem SchedulerState.index_read {V : Type} [OfNat V 0] (s : SchedulerState V) :
    s.store np = s.nextWord := by simp [store,Store.set,np,pl,goal]

theorem SchedulerState.pending_read {V : Type} [OfNat V 0] (s : SchedulerState V) :
    s.store pl = s.pending := by simp [store,Store.set,pl,goal]

theorem SchedulerState.current_read {V : Type} [OfNat V 0] (s : SchedulerState V) :
    s.store goal = s.current := Store.get_set ..

theorem coded_resetTask (s : Store M) (scratch : s u=0) (pending : s pl=0) :
    resetTask.Runs .normal s.code (((s.set pl (s np)).set np (s np+1)).set goal 4).code := by
  let first := s.set pl (s np)
  let second := first.set np (s np+1)
  let cleared := second.set goal 0
  have copyRun := coded_copy (a := np) (b := pl) (by decide) (by decide) (by decide) s scratch
  rw [pending,zero_add] at copyRun
  have increase := coded_increment np first
  rw [show first np = s np from Store.get_set_other _ _ _ _ (by decide)] at increase
  have clearGoal := coded_clear goal second
  have load := (coded_increments 4 goal cleared).block
  rw [show cleared goal = 0 from Store.get_set ..,zero_add] at load
  change (block (List.replicate 4 (inc goal))).Runs .normal cleared.code ((second.set goal 0).set goal 4).code at load
  rw [Store.set_set] at load
  exact .rightExit copyRun (.rightExit increase (.rightExit clearGoal load rfl) rfl) rfl

theorem coded_begin (s : SchedulerState M) :
    (ifZero pl resetTask).Runs .normal s.store.code s.begin.store.code := by
  by_cases empty : s.pending=0
  · have ready : s.store u=0 := by simp [SchedulerState.store,emptyStore,Store.set,u,np,pl,goal]
    have start := coded_resetTask s.store ready (s.pending_read.trans empty)
    rw [s.index_read] at start
    have same : (((s.store.set pl s.nextWord).set np (s.nextWord+1)).set goal 4) = s.begin.store := by
      apply store_ext <;>
        simp [SchedulerState.begin,empty,SchedulerState.store,emptyStore,Store.set,np,pl,goal]
    rw [same] at start
    exact coded_ifZero_zero (s.pending_read.trans empty) start rfl
  · have positive := coded_ifZero_positive (r := pl) (body := resetTask) (s := s.store) (by simpa only [s.pending_read] using empty)
    rw [s.pending_read] at positive
    have same : s.store.set pl (s.pending-1) = s.begin.store := by
      simp only [SchedulerState.begin,empty,↓reduceIte,SchedulerState.store]
      rw [Store.set_comm _ (by decide : goal ≠ pl),Store.set_set]
    exact same ▸ positive

noncomputable def TrialInput.modelDecode (word : M) : TrialInput M :=
  let p := decodeRight word
  let o := decodeRight p
  let d := decodeRight o
  ⟨decodeLeft word,decodeLeft p,decodeLeft o,decodeLeft d,decodeRight d⟩

noncomputable def TrialInput.modelEncode (trial : TrialInput M) : M :=
  pairValue trial.proposal (pairValue trial.position (pairValue trial.orientation
    (pairValue trial.dictionary trial.pending)))

theorem TrialInput.modelDecode_encode (trial : TrialInput M) :
    modelDecode trial.modelEncode = trial := by
  cases trial
  simp only [modelDecode,modelEncode,(decode_pairValue _ _).1,(decode_pairValue _ _).2]

theorem TrialInput.modelDecode_pending_le (word : M) :
    (modelDecode word).pending ≤ word :=
  ((ArithmeticMachine.SourceCantor.decodeValue_bounds _).2.trans
    (ArithmeticMachine.SourceCantor.decodeValue_bounds _).2).trans
    ((ArithmeticMachine.SourceCantor.decodeValue_bounds _).2.trans
      (ArithmeticMachine.SourceCantor.decodeValue_bounds _).2)

noncomputable def TrialInput.prefixStore (c : TrialInput M) (s : SchedulerState M) : Store M :=
  (stageStore s (decodeRight (decodeRight s.pending)) s.current c.proposal c.proposal 0).set sel c.position

theorem TrialInput.prefixScratch (c : TrialInput M) (s : SchedulerState M) :
    ContextScratch (c.prefixStore s) := by
  have h := (stageStore_scratch s (decodeRight (decodeRight s.pending)) s.current c.proposal c.proposal 0).setSel c.position
  exact h.context

/-- Load the current word and the proposed word before scanning their
common context. The remaining field stream stays in the pending register. -/
theorem coded_input_prefix (s : SchedulerState M) :
    let a := s.begin
    let c := TrialInput.modelDecode a.pending
    CodedLines [ifZero pl resetTask,read gues,copy gues lv,move goal fr,read sel]
      s.store.code (c.prefixStore a).code := by
  dsimp only
  let a := s.begin
  let c := TrialInput.modelDecode a.pending
  let loaded := (a.store.set pl (decodeRight a.pending)).set gues c.proposal
  let copied := loaded.set lv c.proposal
  let moved := (copied.set goal 0).set fr a.current
  have load := coded_read (dst := gues) (by decide) (by decide) a.store
    (by simp [SchedulerState.store,emptyStore,Store.set,np,pl,goal,tok])
    (by simp [SchedulerState.store,emptyStore,Store.set,np,pl,goal,u])
  have marker : a.store gues = 0 := by simp [SchedulerState.store,emptyStore,Store.set,np,pl,goal,gues]
  have load' : (read gues).Runs .normal a.store.code loaded.code := by
    simpa only [a.pending_read,marker,zero_add,loaded,c,TrialInput.modelDecode] using load
  have copyRun := coded_copy (a := gues) (b := lv) (by decide) (by decide) (by decide) loaded
    (by simp [loaded,SchedulerState.store,emptyStore,Store.set,np,pl,goal,u,gues])
  have copy' : (copy gues lv).Runs .normal loaded.code copied.code := by
    have back : loaded lv=0 := by simp [loaded,SchedulerState.store,emptyStore,Store.set,np,pl,goal,lv,gues]
    simpa only [back,zero_add,show loaded gues = c.proposal from Store.get_set ..,copied] using copyRun
  have moveRun := coded_move (a := goal) (b := fr) (by decide) copied
  have frZero : copied fr=0 := by
    simp [copied,loaded,SchedulerState.store,emptyStore,Store.set,np,pl,goal,fr,lv,gues]
  have current : copied goal=a.current := by
    simp [copied,loaded,SchedulerState.store,Store.set,pl,goal,lv,gues]
  have move' : (move goal fr).Runs .normal copied.code moved.code := by
    simpa only [frZero,current,zero_add,moved] using moveRun
  have loadPos := coded_read (dst := sel) (by decide) (by decide) moved
    (by simp [moved,copied,loaded,SchedulerState.store,emptyStore,Store.set,np,pl,goal,fr,lv,gues,tok])
    (by simp [moved,copied,loaded,SchedulerState.store,emptyStore,Store.set,np,pl,goal,fr,lv,gues,u])
  have result : (moved.set pl (decodeRight (moved pl))).set sel
      (moved sel + decodeLeft (moved pl)) = c.prefixStore a := by
    apply store_ext <;>
      simp [moved,copied,loaded,TrialInput.prefixStore,c,TrialInput.modelDecode,stageStore,
        SchedulerState.store,emptyStore,Store.set,np,pl,goal,fr,lv,gues,dc,sel]
  rw [result] at loadPos
  exact .cons (coded_begin s) (.cons load' (.cons copy' (.cons move' (.cons loadPos (.nil _)))))

noncomputable def TrialInput.modelPrepare (c : TrialInput M) (s : SchedulerState M) (a b marker : M) : Store M :=
  if c.orientation=0 then stageStore s c.pending a b marker c.dictionary
  else stageStore s c.pending b a marker c.dictionary

theorem TrialInput.modelPrepare_scratch (c : TrialInput M) (s : SchedulerState M) (a b marker : M) :
    ClearScratch (c.modelPrepare s a b marker) := by
  unfold modelPrepare
  split <;> exact stageStore_scratch _ _ _ _ _ _

theorem TrialInput.modelPrepare_selector (c : TrialInput M) (s : SchedulerState M) (a b marker : M) :
    c.modelPrepare s a b marker sel=0 := by
  unfold modelPrepare
  split <;> simp [stageStore,SchedulerState.store,emptyStore,Store.set,np,pl,goal,fr,lv,gues,dc,sel]

theorem TrialInput.modelPrepare_pending (c : TrialInput M) (s : SchedulerState M) (a b marker : M) :
    c.modelPrepare s a b marker pl=c.pending := by
  unfold modelPrepare
  split <;> simp [stageStore,SchedulerState.store,Store.set,pl,goal,fr,lv,gues,dc]

/-- Complete the four field reads after the context scan. The direction
field selects the order of the two suffixes. -/
theorem coded_input_suffix (s : SchedulerState M) (a b marker : M) :
    let c := TrialInput.modelDecode s.pending
    CodedLines [read sel,ifPositive sel side,clear sel,read dc]
      (contextState (c.prefixStore s) 0 a b marker).code (c.modelPrepare s a b marker).code := by
  dsimp only
  let c := TrialInput.modelDecode s.pending
  let before := contextState (c.prefixStore s) 0 a b marker
  let readOrientation := controls before (decodeRight (before pl)) c.orientation
  let source := readOrientation.set sel (c.orientation-1)
  let swapped := (source.set fr (source lv)).set lv (source fr)
  let oriented := if c.orientation=0 then readOrientation else swapped
  let erased := oriented.set sel 0
  have readRun := coded_read (dst := sel) (by decide) (by decide) before
    (by simpa [before,contextState,replaceContext,Store.set,fr,lv,gues,sel,tok] using (c.prefixScratch s).2.1)
    (by simpa [before,contextState,replaceContext,Store.set,fr,lv,gues,sel,u] using (c.prefixScratch s).2.2)
  have read' : (read sel).Runs .normal before.code readOrientation.code := by
    have selector : before sel=0 := by simp [before,contextState,replaceContext,Store.set,fr,lv,gues,sel]
    have orientation : decodeLeft (before pl)=c.orientation := by
      simp [before,contextState,replaceContext,TrialInput.prefixStore,stageStore,c,TrialInput.modelDecode,
        SchedulerState.store,Store.set,pl,goal,fr,lv,gues,dc,sel]
    simpa only [selector,zero_add,orientation,readOrientation,controls] using readRun
  have side' : (ifPositive sel side).Runs .normal readOrientation.code oriented.code := by
    by_cases forward : c.orientation=0
    · have zero : readOrientation sel=0 := (controls_sel ..).trans forward
      simpa only [oriented,forward,↓reduceIte,ifPositive,swapped] using
        (Program.Runs.leftExit (q := side) (coded_decrement_zero zero) (by rfl))
    · have nonzero : readOrientation sel≠0 := by simpa only [readOrientation,controls_sel] using forward
      have decreased := coded_decrement_positive nonzero
      have temp : source tmp=0 := by
        simp [source,readOrientation,controls,before,contextState,replaceContext,TrialInput.prefixStore,
          stageStore,SchedulerState.store,emptyStore,Store.set,tmp,gues,lv,fr,sel,pl,goal,np,dc]
      rw [show readOrientation sel=c.orientation from controls_sel ..] at decreased
      simpa only [oriented,forward,↓reduceIte,ifPositive,swapped] using
        (Program.Runs.rightExit decreased (coded_side source temp) (by rfl))
  have clearRun := coded_clear sel oriented
  have token : erased tok=0 := by
    by_cases f : c.orientation=0 <;>
      simp [erased,oriented,f,swapped,source,readOrientation,controls,before,contextState,replaceContext,
        TrialInput.prefixStore,stageStore,SchedulerState.store,emptyStore,Store.set,tok,gues,lv,fr,sel,pl,goal,np,dc]
  have aux : erased u=0 := by
    by_cases f : c.orientation=0 <;>
      simp [erased,oriented,f,swapped,source,readOrientation,controls,before,contextState,replaceContext,
        TrialInput.prefixStore,stageStore,SchedulerState.store,emptyStore,Store.set,u,gues,lv,fr,sel,pl,goal,np,dc]
  have dict := coded_read (dst := dc) (by decide) (by decide) erased token aux
  have result : (erased.set pl (decodeRight (erased pl))).set dc (erased dc+decodeLeft (erased pl)) =
      c.modelPrepare s a b marker := by
    by_cases f : c.orientation=0 <;>
      simp only [erased,oriented,TrialInput.modelPrepare,f,↓reduceIte] <;>
      apply store_ext <;>
      simp [swapped,source,readOrientation,controls,before,contextState,replaceContext,
        TrialInput.prefixStore,TrialInput.modelPrepare,stageStore,SchedulerState.store,emptyStore,
        Store.set,np,pl,goal,fr,lv,gues,dc,sel,c,TrialInput.modelDecode] <;> rfl
  rw [result] at dict
  exact .cons read' (.cons side' (.cons clearRun (.cons dict (.nil _))))

theorem coded_input (s : SchedulerState M) (a b marker : M)
    (scan : let c := TrialInput.modelDecode s.begin.pending
      contextScan.Runs .normal (c.prefixStore s.begin).code (contextState (c.prefixStore s.begin) 0 a b marker).code) :
    let c := TrialInput.modelDecode s.begin.pending
    CodedLines mainInput s.store.code (c.modelPrepare s.begin a b marker).code :=
  (coded_input_prefix s).append (.cons scan (coded_input_suffix s.begin a b marker))

theorem coded_input_total (s : SchedulerState M) :
    ∃ a b marker, let c := TrialInput.modelDecode s.begin.pending
      CodedLines mainInput s.store.code (c.modelPrepare s.begin a b marker).code := by
  let c := TrialInput.modelDecode s.begin.pending
  obtain ⟨a,b,marker,scan⟩ := coded_contextScan_total (c.prefixStore s.begin) (c.prefixScratch s.begin)
  exact ⟨a,b,marker,coded_input s a b marker scan⟩

end PalomarI3380.Compiler.Source
