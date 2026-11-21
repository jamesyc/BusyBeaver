module
public import I3_380.Calibration.CodedPatternMatching
public import I3_380.Search.Arithmetic.TrialPrograms
@[expose] public section

namespace PalomarI3380.Calibration.TermWords

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open PalomarI3380.Compiler PalomarI3380.Compiler.Source
open scoped FFL.FirstOrder.Arithmetic
open ArithmeticMachine.SourceWords (emitVector)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem coded_side_trace (s : Store M) (ready : ClearScratch s) :
    CodedPatternTrace [.side] s (replaceContext s (s lv) (s fr) (s gues)) := by
  refine .cons (fun p r => ?_) (ready.context_state _ _ _) (.nil _)
  let start := controls s p r
  have run := coded_side start (ready.controls p r).tempZero
  have output : (start.set fr (start lv)).set lv (start fr) =
      controls (replaceContext s (s lv) (s fr) (s gues)) p r := by
    rw [← replaceContext_controls]
    change (start.set fr (start lv)).set lv (start fr) = replaceContext start (s lv) (s fr) (s gues)
    have front : start fr=s fr := by simp [start,controls,Store.set,fr,pl,sel]
    have back : start lv=s lv := by simp [start,controls,Store.set,lv,pl,sel]
    have marker : start gues=s gues := by simp [start,controls,Store.set,gues,pl,sel]
    rw [← front,← back,← marker]
    unfold replaceContext
    let next := (start.set fr (start lv)).set lv (start fr)
    have same : next gues = start gues := by simp [next,Store.set,gues,fr,lv]
    change next = next.set gues (start gues)
    rw [← same,Store.set_same]
  rw [output] at run
  exact run

theorem coded_row_match (e : Equation) (args : Fin 3 → GroundTerm M) (s : Store M) (suffix : M)
    (ready : ClearScratch s) (dict : s dc=termDictionary args)
    (left : s fr = emitVector (termTokens (groundAlgebra.eval args e.1).val) suffix)
    (right : s lv = emitVector (termTokens (groundAlgebra.eval args e.2).val) suffix) :
    CodedPatternTrace (rowPattern e) s (replaceContext s suffix suffix (s gues)) := by
  let leftEnd := s.set fr suffix
  have leftRead := coded_term_pattern args e.1 s suffix ready dict left
  have leftReady := front_ready ready suffix
  have swap := coded_side_trace leftEnd leftReady
  let rightStart := replaceContext leftEnd (leftEnd lv) (leftEnd fr) (leftEnd gues)
  have rightReady : ClearScratch rightStart := leftReady.context_state _ _ _
  have dictRight : rightStart dc = termDictionary args := by
    simpa [rightStart,leftEnd,replaceContext,Store.set,dc,fr,lv,gues] using dict
  have wordRight : rightStart fr = emitVector (termTokens (groundAlgebra.eval args e.2).val) suffix := by
    simpa [rightStart,leftEnd,replaceContext,Store.set,fr,lv,gues] using right
  have rightRead := coded_term_pattern args e.2 rightStart suffix rightReady dictRight wordRight
  have done : rightStart.set fr suffix = replaceContext s suffix suffix (s gues) := by
    funext r
    by_cases f : r=fr <;> by_cases l : r=lv <;> by_cases g : r=gues <;>
      simp_all [rightStart,leftEnd,replaceContext,Store.set,fr,lv,gues] <;> rfl
  rw [done] at rightRead
  exact (leftRead.trans swap).trans rightRead

theorem coded_shared_input (s : SchedulerState M) (c : TrialInput M) (ctx : Context M) (a b : M)
    (encoded : s.begin.pending = c.modelEncode)
    (pos : c.position = len ctx.before)
    (old : s.begin.current = emitVector (ctx.fill a) 0)
    (proposal : c.proposal = emitVector (ctx.fill b) 0) :
    CodedLines mainInput s.store.code
      (c.modelPrepare s.begin (emitVector a (emitVector ctx.after 0))
        (emitVector b (emitVector ctx.after 0)) c.proposal).code := by
  have decode : TrialInput.modelDecode s.begin.pending = c :=
    (congrArg TrialInput.modelDecode encoded).trans c.modelDecode_encode
  let p := c.prefixStore s.begin
  have count : p sel = len ctx.before := (Store.get_set ..).trans pos
  have first : p fr = emitVector ctx.before (emitVector a (emitVector ctx.after 0)) := by
    have frEq : p fr = s.begin.current := by
      simp [p,TrialInput.prefixStore,stageStore,Store.set,fr,lv,gues,dc,sel]
    rw [frEq,old,ctx.fill_word]
  have second : p lv = emitVector ctx.before (emitVector b (emitVector ctx.after 0)) := by
    have lvEq : p lv = c.proposal := by
      simp [p,TrialInput.prefixStore,stageStore,Store.set,lv,gues,dc,sel]
    rw [lvEq,proposal,ctx.fill_word]
  have marker : p gues = c.proposal := by
    simp [p,TrialInput.prefixStore,stageStore,Store.set,gues,dc,sel]
  have scan := coded_contextScan_shared p (c.prefixScratch s.begin) ctx.before _ _ count first second
  rw [marker] at scan
  exact (show CodedLines mainInput s.store.code _ from by
    have input := coded_input s (emitVector a (emitVector ctx.after 0))
      (emitVector b (emitVector ctx.after 0)) c.proposal
    simp only [decode] at input
    exact input scan)

theorem coded_rewrite_instance {e : Equation} (inRows : e ∈ rows) (args : Fin 3 → GroundTerm M)
    (ctx : Context M) (reverse : Bool) :
    ∃ fields : List Nat, ∀ (s : SchedulerState M) (tail : M),
      let a := termTokens (groundAlgebra.eval args e.1).val
      let b := termTokens (groundAlgebra.eval args e.2).val
      let current := emitVector (ctx.fill (if reverse then b else a)) 0
      let proposal := emitVector (ctx.fill (if reverse then a else b)) 0
      let c : TrialInput M := ⟨proposal,len ctx.before,if reverse then 1 else 0,
        termDictionary args,modelFields fields tail⟩
      s.begin.pending = c.modelEncode → s.begin.current = current →
      main.Runs (if proposal=1 then .halt else .normal) s.store.code
        (SchedulerState.mk s.begin.nextWord tail (if proposal=1 then 0 else proposal)).store.code := by
  obtain ⟨fields,cover⟩ := coded_rows_cover (M := M) inRows
  refine ⟨fields,fun s tail => ?_⟩
  dsimp only
  let a := termTokens (groundAlgebra.eval args e.1).val
  let b := termTokens (groundAlgebra.eval args e.2).val
  let rest := emitVector ctx.after 0
  let current := emitVector (ctx.fill (if reverse then b else a)) 0
  let proposal := emitVector (ctx.fill (if reverse then a else b)) 0
  let c : TrialInput M := ⟨proposal,len ctx.before,if reverse then 1 else 0,termDictionary args,modelFields fields tail⟩
  intro encoded old
  have pre := coded_shared_input s c ctx (if reverse then b else a) (if reverse then a else b)
    encoded rfl old rfl
  let start := stageStore s.begin 0 (emitVector a rest) (emitVector b rest) proposal (termDictionary args)
  let final := replaceContext start rest rest proposal
  have compare : c.modelPrepare s.begin (emitVector (if reverse then b else a) rest)
      (emitVector (if reverse then a else b) rest) c.proposal = controls start (modelFields fields tail) 0 := by
    cases reverse <;> apply store_ext <;>
      simp [c,TrialInput.modelPrepare,start,controls,stageStore,SchedulerState.store,emptyStore,Store.set,
        np,pl,goal,fr,lv,gues,dc,sel]
  rw [compare] at pre
  have ready : ClearScratch start := stageStore_scratch .. 
  have trace : CodedPatternTrace (rowPattern e) start final := by
    have marker : start gues=proposal := by simp [start,stageStore,Store.set,gues,dc]
    unfold final
    rw [← marker]
    apply coded_row_match e args start rest ready <;>
      simp [start,stageStore,Store.set,fr,lv,gues,dc,a,b]
  have afterReady : ClearScratch final := ready.context_state _ _ _
  have through := cover start final tail ready trace afterReady
  have run := coded_trial s pre through (afterReady.controls tail 0)
  have marker : remainingMarker (controls final tail 0) = proposal := by
    simp [remainingMarker,mark,final,controls,replaceContext,Store.set,fr,lv,gues,pl,sel]
  have npRead : controls final tail 0 np=s.begin.nextWord := by
    simp [final,start,controls,replaceContext,stageStore,SchedulerState.store,Store.set,np,pl,goal,fr,lv,gues,dc,sel]
  simpa only [marker,npRead,controls_pl] using run

end PalomarI3380.Calibration.TermWords
