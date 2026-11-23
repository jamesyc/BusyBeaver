module
public import I3_334.Calibration.ModelContext
public import I3_334.Calibration.ModelTrie
public import I3_334.Search.TrialInput
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (CodedLines inc clear ifZero coded_clear coded_increment
  coded_ifZero_positive coded_ifZero_zero coded_transfer increase)
open ArithmeticMachine.SourceCantor
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem modelScratch (s : Scheduler M) : Scratch s.store := by
  refine ⟨?_,?_,?_⟩ <;> simp [Scheduler.store,Store.set,np,pl,fr,tmp,expected,tok,u]

theorem coded_restart (s : Scheduler M) (empty : s.pending = 0) :
    restart.Runs .normal s.store.code (Scheduler.mk (s.index+1) s.index 4 s.scratchWord).store.code := by
  let copied := s.store.set pl (s.store pl + s.store np)
  let bumped := copied.set np (copied np + 1)
  let cleared := bumped.set fr 0
  have first : (copy np pl).Runs .normal s.store.code copied.code :=
    coded_copy (by decide) (by decide) (by decide) s.store (modelScratch s).auxiliaryEmpty
  have sequence : CodedLines [copy np pl,inc np,clear fr] s.store.code cleared.code :=
    .cons first (.cons (coded_increment np copied) (.cons (coded_clear fr bumped) (.nil _)))
  have raised := coded_increments fr 4 cleared
  have result : cleared.set fr (cleared fr+(4 : Nat)) =
      (Scheduler.mk (s.index+1) s.index 4 s.scratchWord).store := by
    funext r
    by_cases a : r = np <;> by_cases b : r = pl <;> by_cases c : r = fr <;>
      by_cases d : r = tmp <;>
      simp [cleared,bumped,copied,Scheduler.store,Store.set,a,b,c,d,np,pl,fr,tmp,empty]
  rw [result] at raised
  exact (sequence.append raised).block

theorem coded_begin (s : Scheduler M) :
    (ifZero pl restart).Runs .normal s.store.code s.begin.store.code := by
  have queue : s.store pl = s.pending := by simp [Scheduler.store,Store.set,pl,tmp,fr,np]
  by_cases empty : s.pending = 0
  · simpa only [Scheduler.begin,empty,↓reduceIte] using
      coded_ifZero_zero (queue.trans empty) (coded_restart s empty) (out := .normal) rfl
  · have run := coded_ifZero_positive (s := s.store) (r := pl) (body := restart) (by rwa [queue])
    have out : s.store.set pl (s.store pl-1) = s.begin.store := by
      funext r
      by_cases a : r = np <;> by_cases b : r = pl <;> by_cases c : r = fr <;>
        by_cases d : r = tmp <;> simp [Scheduler.begin,empty,Scheduler.store,Store.set,
          a,b,c,d,np,pl,fr,tmp,queue]
    rwa [out] at run

noncomputable def modelProduce (s : Store M) : Store M :=
  ((s.set pl (decodeRight (s pl))).set gues (decodeLeft (s pl))).set lv (decodeLeft (s pl))

theorem coded_produce (s : Store M) (ready : Scratch s) (zeroGuess : s gues = 0) (zeroBack : s lv = 0) :
    produce.Runs .normal s.code (modelProduce s).code := by
  let a := decodeLeft (s pl)
  let b := decodeRight (s pl)
  let mid := (s.set pl b).set tok a
  have split := coded_pop (src := pl) (dst := tok) (by decide) (by decide) (by decide) s
    ready.tokenEmpty ready.auxiliaryEmpty
  have move := coded_transfer tok [gues,lv] (by decide) (by decide) mid
  have selected : (increase [gues,lv] mid (mid tok)).set tok 0 = modelProduce s := by
    funext r
    by_cases p : r = pl <;> by_cases f : r = gues <;> by_cases h : r = lv <;>
      by_cases c : r = tok <;>
      simp [increase,modelProduce,mid,a,b,Store.set,p,f,h,c,pl,gues,lv,tok,
        ready.tokenEmpty,zeroGuess,zeroBack]
  rw [selected] at move
  exact Program.Runs.rightExit split move rfl

theorem model_context_front (s : Store M) (a b g : M) (ready : Scratch s) :
    CodedFront s (contextState s 0 a b g) := by
  refine ⟨?_,?_,?_,?_⟩ <;>
    simp [contextState,replaceFronts,Scratch.iff_fields,Store.set,goal,fr,lv,gues,np,pl,expected,tok,u,
      ready.expectedEmpty,ready.tokenEmpty,ready.auxiliaryEmpty]

theorem coded_trialInput_total (s : Scheduler M) :
    ∃ t, CodedLines [ifZero pl restart,produce,read goal,contextScan,read dc] s.store.code t.code ∧
      CodedFront s.begin.store t := by
  let staged := s.begin.store
  let proposal := modelProduce staged
  let loaded := (proposal.set pl (decodeRight (proposal pl))).set goal
    (proposal goal+decodeLeft (proposal pl))
  have produce := coded_produce staged (modelScratch s.begin)
    (by simp [staged,Scheduler.store,Store.set,np,pl,fr,tmp,gues])
    (by simp [staged,Scheduler.store,Store.set,np,pl,fr,tmp,lv])
  have ready₁ : Scratch proposal := by
    refine ⟨?_,?_,?_⟩ <;>
      simp [proposal,modelProduce,staged,Scheduler.store,Store.set,np,pl,fr,tmp,gues,lv,expected,tok,u]
  have readGoal := coded_read (dst := goal) (by decide) (by decide) proposal ready₁.tokenEmpty ready₁.auxiliaryEmpty
  have ready₂ : Scratch loaded := by
    simpa [Scratch.iff_fields,loaded,Store.set,pl,goal,expected,tok,u] using Scratch.iff_fields.mp ready₁
  obtain ⟨a,b,g,context⟩ := coded_context_total loaded ready₂
  let compared := contextState loaded 0 a b g
  have ready₃ := (model_context_front loaded a b g ready₂).scratch
  have readDict := coded_read (dst := dc) (by decide) (by decide) compared ready₃.tokenEmpty ready₃.auxiliaryEmpty
  let final := (compared.set pl (decodeRight (compared pl))).set dc
    (compared dc + decodeLeft (compared pl))
  have ready : Scratch final := by
    simpa [Scratch.iff_fields,final,Store.set,pl,dc,expected,tok,u] using Scratch.iff_fields.mp ready₃
  have pending₁ : proposal pl ≤ staged pl := by
    simpa [modelProduce,proposal,Store.set,pl,lv,gues] using (decodeValue_bounds (staged pl)).2
  have pending₂ : loaded pl ≤ proposal pl := by
    simpa [loaded,Store.set,pl,goal] using (decodeValue_bounds (proposal pl)).2
  have pending₃ : final pl ≤ compared pl := by
    simpa [final,Store.set,pl,dc] using (decodeValue_bounds (compared pl)).2
  have index : final np = staged np := by
    simp [final,compared,contextState,replaceFronts,loaded,proposal,modelProduce,
      Store.set,np,pl,dc,goal,fr,lv,gues]
  have unused : final 11 = staged 11 := by
    simp [final,compared,contextState,replaceFronts,loaded,proposal,modelProduce,
      Store.set,np,pl,dc,goal,fr,lv,gues]
  exact ⟨final,.cons (coded_begin s) (.cons produce (.cons readGoal (.cons context (.cons readDict (.nil _))))),
    ready,index,pending₃.trans ((model_context_front loaded a b g ready₂).pending.trans
      (pending₂.trans pending₁)),unused⟩

end PalomarI3334.SearchProgram
