module
public import I3_380.Search.Arithmetic.ContextPrograms
@[expose] public section

namespace PalomarI3380.Compiler.Source

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ArithmeticMachine.SourceCantor (decodeLeft decodeRight)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def afterArity (s : Store M) : Store M :=
  (((s.set «exp» (s «exp»-1+1)).set goal (s goal+(s «exp»-1))).set gues
    (if s «exp»=0 then 0 else s gues))

theorem coded_arity (s : Store M) (scratchZero : s u = 0) :
    arity.Runs .normal s.code (afterArity s).code := by
  let raw := s «exp»-1
  let marker := if s «exp»=0 then 0 else s gues
  let stage := (s.set «exp» raw).set gues marker
  have test : (ifZero «exp» (clear gues)).Runs .normal s.code stage.code := by
    by_cases zero : s «exp» = 0
    · have clear := coded_ifZero_zero zero (coded_clear gues s) rfl
      have same : s.set «exp» raw = s := by
        have rawZero : raw = s «exp» := by simp [raw,zero]
        rw [rawZero,Store.set_same]
      simpa only [stage,same,marker,zero,↓reduceIte] using clear
    · have run := coded_ifZero_positive (body := clear gues) zero
      have same : (s.set «exp» raw).set gues marker = s.set «exp» raw := by
        have kept : (s.set «exp» raw) gues = marker := by
          unfold marker
          rw [ite_eq_right zero]
          exact Store.get_set_other _ _ _ _ (by decide)
        rw [← kept,Store.set_same]
      simpa only [stage,same,raw] using run
  have zeroScratch : stage u = 0 := by
    simpa [stage,Store.set,u,gues,«exp»] using scratchZero
  have backup := coded_copy (a := «exp») (b := goal) (by decide) (by decide) (by decide) stage zeroScratch
  have stageExpected : stage «exp» = raw := by simp [stage,Store.set,«exp»,gues]
  have stageGoal : stage goal = s goal := by simp [stage,Store.set,goal,«exp»,gues]
  rw [stageExpected,stageGoal] at backup
  let middle := stage.set goal (s goal+raw)
  have expected : middle «exp» = raw := by
    unfold middle
    rw [Store.get_set_other _ _ _ _ (by decide : «exp» ≠ goal),stageExpected]
  have align : middle.set «exp» (middle «exp»+1) = afterArity s := by
    rw [expected]
    unfold middle stage afterArity
    rw [Store.set_comm _ (by decide : goal ≠ «exp») (s goal+raw) (raw+1),
      Store.set_comm _ (by decide : gues ≠ «exp») marker (raw+1),Store.set_set,
      Store.set_comm _ (by decide : gues ≠ goal) marker (s goal+raw)]
  have inc := coded_increment «exp» middle
  rw [align] at inc
  exact Program.Runs.rightExit test (Program.Runs.rightExit backup inc rfl) rfl

noncomputable def popScanField (s : Store M) : Store M :=
  (s.set tmp (decodeRight (s tmp))).set «exp» (decodeLeft (s tmp))

noncomputable def eatScanField (s : Store M) : Store M :=
  ((s.set fr (decodeRight (s fr))).set «exp» 0).set gues
    (if s «exp»=decodeLeft (s fr) then s gues else 0)

noncomputable def scanStep (s : Store M) : Store M :=
  eatScanField (popScanField (eatScanField (afterArity (popScanField s))))

theorem coded_scanBody (s : Store M) (clean : ContextScratch s) :
    scanBody.Runs .normal s.code (scanStep s).code := by
  let a := popScanField s
  let b := afterArity a
  let c := eatScanField b
  let d := popScanField c
  have first : (pop tmp «exp»).Runs .normal s.code a.code :=
    coded_pop (by decide) (by decide) (by decide) s clean.1 clean.2.2
  have aScratch : a u = 0 := by simpa [a,popScanField,Store.set,u,tmp,«exp»] using clean.2.2
  have second := coded_arity a aScratch
  have bScratch : b u = 0 := by simpa [b,afterArity,Store.set,u,«exp»,goal,gues] using aScratch
  have bToken : b tok = 0 := by
    simpa [b,a,afterArity,popScanField,Store.set,tok,«exp»,goal,gues,tmp] using clean.2.1
  have third : eat.Runs .normal b.code c.code := coded_eat b bToken bScratch
  have cExpected : c «exp» = 0 := by simp [c,eatScanField,Store.set,«exp»,fr,gues]
  have cScratch : c u = 0 := by simpa [c,eatScanField,Store.set,u,fr,«exp»,gues] using bScratch
  have fourth : (pop tmp «exp»).Runs .normal c.code d.code :=
    coded_pop (by decide) (by decide) (by decide) c cExpected cScratch
  have dScratch : d u = 0 := by simpa [d,popScanField,Store.set,u,tmp,«exp»] using cScratch
  have dToken : d tok = 0 := by
    simpa [d,c,popScanField,eatScanField,Store.set,tok,tmp,«exp»,fr,gues] using bToken
  have last := coded_eat d dToken dScratch
  exact Program.Runs.rightExit first
    (Program.Runs.rightExit second (Program.Runs.rightExit third
      (Program.Runs.rightExit fourth last rfl) rfl) rfl) rfl

theorem scanStep_scratch (s : Store M) (clean : ContextScratch s) : ContextScratch (scanStep s) := by
  unfold ContextScratch
  have token := clean.2.1
  have scratch := clean.2.2
  simpa [scanStep,eatScanField,popScanField,afterArity,Store.set,
    «exp»,tmp,fr,gues,goal,tok,u] using And.intro token scratch

theorem scanStep_goal (s : Store M) :
    scanStep s goal = s goal+(decodeLeft (s tmp)-1) := by
  simp [scanStep,eatScanField,popScanField,afterArity,Store.set,«exp»,tmp,fr,gues,goal]

theorem scanStep_dictionary (s : Store M) :
    scanStep s tmp = decodeRight (decodeRight (s tmp)) := by
  simp [scanStep,eatScanField,popScanField,afterArity,Store.set,«exp»,tmp,fr,gues,goal]

open ArithmeticMachine.SourceWords (cons decodeLeft_cons decodeRight_cons)

theorem scanStep_front (s : Store M) :
    scanStep s fr = decodeRight (decodeRight (s fr)) := by
  simp [scanStep,eatScanField,popScanField,afterArity,Store.set,«exp»,tmp,fr,gues,goal]

theorem scanStep_marker_shared (s : Store M) (a t dictionary front : M)
    (inDictionary : s tmp = cons a t dictionary) (atFront : s fr = cons a t front) :
    scanStep s gues = s gues := by
  simp only [tmp,fr] at inDictionary atFront
  have head : 0 < a+1 := by simp
  have code : (a+1)-1 = a := by simp
  have marker : (a+1 : M) ≠ 0 := head.ne'
  have dictionaryFields := (ArithmeticMachine.SourceCantor.decode_pairValue t dictionary)
  have frontFields := (ArithmeticMachine.SourceCantor.decode_pairValue t front)
  simp [scanStep,eatScanField,popScanField,afterArity,Store.set,«exp»,tmp,fr,gues,goal,
    inDictionary,atFront,decodeLeft_cons,decodeRight_cons,code,marker,dictionaryFields.1,frontFields.1]

end PalomarI3380.Compiler.Source
