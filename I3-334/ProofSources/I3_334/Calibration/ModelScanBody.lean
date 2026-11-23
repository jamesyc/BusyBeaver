module
public import I3_334.Calibration.ModelDictionary
public import I3_334.Search.SearchScan
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (CodedLines inc coded_increment)
open ArithmeticMachine.SourceCantor
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def modelConsume (s : Store M) : Store M :=
  ((s.set fr (decodeRight (s fr))).set expected 0).set gues
    (if s expected = decodeLeft (s fr) then s gues else 0)

noncomputable def modelScanStep (slot : Fin 4) (s : Store M) : Store M :=
  let a := decodeLeft (s tmp)
  let tag := decodeLeft (decodeRight (s tmp))
  let dict := decodeRight (decodeRight (s tmp))
  let first := decodeLeft (s fr)
  let next := decodeLeft (decodeRight (s fr))
  let front := decodeRight (decodeRight (s fr))
  (((s.set goal (s goal+a)).set tmp dict).set fr front).set gues
    (if a+1 = first ∧ tag+(bias slot : M) = next then s gues else 0)

/-- A coded pass uses the exact same reversed-dictionary fields and the
same offset as the literal scan. -/
theorem coded_scanBody (slot : Fin 4) (s : Store M) (clean : Scratch s) :
    (scanBody slot).Runs .normal s.code (modelScanStep slot s).code := by
  let a := decodeLeft (s tmp)
  let rest := decodeRight (s tmp)
  let tag := decodeLeft rest
  let dictionary := decodeRight rest
  let first := (s.set tmp rest).set expected a
  let second := first.set goal (first goal + first expected)
  let third := second.set expected (second expected + 1)
  let fourth := modelConsume third
  let fifth := (fourth.set tmp dictionary).set expected tag
  let sixth := fifth.set expected (fifth expected + (bias slot : M))
  have r₁ : (pop tmp expected).Runs .normal s.code first.code :=
    coded_pop (by decide) (by decide) (by decide) s clean.expectedEmpty clean.auxiliaryEmpty
  have r₂ : (copy expected goal).Runs .normal first.code second.code :=
    coded_copy (by decide) (by decide) (by decide) first
      (by simpa [first,Store.set,tmp,expected,u] using clean.auxiliaryEmpty)
  have r₃ : (inc expected).Runs .normal second.code third.code := coded_increment _ _
  have r₄ : eat.Runs .normal third.code fourth.code :=
    coded_eat third
      (by simpa [third,second,first,Store.set,goal,expected,tmp,tok] using clean.tokenEmpty)
      (by simpa [third,second,first,Store.set,goal,expected,tmp,u] using clean.auxiliaryEmpty)
  have remaining : fourth tmp = rest := by
    simp [fourth,modelConsume,third,second,first,Store.set,tmp,expected,goal,fr,gues]
  have r₅ : (pop tmp expected).Runs .normal fourth.code fifth.code := by
    have run := coded_pop (src := tmp) (dst := expected) (by decide) (by decide) (by decide) fourth
      (by simp [fourth,modelConsume,Store.set,expected,gues])
      (by simpa [fourth,modelConsume,third,second,first,Store.set,goal,expected,tmp,u,fr,gues]
        using clean.auxiliaryEmpty)
    simpa only [remaining] using run
  have r₆ : CodedLines (List.replicate (bias slot) (inc expected)) fifth.code sixth.code :=
    coded_increments expected (bias slot) fifth
  have r₇ : eat.Runs .normal sixth.code (modelConsume sixth).code :=
    coded_eat sixth
      (by simpa [sixth,fifth,fourth,modelConsume,third,second,first,Store.set,goal,expected,tmp,tok,fr,gues]
        using clean.tokenEmpty)
      (by simpa [sixth,fifth,fourth,modelConsume,third,second,first,Store.set,goal,expected,tmp,u,fr,gues]
        using clean.auxiliaryEmpty)
  have lines : CodedLines ([pop tmp expected,copy expected goal,inc expected,eat,pop tmp expected] ++
      List.replicate (bias slot) (inc expected) ++ [eat]) s.code (modelConsume sixth).code :=
    (CodedLines.cons r₁ (.cons r₂ (.cons r₃ (.cons r₄ (.cons r₅ (.nil _)))))).append r₆ |>.append
      (.cons r₇ (.nil _))
  have result : modelConsume sixth = modelScanStep slot s := by
    funext i
    by_cases ex : i = expected <;> by_cases mark : i = gues <;> by_cases f : i = fr <;>
      by_cases t : i = tmp <;> by_cases p : i = goal <;>
      simp [modelScanStep,modelConsume,first,second,third,fourth,fifth,sixth,
        a,rest,tag,dictionary,Store.set,ex,mark,f,t,p,expected,gues,fr,tmp,goal,clean.expectedEmpty]
    all_goals
      by_cases fa : decodeLeft (s tmp) + 1 = decodeLeft (s fr) <;>
      by_cases ft : decodeLeft (decodeRight (s tmp))+(bias slot : M) = decodeLeft (decodeRight (s fr)) <;>
        simp [fa,ft]
  rw [result] at lines
  exact lines.block

theorem modelScanStep_scratch (slot : Fin 4) (s : Store M) (clean : Scratch s) :
    Scratch (modelScanStep slot s) := by
  refine ⟨?_,?_,?_⟩ <;>
    simp [modelScanStep,Store.set,goal,tmp,fr,gues,expected,tok,u,
      clean.expectedEmpty,clean.tokenEmpty,clean.auxiliaryEmpty]

theorem modelScanStep_goal (slot : Fin 4) (s : Store M) :
    modelScanStep slot s goal = s goal+decodeLeft (s tmp) := by
  simp [modelScanStep,Store.set,goal,fr,tmp,gues]

theorem modelScanStep_tmp (slot : Fin 4) (s : Store M) :
    modelScanStep slot s tmp = decodeRight (decodeRight (s tmp)) := by
  simp [modelScanStep,Store.set,goal,fr,tmp,gues]

theorem modelScanStep_fr (slot : Fin 4) (s : Store M) :
    modelScanStep slot s fr = decodeRight (decodeRight (s fr)) := by
  simp [modelScanStep,Store.set,goal,fr,tmp,gues]

theorem modelScanStep_preserves (slot : Fin 4) (s : Store M) (i : Register)
    (immutable : i ∉ [goal,tmp,fr,gues]) : modelScanStep slot s i = s i := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at immutable
  simp [modelScanStep,Store.set,immutable.1,immutable.2.1,immutable.2.2.1,immutable.2.2.2]

end PalomarI3334.SearchProgram
