module
public import I3_334.Calibration.ModelScanConsume
public import I3_334Support.Search.Arithmetic.CodedLines
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (CodedLines clear inc move whilePositive coded_increment coded_clear coded_move)
open ArithmeticMachine.SourceWords
open ArithmeticMachine.SourceCantor
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def modelScanSetup (slot : Fin 4) : List Program :=
  [clear goal,clear tmp,copy dc tmp] ++ dictionarySlot slot ++ [inc goal]

noncomputable def modelScanInitial (s : Store M) (slot : Fin 4) : Store M :=
  (s.set tmp (modelSlot (s dc) slot)).set goal 1

theorem modelScanInitial_clean (s : Store M) (slot : Fin 4) (good : Scratch s) :
    Scratch (modelScanInitial s slot) := by
  simpa [Scratch.iff_fields,modelScanInitial,Store.set,goal,tmp,expected,tok,u]
    using Scratch.iff_fields.mp good

theorem coded_scanSetup (s : Store M) (slot : Fin 4) (good : Scratch s) :
    CodedLines (modelScanSetup slot) s.code (modelScanInitial s slot).code := by
  let clearGoal := s.set goal 0
  let clearTmp := clearGoal.set tmp 0
  let copied := clearTmp.set tmp (s dc)
  let loaded := (s.set goal 0).set tmp (modelSlot (s dc) slot)
  have first := coded_clear goal s
  have second := coded_clear tmp clearGoal
  have third : (copy dc tmp).Runs .normal clearTmp.code copied.code := by
    have move := coded_copy (a := dc) (b := tmp) (by decide) (by decide) (by decide) clearTmp
      (by simpa [clearTmp,clearGoal,Store.set,goal,tmp,u] using good.auxiliaryEmpty)
    have read : clearTmp dc = s dc := by simp [clearTmp,clearGoal,Store.set,goal,tmp,dc]
    have zero : clearTmp tmp = 0 := Store.get_set _ _ _
    simpa only [copied,zero,zero_add,show clearTmp dc = s dc from by
      simp [clearTmp,clearGoal,Store.set,goal,tmp,dc]] using move
  have scratch : Scratch copied := by
    simpa [Scratch.iff_fields,copied,clearTmp,clearGoal,Store.set,goal,tmp,expected,tok,u]
      using Scratch.iff_fields.mp good
  have fourth : CodedLines (dictionarySlot slot) copied.code loaded.code := by
    have run := coded_dictionarySlot slot copied scratch
    simpa only [copied,clearTmp,loaded,clearGoal,Store.get_set,Store.set_set] using run
  have last : (inc goal).Runs .normal loaded.code (modelScanInitial s slot).code := by
    have quantity : loaded goal = 0 := by simp [loaded,Store.set,goal,tmp]
    have normal : loaded.set goal 1 = modelScanInitial s slot := by
      funext i
      by_cases a : i = goal <;> by_cases b : i = tmp <;>
        simp [loaded,modelScanInitial,Store.set,a,b,goal,tmp]
    simpa only [quantity,zero_add,normal] using coded_increment goal loaded
  exact (CodedLines.cons first (.cons second (.cons third (.nil _)))).append
    (fourth.append (.cons last (.nil _)))

theorem coded_scan_total [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (slot : Fin 4) (s : Store M) (clean : Scratch s) :
    ∃ t : Store M, (scan slot).Runs .normal s.code t.code ∧ Scratch t ∧ t goal = 0 ∧
      ∀ r ∉ [goal,tmp,fr,gues], t r = s r := by
  have initial := coded_scanSetup s slot clean
  obtain ⟨t,body,good,clear,preserved⟩ := coded_scanLoop_total slot (modelScanInitial s slot)
    (modelScanInitial_clean s slot clean)
  have code : (scan slot).Runs .normal s.code t.code := by
    simpa only [scan,modelScanSetup,List.append_assoc,List.singleton_append] using (initial.append (.cons body (.nil _))).block
  refine ⟨t,code,good,clear,?_⟩
  intro r outside
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at outside
  simp [preserved r (by simpa using outside),modelScanInitial,Store.set,outside.1,outside.2.1]

theorem coded_scan_selected (slot : Fin 4) (s : Store M) (clean : Scratch s)
    (tokens dictionary front : M)
    (dictWord : modelSlot (s dc) slot = emitRaw tokens dictionary (bias slot : M))
    (frontWord : s fr = emitVector tokens front)
    (parsed : GuardedConsumes (bias slot : M) tokens 1 0) :
    (scan slot).Runs .normal s.code (modelScanner s 0 dictionary front).code := by
  let loaded := modelScanInitial s slot
  have initial := coded_scanSetup s slot clean
  have body := coded_scan_consumes slot loaded (modelScanInitial_clean s slot clean)
    tokens dictionary front (Store.get_set ..)
    (by simpa [loaded,modelScanInitial,Store.set,tmp,goal] using dictWord)
    (by simpa [loaded,modelScanInitial,Store.set,tmp,goal,fr] using frontWord)
    parsed
  have final : modelScanner loaded 0 dictionary front = modelScanner s 0 dictionary front := by
    funext i
    by_cases a : i = goal <;> by_cases b : i = tmp <;> by_cases c : i = fr <;>
      simp [modelScanner,loaded,modelScanInitial,Store.set,a,b,c,goal,tmp,fr]
  rw [final] at body
  simpa only [scan,modelScanSetup,List.append_assoc,List.singleton_append] using (initial.append (.cons body (.nil _))).block

theorem coded_exchange (s : Store M) (scratchZero : s u = 0) :
    exchange.Runs .normal s.code ((s.set fr (s lv)).set lv (s fr)).code := by
  let first := (s.set fr 0).set u (s fr)
  let second := (first.set lv 0).set fr (s lv)
  have a : (move fr u).Runs .normal s.code first.code := by
    simpa only [first,scratchZero,zero_add] using coded_move (a := fr) (b := u) (by decide) s
  have b : (move lv fr).Runs .normal first.code second.code := by
    simpa [first,second,Store.set,fr,u,lv] using coded_move (a := lv) (b := fr) (by decide) first
  have c := coded_move (a := u) (b := lv) (by decide) second
  have equal : (second.set u 0).set lv (second lv+second u) = (s.set fr (s lv)).set lv (s fr) := by
    funext i
    by_cases x : i = fr <;> by_cases y : i = lv <;> by_cases z : i = u <;>
      simp [second,first,Store.set,x,y,z,fr,lv,u,scratchZero]
  rw [equal] at c
  exact Program.Runs.rightExit a (Program.Runs.rightExit b c rfl) rfl

end PalomarI3334.SearchProgram
