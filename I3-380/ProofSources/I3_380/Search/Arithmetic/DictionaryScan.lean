module
public import I3_380.Search.Arithmetic.DictionaryFields
public import I3_380.Search.Arithmetic.CodedLines
@[expose] public section

namespace PalomarI3380.Compiler.Source

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open ArithmeticMachine.SourceCantor
open ArithmeticMachine.SourceWords

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def modelDictionaryTail : Nat → M → M
  | 0, code => code
  | n+1, code => modelDictionaryTail n (decodeRight code)

noncomputable def modelCoordinate (code : M) (index : Fin 3) : M :=
  decodeLeft (modelDictionaryTail index.val code)

noncomputable def modelDictionary (entries : Fin 3 → M) : M :=
  pairValue (entries 0) (pairValue (entries 1) (pairValue (entries 2) 0))

theorem modelCoordinate_dictionary (entries : Fin 3 → M) (index : Fin 3) :
    modelCoordinate (modelDictionary entries) index = entries index := by
  have which : index = 0 ∨ index = 1 ∨ index = 2 := by
    rcases (show index.val=0 ∨ index.val=1 ∨ index.val=2 by have h:=index.isLt; omega) with h|h|h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  rcases which with rfl|rfl|rfl <;>
    simp [modelCoordinate,modelDictionary,modelDictionaryTail,decode_pairValue]

theorem coded_dropFields (n : Nat) (s : Store M) (clean : ContextScratch s) :
    CodedLines (List.replicate n dropField) s.code (s.set tmp (modelDictionaryTail n (s tmp))).code := by
  induction n generalizing s with
  | zero =>
    simpa only [List.replicate_zero,modelDictionaryTail,Store.set_same] using CodedLines.nil s.code
  | succ n ih =>
    let middle := s.set tmp (decodeRight (s tmp))
    have clear : ContextScratch middle := by
      simpa [ContextScratch,middle,Store.set,tmp,«exp»,tok,u] using clean
    have step := ih middle clear
    change CodedLines _ middle.code ((s.set tmp (decodeRight (s tmp))).set tmp
      (modelDictionaryTail n (middle tmp))).code at step
    rw [show middle tmp = decodeRight (s tmp) from Store.get_set ..,Store.set_set] at step
    exact CodedLines.cons (coded_dropField s clean) step

def scanSetup (index : Fin 3) : List Program :=
  [copy dc tmp] ++ List.replicate index.val dropField ++ [grabField,inc goal]

noncomputable def scanInitial (s : Store M) (index : Fin 3) : Store M :=
  (s.set tmp (modelCoordinate (s dc) index)).set goal 1

theorem scanInitial_scratch (s : Store M) (index : Fin 3) (scratch : ClearScratch s) :
    ContextScratch (scanInitial s index) := by
  have cleared : ContextScratch s := ⟨scratch.expZero,scratch.tokZero,scratch.auxZero⟩
  simpa [ContextScratch,scanInitial,Store.set,goal,tmp,«exp»,tok,u] using cleared

theorem coded_scanSetup (s : Store M) (index : Fin 3) (scratch : ClearScratch s) :
    CodedLines (scanSetup index) s.code (scanInitial s index).code := by
  let copied := s.set tmp (s dc)
  have copyRun := coded_copy (a := dc) (b := tmp) (by decide) (by decide) (by decide) s scratch.auxZero
  rw [scratch.tempZero,zero_add] at copyRun
  have baseClean : ContextScratch s := ⟨scratch.expZero,scratch.tokZero,scratch.auxZero⟩
  have copiedClean : ContextScratch copied := by
    simpa [ContextScratch,copied,Store.set,tmp,«exp»,tok,u] using baseClean
  have drop := coded_dropFields index.val copied copiedClean
  let tail := modelDictionaryTail index.val (s dc)
  let remaining := s.set tmp tail
  change CodedLines _ copied.code ((s.set tmp (s dc)).set tmp
    (modelDictionaryTail index.val (copied tmp))).code at drop
  rw [show copied tmp = s dc from Store.get_set ..,Store.set_set] at drop
  have cleanTail : ContextScratch remaining := by
    simpa [ContextScratch,remaining,Store.set,tmp,«exp»,tok,u] using baseClean
  have last := coded_grabField remaining cleanTail
  change grabField.Runs .normal remaining.code ((s.set tmp tail).set tmp
    (decodeLeft (remaining tmp))).code at last
  rw [show remaining tmp = tail from Store.get_set ..,Store.set_set] at last
  let chosen := s.set tmp (modelCoordinate (s dc) index)
  have goal := coded_increment goal chosen
  have zero : chosen Source.goal = 0 := by
    unfold chosen
    rw [Store.get_set_other _ _ _ _ (by decide : Source.goal ≠ tmp),scratch.goalZero]
  rw [zero,zero_add] at goal
  unfold scanSetup
  rw [List.append_assoc]
  exact CodedLines.cons copyRun (drop.append (CodedLines.cons last (CodedLines.cons goal (.nil _))))

theorem coded_scanShared (index : Fin 3) (s : Store M) (clear : ClearScratch s)
    (tokens rest : M) (decoded : modelCoordinate (s dc) index = emitVector tokens 0)
    (front : s fr = emitVector tokens rest) (tree : ConsumesTree tokens) :
    (scan index).Runs .normal s.code (s.set fr rest).code := by
  let initial := scanInitial s index
  have setup := coded_scanSetup s index clear
  have ready := scanInitial_scratch s index clear
  have need : initial goal = 1 := Store.get_set ..
  have dictionary : initial tmp = emitVector tokens 0 := by
    simpa [initial,scanInitial,Store.set,tmp,goal] using decoded
  have word : initial fr = emitVector tokens rest := by
    simpa [initial,scanInitial,Store.set,fr,tmp,goal] using front
  have run := coded_scan_consumes initial ready tokens 0 rest need dictionary word
    (by simpa using tree 1 (by simp))
  let finish := scannerStore initial 0 0 rest
  have tmpZero : finish tmp = 0 := by simp [finish,scannerStore,Store.set,tmp,fr]
  have clearTmp := coded_clear tmp finish
  have same : finish.set tmp 0 = s.set fr rest := by
    have h1 : finish.set tmp 0 = finish := by rw [← tmpZero,Store.set_same]
    rw [h1]
    unfold finish scannerStore initial scanInitial
    rw [Store.set_set]
    have goalStill : (s.set tmp (modelCoordinate (s dc) index)) goal = 0 := by
      rw [Store.get_set_other _ _ _ _ (by decide : goal ≠ tmp),clear.goalZero]
    have removeGoal : (s.set tmp (modelCoordinate (s dc) index)).set goal 0 =
        s.set tmp (modelCoordinate (s dc) index) := by rw [← goalStill,Store.set_same]
    rw [removeGoal,Store.set_set,← clear.tempZero,Store.set_same]
  rw [same] at clearTmp
  apply CodedLines.block
  simpa [scanSetup,List.append_assoc] using setup.append (.cons run (.cons clearTmp (.nil _)))

theorem coded_scan_total [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (index : Fin 3) (s : Store M)
    (clear : ClearScratch s) : ∃ front marker : M,
    (scan index).Runs .normal s.code ((s.set fr front).set gues marker).code := by
  let start := scanInitial s index
  have setup := coded_scanSetup s index clear
  obtain ⟨finished,loop,clean,empty,preserved⟩ := coded_scanLoop_total start (scanInitial_scratch s index clear)
  have erase := coded_clear tmp finished
  have aligned : finished.set tmp 0 = (s.set fr (finished fr)).set gues (finished gues) := by
    funext r
    by_cases atFront : r=fr
    · subst r
      simp [Store.set,fr,tmp,gues]
    by_cases atMark : r=gues
    · subst r
      simp [Store.set,gues,tmp]
    simp only [Store.set,atFront,atMark,↓reduceIte]
    by_cases atTmp : r=tmp
    · subst r
      simpa only [if_true] using clear.tempZero.symm
    · simp only [atTmp,↓reduceIte]
      by_cases atGoal : r=goal
      · subst r
        exact empty.trans clear.goalZero.symm
      by_cases atExp : r=«exp»
      · subst r
        exact clean.1.trans clear.expZero.symm
      have outside : r ∉ scanRegisters := by simp [scanRegisters,atTmp,atFront,atMark,atGoal,atExp]
      exact (preserved r outside).trans (by simp [start,scanInitial,Store.set,atGoal,atTmp])
  rw [aligned] at erase
  refine ⟨finished fr,finished gues,?_⟩
  apply CodedLines.block
  simpa [scanSetup,List.append_assoc] using setup.append (.cons loop (.cons erase (.nil _)))

end PalomarI3380.Compiler.Source
