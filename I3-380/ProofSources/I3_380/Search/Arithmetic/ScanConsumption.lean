module
public import I3_380.Search.Arithmetic.ScanLoop
public import I3_380.Search.Arithmetic.TokenConsumption
@[expose] public section

namespace PalomarI3380.Compiler.Source

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PalomarI3380.Arithmetic (Chain)
open ArithmeticMachine.SourceWords
open ArithmeticMachine.SourceCantor (decode_pairValue)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def scannerStore (s : Store M) (waiting dictionary front : M) : Store M :=
  ((s.set goal waiting).set tmp dictionary).set fr front

theorem scannerStore_good (s : Store M) (clean : ContextScratch s) (waiting dictionary front : M) :
    ContextScratch (scannerStore s waiting dictionary front) := by
  simpa [ContextScratch,scannerStore,Store.set,«exp»,goal,tmp,fr,tok,u] using clean

theorem scanStep_shared (s : Store M) (clean : ContextScratch s) (a t dictionary front : M)
    (inDictionary : s tmp = cons a t dictionary) (atFront : s fr = cons a t front) :
    scanStep s = scannerStore s (s goal+a) dictionary front := by
  have goalValue : scanStep s goal = s goal+a := by
    rw [scanStep_goal,inDictionary,decodeLeft_cons,Arithmetic.add_sub_self]
  have dictionaryValue : scanStep s tmp = dictionary := by
    rw [scanStep_dictionary,inDictionary,decodeRight_cons,(decode_pairValue _ _).2]
  have frontValue : scanStep s fr = front := by
    rw [scanStep_front,atFront,decodeRight_cons,(decode_pairValue _ _).2]
  have markerValue := scanStep_marker_shared s a t dictionary front inDictionary atFront
  have expValue := (scanStep_scratch s clean).1
  funext r
  by_cases isGoal : r=goal
  · subst r; simpa [scannerStore,Store.set,goal,tmp,fr] using goalValue
  by_cases isTmp : r=tmp
  · subst r; simpa [scannerStore,Store.set,tmp,fr] using dictionaryValue
  by_cases isFr : r=fr
  · subst r; simpa [scannerStore] using frontValue
  by_cases isMark : r=gues
  · subst r; simpa [scannerStore,Store.set,goal,tmp,fr,gues] using markerValue
  by_cases isExp : r=«exp»
  · subst r
    exact expValue.trans (scannerStore_good s clean (s goal+a) dictionary front).1.symm
  have other : r ∉ scanRegisters := by
    simp [scanRegisters,isGoal,isTmp,isFr,isMark,isExp]
  simpa [scannerStore,Store.set,isGoal,isTmp,isFr] using scanStep_preserves s r other

/-- A matched dictionary prefix is consumed without changing the
candidate marker. The token trace can have any length in the model. -/
theorem coded_scan_consumes (s : Store M) (clean : ContextScratch s) (tokens dictionary front : M)
    (waiting : s goal=1) (inDictionary : s tmp = emitVector tokens dictionary)
    (atFront : s fr = emitVector tokens front) (parsed : Consumes tokens (1 : M) 0) :
    (whilePositive goal scanBody).Runs .normal s.code
      (scannerStore s 0 dictionary front).code := by
  let state := fun z : M => scannerStore s (π₂ z) (emitVector (π₁ z) dictionary) (emitVector (π₁ z) front)
  let code := fun z : M => (state z).code
  have graph : 𝚺ᴬ₁-Function₁ code := by
    have dGoal := Store.writeCode_definable (M := M) goal
    have dTmp := Store.writeCode_definable (M := M) tmp
    have dFr := Store.writeCode_definable (M := M) fr
    have formula (z : M) : code z = Store.writeCode fr (Store.writeCode tmp
        (Store.writeCode goal s.code (π₂ z)) (emitVector (π₁ z) dictionary)) (emitVector (π₁ z) front) := by
      simp [code,state,scannerStore,Store.writeCode]
    change 𝚺ᴬ₁.Definable (fun v : Fin 2 → M => v 0 = code (v 1))
    simp only [formula]
    definability
  let body := Program.seq scanBody (continue_ 1)
  let edge := fun a b : M => ∃ mid, (dec goal).Runs .normal a mid ∧ body.Runs (.repeatAt 0) mid b
  have realizes : ∀ x y : M, consumptionStep x y → edge (code x) (code y) := by
    intro x y h
    obtain ⟨positive,token,rest,remains,rfl⟩ := h
    have goalValue : state x goal = π₂ x := by simp [state,scannerStore,Store.set,goal,tmp,fr]
    have still : state x goal ≠ 0 := goalValue.symm ▸ positive.ne'
    let middle := (state x).set goal (state x goal-1)
    have good : ContextScratch middle := by
      have spec := scannerStore_good s clean (π₂ x) (emitVector (π₁ x) dictionary) (emitVector (π₁ x) front)
      simpa [ContextScratch,middle,Store.set,goal,«exp»,tok,u] using spec
    have dictionaryWord : middle tmp = cons (π₁ token) (π₂ token) (emitVector rest dictionary) := by
      simp [middle,state,scannerStore,Store.set,tmp,goal,fr,remains]
    have frontWord : middle fr = cons (π₁ token) (π₂ token) (emitVector rest front) := by
      simp [middle,state,scannerStore,Store.set,goal,fr,remains]
    have one := coded_scanBody middle good
    rw [scanStep_shared middle good _ _ _ _ dictionaryWord frontWord] at one
    have final : scannerStore middle (middle goal+π₁ token) (emitVector rest dictionary) (emitVector rest front) =
        state ⟪rest,π₂ x-1+π₁ token⟫ := by
      have remaining : middle goal = π₂ x-1 := by simp only [middle,Store.get_set,goalValue]
      rw [remaining]
      unfold state
      simp only [Arithmetic.pi₁_pair,Arithmetic.pi₂_pair]
      funext r
      by_cases isGoal : r=goal <;> by_cases isTmp : r=tmp <;> by_cases isFr : r=fr <;>
        simp [middle,state,scannerStore,Store.set,isGoal,isTmp,isFr,goalValue]
    rw [final] at one
    exact ⟨middle.code,coded_decrement_positive still,
      Program.Runs.rightExit one (coded_continue 1 _) rfl⟩
  have trace := Chain.map parsed code graph realizes
  have start : state ⟪tokens,(1 : M)⟫ = s := by
    simp [state,scannerStore,← waiting,← inDictionary,← atFront,Store.set_same]
  have finish : state ⟪0,0⟫ = scannerStore s 0 dictionary front := by simp [state]
  have zero : (scannerStore s 0 dictionary front) goal = 0 := by
    simp [scannerStore,Store.set,goal,fr,tmp]
  refine ⟨len tokens,(scannerStore s 0 dictionary front).code,?_,Or.inl (coded_decrement_zero zero)⟩
  simpa only [code,start,finish] using trace

end PalomarI3380.Compiler.Source
