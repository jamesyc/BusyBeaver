module
public import I3_334.Calibration.ModelWords
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (whilePositive continue_ dec coded_continue
  coded_decrement_positive coded_decrement_zero)
open PalomarI3380.Arithmetic (Chain)
open ArithmeticMachine.SourceCantor
open ArithmeticMachine.SourceWords
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def modelScanner (s : Store M) (waiting dictionary front : M) : Store M :=
  ((s.set goal waiting).set tmp dictionary).set fr front

theorem modelScanner_clean (s : Store M) (ready : Scratch s) (waiting dictionary front : M) :
    Scratch (modelScanner s waiting dictionary front) := by
  refine ⟨?_,?_,?_⟩ <;>
    simp [modelScanner,Store.set,goal,tmp,fr,expected,tok,u,
      ready.expectedEmpty,ready.tokenEmpty,ready.auxiliaryEmpty]

theorem modelScanStep_shared (slot : Fin 4) (s : Store M) (a tag dictionary front : M)
    (safe : (bias slot : M) ≤ tag)
    (inDictionary : s tmp = rawCons a (tag-(bias slot : M)) dictionary)
    (atFront : s fr = cons a tag front) :
    modelScanStep slot s = modelScanner s (s goal+a) dictionary front := by
  have recover : tag-(bias slot : M)+(bias slot : M) = tag :=
    tsub_add_cancel_of_le safe
  simp only [modelScanStep,inDictionary,atFront,rawCons,(decode_pairValue _ _).1,
    (decode_pairValue _ _).2, decodeLeft_cons,decodeRight_cons,recover, ↓reduceIte, and_self]
  funext i
  by_cases g : i = goal <;> by_cases t : i = tmp <;> by_cases f : i = fr <;>
    by_cases m : i = gues <;> simp [modelScanner,Store.set,g,t,f,m,goal,tmp,fr,gues]

/-- A guard-valid internal token vector is consumed by the native
dictionary loop. This theorem places no external bound on its length. -/
theorem coded_scan_consumes (slot : Fin 4) (s : Store M) (clean : Scratch s)
    (tokens dictionary front : M)
    (waiting : s goal = 1) (inDictionary : s tmp = emitRaw tokens dictionary (bias slot : M))
    (atFront : s fr = emitVector tokens front) (parsed : GuardedConsumes (bias slot : M) tokens 1 0) :
    (whilePositive goal (scanBody slot)).Runs .normal s.code
      (modelScanner s 0 dictionary front).code := by
  let state := fun z : M => modelScanner s (π₂ z) (emitRaw (π₁ z) dictionary (bias slot : M))
    (emitVector (π₁ z) front)
  let code := fun z : M => (state z).code
  have graph : 𝚺ᴬ₁-Function₁ code := by
    have dGoal := Store.writeCode_definable (M := M) goal
    have dTmp := Store.writeCode_definable (M := M) tmp
    have dFr := Store.writeCode_definable (M := M) fr
    have formula (z : M) : code z = Store.writeCode fr (Store.writeCode tmp
        (Store.writeCode goal s.code (π₂ z)) (emitRaw (π₁ z) dictionary (bias slot : M)))
          (emitVector (π₁ z) front) := by
      simp [code,state,modelScanner,Store.writeCode]
    change 𝚺ᴬ₁.Definable (fun v : Fin 2 → M => v 0 = code (v 1))
    simp only [formula]
    definability
  let body := Program.seq (scanBody slot) (continue_ 1)
  let edge := fun a b : M => ∃ mid, (dec goal).Runs .normal a mid ∧ body.Runs (.repeatAt 0) mid b
  have realizes : ∀ x y : M, guardedStep (bias slot : M) x y → edge (code x) (code y) := by
    intro x y h
    obtain ⟨token,rest,positive,remains,allowed,rfl⟩ := h
    have goalValue : state x goal = π₂ x := by simp [state,modelScanner,Store.set,goal,tmp,fr]
    have still : state x goal ≠ 0 := goalValue.symm ▸ positive.ne'
    let middle := (state x).set goal (state x goal-1)
    have good : Scratch middle := by
      have initial := modelScanner_clean s clean (π₂ x) (emitRaw (π₁ x) dictionary (bias slot : M))
        (emitVector (π₁ x) front)
      exact ⟨by simpa [middle,state,Store.set,goal,expected] using initial.expectedEmpty,
        by simpa [middle,state,Store.set,goal,tok] using initial.tokenEmpty,
        by simpa [middle,state,Store.set,goal,u] using initial.auxiliaryEmpty⟩
    have dictionaryWord : middle tmp = rawCons (π₁ token) (π₂ token-(bias slot : M))
        (emitRaw rest dictionary (bias slot : M)) := by
      simp [middle,state,modelScanner,Store.set,tmp,goal,fr,remains]
    have frontWord : middle fr = cons (π₁ token) (π₂ token) (emitVector rest front) := by
      simp [middle,state,modelScanner,Store.set,tmp,goal,fr,remains]
    have one := coded_scanBody slot middle good
    rw [modelScanStep_shared slot middle _ _ _ _ allowed dictionaryWord frontWord] at one
    have final : modelScanner middle (middle goal+π₁ token) (emitRaw rest dictionary (bias slot : M))
        (emitVector rest front) = state ⟪rest,π₂ x-1+π₁ token⟫ := by
      have remaining : middle goal = π₂ x-1 := by simp only [middle,Store.get_set,goalValue]
      rw [remaining]
      unfold state
      simp only [Arithmetic.pi₁_pair,Arithmetic.pi₂_pair]
      funext r
      by_cases x : r = goal <;> by_cases y : r = tmp <;> by_cases z : r = fr <;>
        simp [middle,state,modelScanner,Store.set,x,y,z,goalValue]
    rw [final] at one
    exact ⟨middle.code,coded_decrement_positive still,
      Program.Runs.rightExit one (coded_continue 1 _) rfl⟩
  have trace := Chain.map parsed code graph realizes
  have start : state ⟪tokens,(1 : M)⟫ = s := by
    simp [state,modelScanner,← waiting,← inDictionary,← atFront,Store.set_same]
  have finish : state ⟪0,0⟫ = modelScanner s 0 dictionary front := by simp [state]
  have zero : (modelScanner s 0 dictionary front) goal = 0 := by
    simp [modelScanner,Store.set,goal,fr,tmp]
  refine ⟨len tokens,(modelScanner s 0 dictionary front).code,?_,Or.inl (coded_decrement_zero zero)⟩
  simpa only [code,start,finish] using trace

end PalomarI3334.SearchProgram
