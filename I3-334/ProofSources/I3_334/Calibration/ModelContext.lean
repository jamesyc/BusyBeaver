module
public import I3_334.Calibration.ModelInstructions
import I3_334Support.Engine.Arithmetic.Tape
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (dec continue_ coded_decrement_positive coded_decrement_zero coded_continue)
open PalomarI3380.Arithmetic (Chain)
open ArithmeticMachine.SourceCantor
open ArithmeticMachine.SourceWords (cons tail emitVector)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def replaceFronts (s : Store M) (a b guess : M) : Store M :=
  ((s.set fr a).set lv b).set gues guess

noncomputable def contextState (s : Store M) (remaining a b guess : M) : Store M :=
  replaceFronts (s.set goal remaining) a b guess

private theorem contextState_code (s : Store M) (remaining a b guess : M) :
    (contextState s remaining a b guess).code =
      Store.writeCode gues (Store.writeCode lv (Store.writeCode fr (Store.writeCode goal s.code remaining) a) b) guess := by
  simp [contextState,replaceFronts,Store.writeCode]

private theorem contextState_clean (s : Store M) (ready : Scratch s) (q a b g : M) :
    Scratch (contextState s q a b g) := by
  simpa [Scratch.iff_fields,contextState,replaceFronts,Store.set,goal,fr,lv,gues,tok,u,expected]
    using Scratch.iff_fields.mp ready

noncomputable def modelContextField (s : Store M) : Store M :=
  replaceFronts s (decodeRight (s fr)) (decodeRight (s lv))
    (if decodeLeft (s fr) = decodeLeft (s lv) then s gues else 0)

theorem coded_contextField (s : Store M) (ready : Scratch s) :
    contextField.Runs .normal s.code (modelContextField s).code := by
  let middle := (s.set lv (decodeRight (s lv))).set expected (decodeLeft (s lv))
  have pop := coded_pop (src := lv) (dst := expected) (by decide) (by decide) (by decide) s
    ready.expectedEmpty ready.auxiliaryEmpty
  have eat := coded_eat middle
    (by simpa [middle,Store.set,lv,expected,tok] using ready.tokenEmpty)
    (by simpa [middle,Store.set,lv,expected,u] using ready.auxiliaryEmpty)
  have normal : modelConsume middle = modelContextField s := by
    funext i
    by_cases a : i = fr <;> by_cases b : i = lv <;> by_cases c : i = gues <;>
      by_cases d : i = expected <;>
      simp [middle,modelConsume,modelContextField,replaceFronts,Store.set,a,b,c,d,
        fr,lv,gues,expected,ready.expectedEmpty,eq_comm]
  change SearchProgram.eat.Runs .normal middle.code (modelConsume middle).code at eat
  rw [normal] at eat
  exact Program.Runs.rightExit pop eat rfl

noncomputable def contextMarker (s : Store M) : M :=
  if decodeLeft (s fr) = decodeLeft (s lv) ∧
      decodeLeft (decodeRight (s fr)) = decodeLeft (decodeRight (s lv)) then s gues else 0

theorem coded_contextToken (s : Store M) (ready : Scratch s) :
    (.seq contextField contextField : Program).Runs .normal s.code
      (replaceFronts s (tail (s fr)) (tail (s lv)) (contextMarker s)).code := by
  have first := coded_contextField s ready
  have clean : Scratch (modelContextField s) := by
    simpa [Scratch.iff_fields,modelContextField,replaceFronts,Store.set,fr,lv,gues,expected,tok,u]
      using Scratch.iff_fields.mp ready
  have second := coded_contextField (modelContextField s) clean
  have same : modelContextField (modelContextField s) =
      replaceFronts s (tail (s fr)) (tail (s lv)) (contextMarker s) := by
    funext i
    by_cases a : i = fr <;> by_cases b : i = lv <;> by_cases c : i = gues <;>
      simp [modelContextField,replaceFronts,contextMarker,tail,Store.set,a,b,c,fr,lv,gues]
    all_goals
      by_cases arity : decodeLeft (s fr) = decodeLeft (s lv) <;>
      by_cases tag : decodeLeft (decodeRight (s fr)) = decodeLeft (decodeRight (s lv)) <;>
        simp [arity,tag]
  rw [same] at second
  exact Program.Runs.rightExit first second rfl

private abbrev contextTail : Program :=
  .seq (.seq (dec goal) (.seq (.seq contextField contextField) (continue_ 2))) exchange

/-- Both decrements occur before each token. The final odd unit
selects the side exchange, including in nonstandard arithmetic. -/
theorem coded_context_invariant (s : Store M) (ready : Scratch s)
    (count : M) (reverse : Bool) (encoded : s goal = 2*count+(reverse.toNat : M))
    (P : M → M → M → M → Prop) (defined : 𝚺ᴬ₁-Relation₄ P)
    (initial : P 0 (s fr) (s lv) (s gues))
    (advance : ∀ i < count, ∀ a b g, P i a b g →
      P (i+1) (tail a) (tail b)
        (contextMarker (contextState s (2*(count-(i+1))+(reverse.toNat : M)) a b g))) :
    ∃ a b g, P count a b g ∧
      contextScan.Runs .normal s.code
        (contextState s 0 (if reverse then b else a) (if reverse then a else b) g).code := by
  let flag : M := reverse.toNat
  let edge := fun a b : M => ∃ mid, (dec goal).Runs .normal a mid ∧ contextTail.Runs (.repeatAt 0) mid b
  have edgeDef : 𝚺ᴬ₁-Relation edge := by
    have first := (dec goal).runs_definable (M := M) .normal
    have rest := contextTail.runs_definable (M := M) (.repeatAt 0)
    unfold edge
    definability
  let I := fun i code : M => ∃ a b g, P i a b g ∧
    code = (contextState s (2*(count-i)+flag) a b g).code
  have Idef : 𝚺ᴬ₁-Relation I := by
    have goalCode := Store.writeCode_definable (M := M) goal
    have frontCode := Store.writeCode_definable (M := M) fr
    have backCode := Store.writeCode_definable (M := M) lv
    have guessCode := Store.writeCode_definable (M := M) gues
    simp only [I,contextState_code]
    definability
  have base : contextState s (2*(count-0)+flag) (s fr) (s lv) (s gues) = s := by
    simp only [Arithmetic.sub_zero, flag, ← encoded, contextState, replaceFronts, Store.set_same]
  have start : I 0 s.code := ⟨_,_,_,initial,congrArg Store.code base.symm⟩
  have next (i : M) (earlier : i < count) (code : M) (state : I i code) :
      ∃ t, edge code t ∧ I (i+1) t := by
    obtain ⟨a,b,g,ok,rfl⟩ := state
    let before := contextState s (2*(count-i)+flag) a b g
    let remaining := 2*(count-(i+1))+flag
    let mid := before.set goal (before goal-1)
    let after := contextState s remaining a b g
    have pair : before goal = remaining+2 := by
      have active : i+1 ≤ count := lt_iff_succ_le.mp earlier
      have debit : count-i = (count-(i+1))+1 := by
        have one := tsub_add_cancel_of_le active
        calc count-i = ((count-(i+1))+(i+1))-i := by rw [one]
          _ = (count-(i+1))+1 := by
            rw [← add_assoc, add_right_comm]
            exact Arithmetic.add_sub_self
      simp only [before,contextState,replaceFronts,Store.set,goal,fr,lv,gues,reduceIte]
      rw [debit,mul_add,mul_one]
      simp [remaining,add_assoc,add_comm,add_left_comm]
    have positive : before goal ≠ 0 := by rw [pair]; simp
    have midCount : mid goal = remaining+1 := by
      simp only [mid,Store.get_set,pair]
      rw [← one_add_one_eq_two,← add_assoc,Arithmetic.add_sub_self]
    have second : mid goal ≠ 0 := by rw [midCount]; simp
    have exactDebit : mid.set goal (mid goal-1) = after := by
      rw [midCount,Arithmetic.add_sub_self]
      funext j
      by_cases atGoal : j = goal <;> simp [mid,before,after,contextState,replaceFronts,Store.set,atGoal,goal,fr,lv,gues]
    have step := coded_decrement_positive (r := goal) second
    rw [exactDebit] at step
    have body := coded_contextToken after (contextState_clean s ready remaining a b g)
    let out := contextState s remaining (tail a) (tail b) (contextMarker after)
    have front : after fr = a := by simp [after,contextState,replaceFronts,Store.set,fr,lv,gues]
    have back : after lv = b := by simp [after,contextState,replaceFronts,Store.set,lv,gues]
    rw [front,back] at body
    have replace : replaceFronts after (tail a) (tail b) (contextMarker after) = out := by
      funext j
      by_cases x : j = fr <;> by_cases y : j = lv <;> by_cases z : j = gues <;>
        simp [after,out,contextState,replaceFronts,Store.set,x,y,z]
    rw [replace] at body
    have loop : contextTail.Runs (.repeatAt 0) mid.code out.code :=
      Program.Runs.leftExit (Program.Runs.rightExit step
        (Program.Runs.rightExit body (coded_continue 2 out) rfl) rfl) rfl
    exact ⟨out.code,⟨mid.code,coded_decrement_positive positive,loop⟩,
      ⟨_,_,_,advance i earlier a b g ok,rfl⟩⟩
  obtain ⟨finish,trace,⟨a,b,g,ok,rfl⟩⟩ := Chain.build edge edgeDef count s.code I Idef start next
  refine ⟨a,b,g,ok,?_⟩
  let final := contextState s flag a b g
  have finalCode : (contextState s (2*(count-count)+flag) a b g).code = final.code := by
    simp [final,Arithmetic.sub_self]
  rw [finalCode] at trace
  change (.seq (dec goal) contextTail : Program).Runs .normal _ _
  cases reverse with
  | false =>
    have empty : final goal = 0 := by simp [final,flag,contextState,replaceFronts,Store.set,goal,fr,lv,gues]
    exact ⟨count,final.code,trace,Or.inl (coded_decrement_zero empty)⟩
  | true =>
    have one : final goal = 1 := by simp [final,flag,contextState,replaceFronts,Store.set,goal,fr,lv,gues]
    let stopped := contextState s 0 a b g
    have first := coded_decrement_positive (r := goal) (s := final) (by rw [one]; simp)
    have reset : final.set goal (final goal-1) = stopped := by
      rw [one,Arithmetic.sub_self]
      funext j
      by_cases hit : j = goal <;> simp [final,stopped,contextState,replaceFronts,Store.set,hit,flag,goal,fr,lv,gues]
    rw [reset] at first
    have zero : stopped goal = 0 := by simp [stopped,contextState,replaceFronts,Store.set,goal,fr,lv,gues]
    have cancelled := coded_decrement_zero zero
    have ready := contextState_clean s ready 0 a b g
    have swaps := coded_exchange stopped ready.auxiliaryEmpty
    have last : (stopped.set fr (stopped lv)).set lv (stopped fr) = contextState s 0 b a g := by
      funext r
      by_cases x : r = fr <;> by_cases y : r = lv <;>
        simp [stopped,contextState,replaceFronts,Store.set,x,y,fr,lv,gues]
    rw [last] at swaps
    exact ⟨count,final.code,trace,Or.inr ⟨stopped.code,first,
      Program.Runs.rightExit (Program.Runs.leftExit cancelled rfl) swaps rfl⟩⟩

end PalomarI3334.SearchProgram

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.ArithmeticMachine (pushBit_split pushBit divIn)
open ArithmeticMachine.SourceWords (cons tail emitVector)
open ArithmeticMachine.SourceCantor
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem coded_context_total (s : Store M) (ready : Scratch s) :
    ∃ a b g, contextScan.Runs .normal s.code (contextState s 0 a b g).code := by
  obtain ⟨reverse,packed⟩ := pushBit_split (s goal)
  let count := divIn (s goal) 2
  have code : s goal = 2*count+(reverse.toNat : M) := packed.symm
  obtain ⟨a,b,g,_,run⟩ := coded_context_invariant s ready count reverse code (fun _ _ _ _ => True)
    (by
      change 𝚺ᴬ₁.Definable (fun _ : Fin 4 → M => True)
      simp) trivial (fun _ _ _ _ _ _ => trivial)
  exact ⟨_,_,g,run⟩

theorem coded_context_shared (s : Store M) (ready : Scratch s)
    (tokens front back : M) (reverse : Bool)
    (encoded : s goal = 2*len tokens+(reverse.toNat : M))
    (left : s fr = emitVector tokens front) (right : s lv = emitVector tokens back) :
    contextScan.Runs .normal s.code
      (contextState s 0 (if reverse then back else front) (if reverse then front else back) (s gues)).code := by
  let P := fun i a b g : M => ∃ remainder : M,
    len remainder = len tokens-i ∧ a = emitVector remainder front ∧ b = emitVector remainder back ∧ g = s gues
  have graph : 𝚺ᴬ₁-Relation₄ P := by unfold P; definability
  have began : P 0 (s fr) (s lv) (s gues) := ⟨tokens,by simp,left,right,rfl⟩
  have next : ∀ i < len tokens, ∀ a b g, P i a b g →
      P (i+1) (tail a) (tail b)
        (contextMarker (contextState s (2*(len tokens-(i+1))+(reverse.toNat : M)) a b g)) := by
    intro i earlier a b g state
    obtain ⟨remainder,remaining,aEq,bEq,gEq⟩ := state
    have positive : 0 < len remainder := remaining ▸ (Arithmetic.pos_sub_iff_lt.mpr earlier)
    rcases nil_or_adjoin remainder with rfl | ⟨token,rest,rfl⟩
    · simpa using positive
    · refine ⟨rest,?_,?_,?_,?_⟩
      · rw [← Arithmetic.sub_sub, ← remaining, len_adjoin, Arithmetic.add_sub_self]
      · rw [aEq,ArithmeticMachine.SourceWords.emitVector_cons,ArithmeticMachine.SourceWords.tail_cons]
      · rw [bEq,ArithmeticMachine.SourceWords.emitVector_cons,ArithmeticMachine.SourceWords.tail_cons]
      · simp [contextMarker,contextState,replaceFronts,Store.set,fr,lv,gues,aEq,bEq,gEq,decode_pairValue]
  obtain ⟨a,b,g,h,result⟩ := coded_context_invariant s ready (len tokens) reverse encoded P graph began next
  obtain ⟨rest,length,outA,outB,outMark⟩ := h
  rw [Arithmetic.sub_self] at length
  have empty : rest = 0 := len_zero_iff_eq_nil.mp length
  simpa only [outA,outB,outMark,empty,ArithmeticMachine.SourceWords.emitVector_nil] using result

end PalomarI3334.SearchProgram
