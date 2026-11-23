module
public import I3_334Support.Search.Arithmetic.CounterPrograms
public import I3_334Support.Search.Arithmetic.SourceCantor
@[expose] public section

namespace PalomarI3380.Compiler.Source

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ArithmeticMachine.SourceCantor

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem coded_ifZero_positive {r : Register} {body : Program} {s : Store M} (nonzero : s r ≠ 0) :
    (ifZero r body).Runs .normal s.code (s.set r (s r-1)).code :=
  Program.Runs.leftExit
    (Program.Runs.rightExit (coded_decrement_positive nonzero)
      (Program.Runs.instruction (.break_ 1) _) rfl) rfl

theorem coded_ifZero_zero {r : Register} {body : Program} {s t : Store M} {out : Flow}
    (zero : s r = 0) (run : body.Runs out s.code t.code) (exit : out.fromRight = some out) :
    (ifZero r body).Runs out s.code t.code :=
  Program.Runs.rightExit (Program.Runs.leftExit (coded_decrement_zero zero) rfl) run exit

/-- The conditional move implements one diagonal advance on the
two counters, exactly as in the source's Cantor pairing. -/
theorem coded_advance {a b : Register} (different : a ≠ b) (s : Store M) :
    let next := advanceState ⟪s a,s b⟫
    (Program.seq (inc b) (ifZero a (move b a))).Runs .normal s.code
      ((s.set a (π₁ next)).set b (π₂ next)).code := by
  let mid := s.set b (s b+1)
  have unchanged : mid a = s a := Store.get_set_other s b a (s b+1) different
  by_cases zero : s a = 0
  · have atZero : mid a = 0 := unchanged.trans zero
    have next := coded_move (Ne.symm different) mid
    have result : (mid.set b 0).set a (mid a+mid b) = (s.set a (s b+1)).set b 0 := by
      rw [unchanged,zero,zero_add]
      simp only [mid,Store.get_set,Store.set_set]
      exact Store.set_comm s (Ne.symm different) _ _
    rw [result] at next
    have run := Program.Runs.rightExit (coded_increment b s) (coded_ifZero_zero atZero next rfl) rfl
    simpa only [advanceState,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair,zero,↓reduceIte] using run
  · have atPositive : mid a ≠ 0 := fun eq => zero (unchanged.symm.trans eq)
    have next := coded_ifZero_positive (body := move b a) atPositive
    have result : mid.set a (mid a-1) = (s.set a (s a-1)).set b (s b+1) := by
      rw [unchanged]
      exact Store.set_comm s (Ne.symm different) _ _
    rw [result] at next
    have run := Program.Runs.rightExit (coded_increment b s) next rfl
    simpa only [advanceState,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair,zero,↓reduceIte] using run

theorem coded_unpair {a b input : Register} (ab : a ≠ b) (ai : a ≠ input) (bi : b ≠ input)
    (s : Store M) (zeroLeft : s a = 0) (zeroRight : s b = 0) :
    (unpair a b input).Runs .normal s.code
      (((s.set input 0).set a (decodeLeft (s input))).set b (decodeRight (s input))).code := by
  let states := fun i : M => ((s.set input (s input-i)).set a (decodeLeft i)).set b (decodeRight i)
  have graph : 𝚺ᴬ₁-Function₁ (fun i => (states i).code) := by
    apply matrixToVec_definable₁
    intro r
    by_cases equalsRight : r = b
    · simp only [states,Store.set,equalsRight,↓reduceIte]
      definability
    · by_cases equalsLeft : r = a
      · simp only [states,Store.set,equalsRight,equalsLeft,↓reduceIte]
        definability
      · by_cases equalsInput : r = input
        · simp only [states,Store.set,equalsRight,equalsLeft,equalsInput,↓reduceIte]
          definability
        · simp only [states,Store.set,equalsRight,equalsLeft,equalsInput,↓reduceIte]
          definability
  have left (i : M) : states i a = decodeLeft i := by simp [states,Store.set,ab]
  have right (i : M) : states i b = decodeRight i := by simp [states]
  have counter (i : M) : states i input = s input-i := by
    simp [states,Store.set,Ne.symm ai,Ne.symm bi]
  have stop : states (s input) input = 0 := by rw [counter,Arithmetic.sub_self]
  have onlyLeft : s.set a 0 = s := by rw [← zeroLeft,Store.set_same]
  have onlyRight : s.set b 0 = s := by rw [← zeroRight,Store.set_same]
  have base : states 0 = s := by
    simp [states,decodeLeft,decodeRight,Store.set_same,onlyLeft,onlyRight]
  have finish : states (s input) =
      ((s.set input 0).set a (decodeLeft (s input))).set b (decodeRight (s input)) := by simp [states]
  have trace := coded_while input (.seq (inc b) (ifZero a (move b a))) states (s input) graph stop
  suffices steps : _ by
    simpa only [base,finish,unpair] using trace steps
  intro i before
  have positive : 0 < s input-i := Arithmetic.pos_sub_iff_lt.mpr before
  refine ⟨by simpa only [counter] using positive.ne',?_⟩
  let decState := (states i).set input (states i input-1)
  have changed := coded_advance ab decState
  have ha : decState a = decodeLeft i := (Store.get_set_other (states i) input a (states i input-1) ai).trans (left i)
  have hb : decState b = decodeRight i := (Store.get_set_other (states i) input b (states i input-1) bi).trans (right i)
  have pair : ⟪decState a,decState b⟫ = decodeState i := by
    rw [ha,hb,decodeLeft,decodeRight,pair_unpair]
  dsimp only at changed
  rw [pair,← decodeState_succ] at changed
  have aligned :
      (decState.set a (decodeLeft (i+1))).set b (decodeRight (i+1)) = states (i+1) := by
    funext r
    by_cases atRight : r = b <;> by_cases atLeft : r = a <;> by_cases atInput : r = input <;>
      simp [decState,counter,states,Store.set,atRight,atLeft,atInput,
        Arithmetic.sub_sub,Ne.symm ai,Ne.symm bi]
  change ((inc b).seq (ifZero a (move b a))).Runs .normal decState.code
    ((decState.set a (decodeLeft (i+1))).set b (decodeRight (i+1))).code at changed
  rwa [aligned] at changed

end PalomarI3380.Compiler.Source
