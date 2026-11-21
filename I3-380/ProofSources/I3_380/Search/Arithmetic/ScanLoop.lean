module
public import I3_380.Search.Arithmetic.ScanPrograms
@[expose] public section

namespace PalomarI3380.Compiler.Source

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ArithmeticMachine.SourceCantor

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def scanRegisters : List Register := [goal,tmp,fr,gues,«exp»]

theorem scanStep_preserves (s : Store M) (r : Register) (outside : r ∉ scanRegisters) :
    scanStep s r = s r := by
  simp only [scanRegisters,List.mem_cons,List.not_mem_nil,or_false,not_or] at outside
  obtain ⟨notGoal,notDictionary,notFront,notMarker,notExpected⟩ := outside
  simp [scanStep,eatScanField,popScanField,afterArity,Store.set,
    notGoal,notDictionary,notFront,notMarker,notExpected]

theorem decode_sum_le (word : M) : decodeLeft word+decodeRight word ≤ word := by
  have small := triangle_ge (decodeLeft word+decodeRight word)
  have lePair : triangleValue (decodeLeft word+decodeRight word) ≤
      pairValue (decodeLeft word) (decodeRight word) := by
    unfold pairValue
    simp
  exact small.trans (lePair.trans_eq (pairValue_decode word))

theorem scan_drops_measure (s : Store M) (pending : s goal ≠ 0) :
    scanStep (s.set goal (s goal-1)) goal + scanStep (s.set goal (s goal-1)) tmp <
      s goal + s tmp := by
  have tmpSame : (s.set goal (s goal-1)) tmp = s tmp :=
    Store.get_set_other _ _ _ _ (by decide)
  rw [scanStep_goal,scanStep_dictionary,Store.get_set,tmpSame]
  have lessNeed : s goal-1 < s goal :=
    Arithmetic.pred_lt_self_of_pos (pos_iff_ne_zero.mpr pending)
  have dictionary : (decodeLeft (s tmp)-1) + decodeRight (decodeRight (s tmp)) ≤ s tmp :=
    (add_le_add (Arithmetic.sub_le_self ..) (decodeValue_bounds (decodeRight (s tmp))).2).trans
      (decode_sum_le (s tmp))
  rw [add_assoc]
  have fewer : s goal-1+s tmp < s goal+s tmp := by
    simpa only [add_comm] using add_lt_add_right lessNeed (s tmp)
  exact lt_of_le_of_lt (add_le_add_right dictionary (s goal-1)) fewer

/-- Termination on every dictionary word, including malformed words.
The dictionary code plus the pending node count decreases at each step. -/
theorem coded_scanLoop_total [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (s : Store M) (initial : ContextScratch s) :
    ∃ t : Store M, (whilePositive goal scanBody).Runs .normal s.code t.code ∧
      ContextScratch t ∧ t goal = 0 ∧ ∀ r ∉ scanRegisters, t r = s r := by
  let measure := fun code : M => Store.ofCode code goal + Store.ofCode code tmp
  have goalRead := Store.read_definable (M := M) goal
  have dictionaryRead := Store.read_definable (M := M) tmp
  have measureDef : 𝚺ᴬ₁-Function₁ measure := by unfold measure; definability
  let I := fun code : M => len code = 12 ∧ ContextScratch (Store.ofCode code) ∧
    ∀ r ∉ scanRegisters, Store.ofCode code r = s r
  have reading (r : Register) := Store.read_definable (M := M) r
  have fixedRegisters : 𝚺ᴬ₁-Predicate (fun code : M =>
      ∀ r ∉ scanRegisters, Store.ofCode code r = s r) := by
    apply Bounding.HierarchySymbol.Definable.fintype_all
    intro r
    have read := reading r
    by_cases altered : r ∈ scanRegisters <;> simp [altered] <;> definability
  have invariant : 𝚺ᴬ₁-Predicate I := by
    unfold I ContextScratch
    have e := reading «exp»
    have t := reading tok
    have a := reading u
    definability
  have next : ∀ code : M, I code → Store.ofCode code goal ≠ 0 →
      ∃ after : M, scanBody.Runs .normal
        (Store.writeCode goal code (Store.ofCode code goal-1)) after ∧
        I after ∧ measure after < measure code := by
    intro code valid positive
    let state := Store.ofCode code
    let mid := state.set goal (state goal-1)
    have before : ContextScratch mid := by
      simpa [ContextScratch,mid,Store.set,goal,«exp»,tok,u] using valid.2.1
    let after := scanStep mid
    have out := coded_scanBody mid before
    change scanBody.Runs .normal mid.code after.code at out
    refine ⟨after.code,out,?_ ,?_⟩
    · unfold I
      rw [Store.len_code,Store.ofCode_code]
      refine ⟨rfl,scanStep_scratch mid before,fun r outside => ?_⟩
      have other : r ≠ goal := by
        intro wrong
        subst r
        exact outside (by simp [scanRegisters])
      exact (scanStep_preserves mid r outside).trans
        ((Store.get_set_other _ _ _ _ other).trans (valid.2.2 r outside))
    · simpa only [measure,Store.ofCode_code,after,mid,state] using scan_drops_measure state positive
  have ready : I s.code := by
    simpa [I,Store.len_code,Store.ofCode_code] using initial
  obtain ⟨last,run,ok,done⟩ := coded_while_measure goal scanBody measure measureDef I invariant next s.code ready
  let t := Store.ofCode last
  have code : t.code = last := Store.code_ofCode ok.1
  exact ⟨t,code.symm ▸ run,ok.2.1,done,ok.2.2⟩

end PalomarI3380.Compiler.Source
