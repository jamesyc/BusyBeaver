module
public import I3_334.Calibration.ModelScanBody
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380 PalomarI3380.Compiler
open PalomarI3380.Compiler.Source (whilePositive coded_while_measure)
open ArithmeticMachine.SourceCantor
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem modelScan_drops (slot : Fin 4) (s : Store M) (pending : s goal ≠ 0) :
    modelScanStep slot (s.set goal (s goal-1)) goal +
      modelScanStep slot (s.set goal (s goal-1)) tmp < s goal + s tmp := by
  have same : (s.set goal (s goal-1)) tmp = s tmp := Store.get_set_other _ _ _ _ (by decide)
  rw [modelScanStep_goal,modelScanStep_tmp,Store.get_set,same]
  have bound : decodeLeft (s tmp)+decodeRight (decodeRight (s tmp)) ≤ s tmp :=
    (add_le_add (le_refl _) (decodeValue_bounds (decodeRight (s tmp))).2).trans (decode_sum_le (s tmp))
  have fewer : s goal-1 < s goal := Arithmetic.pred_lt_self_of_pos (pos_iff_ne_zero.mpr pending)
  rw [add_assoc]
  exact (add_le_add_right bound _).trans_lt (add_lt_add_left fewer _)

theorem coded_scanLoop_total [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (slot : Fin 4) (s : Store M) (initial : Scratch s) :
    ∃ t : Store M, (whilePositive goal (scanBody slot)).Runs .normal s.code t.code ∧
      Scratch t ∧ t goal = 0 ∧ ∀ r ∉ [goal,tmp,fr,gues], t r = s r := by
  let scanRegisters := [goal,tmp,fr,gues]
  let measure := fun code : M => Store.ofCode code goal + Store.ofCode code tmp
  have goalRead := Store.read_definable (M := M) goal
  have dictionaryRead := Store.read_definable (M := M) tmp
  have measureDef : 𝚺ᴬ₁-Function₁ measure := by unfold measure; definability
  let I := fun code : M => len code = 12 ∧ Scratch (Store.ofCode code) ∧
    ∀ r ∉ scanRegisters, Store.ofCode code r = s r
  have reading (r : Register) := Store.read_definable (M := M) r
  have fixedRegisters : 𝚺ᴬ₁-Predicate (fun code : M =>
      ∀ r ∉ scanRegisters, Store.ofCode code r = s r) := by
    apply Bounding.HierarchySymbol.Definable.fintype_all
    intro r
    have read := reading r
    by_cases altered : r ∈ scanRegisters <;> simp [altered] <;> definability
  have invariant : 𝚺ᴬ₁-Predicate I := by
    simp only [I,Scratch.iff_fields]
    have e := reading expected
    have t := reading tok
    have a := reading u
    definability
  have next : ∀ code : M, I code → Store.ofCode code goal ≠ 0 →
      ∃ after : M, (scanBody slot).Runs .normal
        (Store.writeCode goal code (Store.ofCode code goal-1)) after ∧
        I after ∧ measure after < measure code := by
    intro code valid positive
    let state := Store.ofCode code
    let mid := state.set goal (state goal-1)
    have before : Scratch mid := by
      simpa [Scratch.iff_fields,mid,Store.set,goal,expected,tok,u] using
        (Scratch.iff_fields.mp valid.2.1)
    let after := modelScanStep slot mid
    have out := coded_scanBody slot mid before
    change (scanBody slot).Runs .normal mid.code after.code at out
    refine ⟨after.code,out,?_ ,?_⟩
    · unfold I
      rw [Store.len_code,Store.ofCode_code]
      refine ⟨rfl,modelScanStep_scratch slot mid before,fun r outside => ?_⟩
      have other : r ≠ goal := by
        intro wrong
        subst r
        exact outside (by simp [scanRegisters])
      exact (modelScanStep_preserves slot mid r outside).trans
        ((Store.get_set_other _ _ _ _ other).trans (valid.2.2 r outside))
    · simpa only [measure,Store.ofCode_code,after,mid,state] using modelScan_drops slot state positive
  have ready : I s.code := by
    simpa [I,Store.len_code,Store.ofCode_code] using initial
  obtain ⟨last,run,ok,done⟩ := coded_while_measure goal (scanBody slot) measure measureDef I invariant next s.code ready
  let t := Store.ofCode last
  have code : t.code = last := Store.code_ofCode ok.1
  exact ⟨t,code.symm ▸ run,ok.2.1,done,ok.2.2⟩


end PalomarI3334.SearchProgram
