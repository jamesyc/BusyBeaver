module
public import I0451.Omega.NativeTheories
public import I0451.Omega.ReaderFacts
public import I0451.Omega.IndependenceTransfer

/-! Transport an arithmetic refutation through the set interpretation
and the native proof compiler. The interpreter facts are obtained
from the ZF theorems of the native set presentation. -/
@[expose] public section
namespace I0451.Omega

open FFL FFL.Entailment FFL.FirstOrder FFL.FirstOrder.SetTheory FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open I0451.Arithmetization ZF207.Internal.Arith
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

private theorem insert_formulaSet {p s : V} (hp : IsFormula ℒₛₑₜ p) (hs : IsFormulaSet ℒₛₑₜ s) :
    IsFormulaSet ℒₛₑₜ (insert p s) := by
  intro y hy
  rcases mem_bitInsert_iff.mp hy with rfl | hy
  · exact hp
  · exact hs y hy

private theorem derivable_of_padding {U : SetTheory} [U.Δ₁] {p padding s : V}
    (hp : IsFormula ℒₛₑₜ p) (hv : IsFormula ℒₛₑₜ padding)
    (context : IsFormulaSet ℒₛₑₜ s) (available : p ^⋏ padding ∈ U.Δ₁Class) :
    Derivable U (insert p s) := by
  have withBody := insert_formulaSet hp context
  have pairForm : IsFormula ℒₛₑₜ (p ^⋏ padding) := by simp [hp, hv]
  have prem := Derivable.by_axm (insert_formulaSet pairForm withBody) _ (by simp) available
  apply Derivable.cut (p ^⋏ padding) prem
  rw [show Bootstrapping.neg ℒₛₑₜ (p ^⋏ padding) =
    Bootstrapping.neg ℒₛₑₜ p ^⋎ Bootstrapping.neg ℒₛₑₜ padding by simp [hp.isUFormula,hv.isUFormula]]
  have np := IsSemiformula.neg_iff.mpr hp
  have nv := IsSemiformula.neg_iff.mpr hv
  have any := insert_formulaSet (show IsFormula ℒₛₑₜ (Bootstrapping.neg ℒₛₑₜ p ^⋎ Bootstrapping.neg ℒₛₑₜ padding) by simp [np,nv]) withBody
  apply Derivable.or_m (p := Bootstrapping.neg ℒₛₑₜ p) (q := Bootstrapping.neg ℒₛₑₜ padding) (by simp)
  exact Derivable.em (insert_formulaSet np (insert_formulaSet nv any)) p (by simp) (by simp)

private theorem derivable_truths {U : SetTheory} [U.Δ₁] {s : V} (context : IsFormulaSet ℒₛₑₜ s) :
    ∀ stamp : V, Derivable U (insert (qqVerums stamp) s) := by
  intro stamp
  induction stamp using ISigma1.sigma1_succ_induction
  · definability
  · simpa using Derivable.verum (T := U) (insert_formulaSet (by simp) context) (by simp)
  · rename_i n ih
    rw [qqVerums_succ]
    have truth : IsFormula ℒₛₑₜ (qqVerums n : V) := IsSemiformula.qqVerums n
    have shape := insert_formulaSet (show IsFormula ℒₛₑₜ (^⊤ ^⋏ qqVerums n : V) by simp) context
    refine Derivable.and_m (p := ^⊤) (q := qqVerums n) (by simp) ?_ ?_
    · exact Derivable.verum (insert_formulaSet (by simp) shape) (by simp)
    · refine Derivable.wk (insert_formulaSet truth shape) ?_ ih
      intro y hy
      rcases mem_bitInsert_iff.mp hy with rfl | hy <;> simp [hy]

theorem native_arithmetic_axiom_step :
    AxStep omegaReader nativeArithmeticTheory nativeSetTheory V := by
  intro p member marker markerOK
  obtain ⟨s, _, n, _, rfl, sForm, sClosed, _, stamp⟩ :=
    (I0451.Logic.UniformCraig.mem_iff ℒₒᵣ nativeArithmeticEnumeration p).mp member
  have target := (nativeArithmeticEnumeration_eval s).mp
    ((I0451.Logic.UniformCraig.witness_spec nativeArithmeticEnumeration s).mpr ⟨n,stamp⟩)
  have targetForm := kax_formula omegaReader sForm
  obtain ⟨count, available⟩ := from_native_axiom targetForm (omegaReaderCode_fixed sForm sClosed) target
  have wfMarker : IsFormula ℒₛₑₜ (markAt omegaReader marker) := markAt_semiformula omegaReader markerOK
  have wfJ : IsFormula ℒₛₑₜ (J omegaReader marker 0 s) := J_semiformula omegaReader 0 s sForm marker markerOK
  have negMarker := IsSemiformula.neg_iff.mpr wfMarker
  have ctx : IsFormulaSet ℒₛₑₜ (insert (Bootstrapping.neg ℒₛₑₜ (markAt omegaReader marker))
    (insert (J omegaReader marker 0 s) (0 : V))) := pair_formulaSet negMarker wfJ
  have compile := derivable_of_kax' omegaReader sForm markerOK
    (derivable_of_padding targetForm (IsSemiformula.qqVerums count) ctx available)
  have distributes : J omegaReader marker 0 (s ^⋏ qqVerums n) =
      J omegaReader marker 0 s ^⋏ qqVerums n := by
    rw [J_and sForm.isUFormula (IsSemiformula.qqVerums (n := 0) n).isUFormula, J_verums]
  rw [distributes]
  have ctxFull := pair_formulaSet negMarker
    (show IsFormula ℒₛₑₜ (J omegaReader marker 0 s ^⋏ qqVerums n) by simp [wfJ])
  refine Derivable.and_m (p := J omegaReader marker 0 s) (q := qqVerums n)
    (by simp) ?_ (derivable_truths ctxFull n)
  refine Derivable.wk (insert_formulaSet wfJ ctxFull) ?_ compile
  intro y hy
  rcases mem_bitInsert_iff.mp hy with rfl | hy
  · simp
  · rcases mem_bitInsert_iff.mp hy with rfl | hy
    · simp
    · simp at hy

private theorem mark_quoted :
    markAt omegaReader (^#0 : V) = (⌜omegaReader.mark⌝ : V) := by
  have marked : IsSemiformula ℒₛₑₜ 1 (tq omegaReader.mark : V) := by
    simpa only [Nat.cast_one] using tq_semiformula (V := V) omegaReader.mark
  have vars : IsSemitermVec ℒₛₑₜ 1 1 (^#0 ∷ (0 : V)) := by
    rw [show (1 : V) = 0 + 1 by simp]
    simp
  have unchanged := subst_eq_self marked vars (fun i inside => by
    rcases (lt_one_iff_eq_zero.mp inside) with rfl
    simp)
  unfold markAt
  rw [unchanged]
  exact tq_eq _

theorem native_arithmetic_refutation_translates [𝗭𝗙 ⪯ nativeSetTheory]
    (refutation : Bootstrapping.Provable nativeArithmeticTheory (^⊥ : V)) : NativeDerivable (1 : V) := by
  obtain ⟨x, failed⟩ := stage_one nativeArithmeticTheory (omegaReader_facts nativeSetTheory)
    native_arithmetic_axiom_step refutation
  have existsMarker : nativeSetTheory ⊢ ∃¹ omegaReader.mark := by
    apply Entailment.WeakerThan.pbl (𝓢 := (𝗭𝗙 : SetTheory))
    apply SetTheory.complete.{0}
    intro W _ _ _
    simp [models_iff, omegaReader, isEmpty]
    exact ⟨∅, by simp⟩
  have marked := internal_provable_iff_internal_derivable.mp (internalize_provability (V := V) existsMarker)
  have witness : Derivable nativeSetTheory (insert (^∃ (markAt omegaReader (^#0 : V))) (0 : V)) := by
    simpa [mark_quoted, FirstOrder.Sentence.quote_ex, emptyset_def] using marked
  have descends := mark_descend omegaReader x failed
  have markerWf : IsSemiformula ℒₛₑₜ 1 (markAt omegaReader (^#0 : V)) :=
    markAt_semiformula omegaReader (by simp)
  have allDenied : Derivable nativeSetTheory
      (insert (^∀ (Bootstrapping.neg ℒₛₑₜ (markAt omegaReader (^#0 : V)))) (0 : V)) :=
    Derivable.all (IsSemiformula.neg_iff.mpr markerWf) (by simpa [markAt_free,setShift_zero] using descends)
  have contradiction : Derivable nativeSetTheory (0 : V) :=
    Derivable.cut (^∀ (Bootstrapping.neg ℒₛₑₜ (markAt omegaReader (^#0 : V))))
      (by simpa using allDenied) (by simpa [markerWf.isUFormula] using witness)
  exact native_set_refutation_translates
    (internal_provable_iff_internal_derivable.mpr
      (Derivable.wk (singleton_formulaSet (by simp)) (fun y hy => by simp at hy) contradiction))

end I0451.Omega
