module
public import Halting.Templates
public import Halting.GateHull
public import ConcreteArithmeticProofTransport
@[expose] public section
/-! # Absorb, base, the template facts and the marker axiom

Models of `U` carry pointed hulls on their indiscernibility quotient (`gateHull_of_U`), so at
every empty marker the templates read the natural numbers of a ZF model (`reads`). Hence `U`
proves:
* `kaxS ψ` whenever ZF proves `ψ` in ω, so `T ⊢ ψ` (`absorb`), and `𝗣𝗔 ⪯ T` (`base`);
* the template facts (`interpFacts`) and `∃e Mark e` (`markAx_U`). -/
namespace ZF207.Halting
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.SetTheory FFL.Entailment
open ZF207.Independence ZF207.GateModel ZF207.OmegaInterpretation ZF207.Internal.Arith

/-! ## The sentence `kaxS ψ` -/

lemma kaxP_shift (σ : Sentence ℒₒᵣ) :
    Bootstrapping.shift ℒₛₑₜ (⌜kaxP tmpl σ⌝ : ℕ) = ⌜kaxP tmpl σ⌝ := by
  rw [quote_kaxP]
  exact kax_shift tmpl (Sentence.quote_isSemiformula₀ σ) (shift_quote_sentence σ)

/-- `∀e (Mark e → Ĵψ)` as a sentence. -/
noncomputable def kaxS (σ : Sentence ℒₒᵣ) : Sentence ℒₛₑₜ :=
  Classical.choose (exists_sentence_of_shift ℒₛₑₜ (kaxP_shift σ))

lemma kaxS_spec (σ : Sentence ℒₒᵣ) : kaxP tmpl σ = Rewriting.emb (kaxS σ) :=
  Classical.choose_spec (exists_sentence_of_shift ℒₛₑₜ (kaxP_shift σ))

lemma quote_kaxS (σ : Sentence ℒₒᵣ) : (⌜kaxS σ⌝ : ℕ) = kax tmpl (⌜σ⌝ : ℕ) := by
  rw [Sentence.quote_def, ← kaxS_spec, quote_kaxP]

/-! ## Meaning of `kaxS` -/

section Meaning
variable {W : Type*} [SetStructure W] [Nonempty W] [GateHull (NQ (fun x y : W => x ∈ y))]

lemma kaxS_iff (σ : Sentence ℒₒᵣ) : W↓[ℒₛₑₜ] ⊧ kaxS σ ↔ ∀ (e : W) (he : ∀ y, y ∉ e),
    (Semiformula.Eval (M := arithmeticTranslation.Model (WFPart (Q (nq_isEmpty
      (mem := fun x y : W => x ∈ y) he)))) ![] Empty.elim) σ := by
  have h0 : W↓[ℒₛₑₜ] ⊧ kaxS σ ↔ (kaxP tmpl σ).Eval ![] (fun _ => Classical.arbitrary W) := by
    rw [kaxS_spec, models_iff, Semiformula.eval_emb]
  rw [h0]
  simp only [kaxP, Semiformula.eval_all, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, eval_tpl]
  have hm : ∀ x : W, (fun i => Semiterm.val ![x] (fun _ => Classical.arbitrary W)
      ((![#0] : Fin 1 → Semiterm ℒₛₑₜ ℕ 1) i)) = ![x] := by
    intro x; funext i; rw [Fin.fin_one_eq_zero i]; rfl
  simp only [hm]
  apply forall_congr'
  intro x
  by_cases he : ∀ y, y ∉ x
  · have hx : W ⊧/![x] tmpl.mark := by simpa [tmpl, emptyF] using he
    simp only [hx, LogicalConnective.Prop.neg_eq, not_true, LogicalConnective.Prop.or_eq, false_or]
    rw [eval_Jx (reads he) _ (#0) ![x] _ (by simp)]
    simp only [Semiformula.eval_castLE, Semiformula.eval_emb]
    exact ⟨fun H _ => by simpa [Matrix.empty_eq, Empty.eq_elim] using H,
      fun H => by simpa [Matrix.empty_eq, Empty.eq_elim] using H he⟩
  · have hx : ¬W ⊧/![x] tmpl.mark := by simpa [tmpl, emptyF] using he
    simp only [hx, LogicalConnective.Prop.neg_eq, not_false_eq_true, LogicalConnective.Prop.or_eq,
      true_or, true_iff]
    exact fun h => absurd h he

end Meaning

/-! ## Absorb and base -/

/-- `U` proves the marker translation of every ZF-theorem read in ω. -/
theorem U_kaxS {ψ : ArithmeticSentence}
    (h : (𝗭𝗙 : SetTheory) ⊢ arithmeticTranslation.translate ψ) : theoryU ⊢ kaxS ψ := by
  apply SetTheory.complete.{0}
  intro W _ _ _
  have := gateHull_of_U (W := W)
  rw [kaxS_iff]
  intro e he
  have hN := models_of_provable
    (inferInstance : (WFPart (Q (nq_isEmpty (mem := fun x y : W => x ∈ y) he)))↓[ℒₛₑₜ] ⊧* 𝗭𝗙) h
  have ht := DirectTranslation.Model.translate_iff (π := arithmeticTranslation)
    (M := WFPart (Q (nq_isEmpty (mem := fun x y : W => x ∈ y) he))) (σ := ψ)
  rw [interpreted_structure_eq_standard (V := WFPart (Q (nq_isEmpty (mem := fun x y : W => x ∈ y) he)))] at ht
  simpa [models_iff, Matrix.empty_eq] using ht.mp hN

/-- Absorb: ZF-theorems read in ω are theorems of `T`. -/
theorem absorb {ψ : ArithmeticSentence}
    (h : (𝗭𝗙 : SetTheory) ⊢ arithmeticTranslation.translate ψ) : theoryT tmpl ⊢ ψ := by
  apply T_of_cprov tmpl
  rw [← quote_kaxS]
  exact cprov_of_U (U_kaxS h)

theorem pa_weaker : 𝗣𝗔 ⪯ theoryT tmpl :=
  weakerThan_iff.mpr fun hp => absorb (pa_proof_to_zf hp)

theorem base : 𝗜𝚺₁ ⪯ theoryT tmpl :=
  haveI := pa_weaker
  Entailment.WeakerThan.trans inferInstance this

/-! ## The template facts -/

section Trivial
variable {W : Type*} [SetStructure W] {e : W} (he : ¬∀ y, y ∉ e)
include he

lemma not_mark : ¬W ⊧/![e] emptyF := by simpa [emptyF] using he

lemma triv_eq (x y : W) : W ⊧/![e, x, y] tmpl.eq :=
  (tmpl_eq_eval e x y).mpr fun h => absurd h (not_mark he)
lemma triv_lt (x y : W) : W ⊧/![e, x, y] tmpl.lt :=
  (tmpl_lt_eval e x y).mpr fun h => absurd h (not_mark he)
lemma triv_zero (y : W) : W ⊧/![e, y] tmpl.zero :=
  (tmpl_zero_eval e y).mpr fun h => absurd h (not_mark he)
lemma triv_one (y : W) : W ⊧/![e, y] tmpl.one :=
  (tmpl_one_eval e y).mpr fun h => absurd h (not_mark he)
lemma triv_add (a b y : W) : W ⊧/![e, a, b, y] tmpl.add :=
  (tmpl_add_eval e a b y).mpr fun h => absurd h (not_mark he)
lemma triv_mul (a b y : W) : W ⊧/![e, a, b, y] tmpl.mul :=
  (tmpl_mul_eval e a b y).mpr fun h => absurd h (not_mark he)

end Trivial

/-- To prove a sentence in `U`, check it in models with pointed hulls. -/
lemma U_of_models {φ : Sentence ℒₛₑₜ}
    (H : ∀ (W : Type) [SetStructure W] [Nonempty W] [GateHull (NQ (fun x y : W => x ∈ y))],
      W↓[ℒₛₑₜ] ⊧ φ) : theoryU ⊢ φ := by
  apply SetTheory.complete.{0}
  intro W _ _ _
  have := gateHull_of_U (W := W)
  exact H W

/-- The template facts hold in `U`. -/
theorem interpFacts : InterpFacts tmpl theoryU where
  dom_all := by
    refine U_of_models fun W _ _ _ => ?_
    simp [models_iff, tmpl]
  eq_refl := by
    refine U_of_models fun W _ _ _ => ?_
    simp only [models_iff]; simp
    intro e x
    by_cases he : ∀ y, y ∉ e
    · have R := reads he
      exact (R.eq x x).mpr rfl
    · exact triv_eq he x x
  eq_symm := by
    refine U_of_models fun W _ _ _ => ?_
    simp only [models_iff]; simp
    intro e x y
    by_cases he : ∀ y, y ∉ e
    · have R := reads he
      intro h; exact (R.eq y x).mpr ((R.eq x y).mp h).symm
    · intro _; exact triv_eq he y x
  eq_trans := by
    refine U_of_models fun W _ _ _ => ?_
    simp only [models_iff]; simp
    intro e x y z
    by_cases he : ∀ y, y ∉ e
    · have R := reads he
      intro h₁ h₂; exact (R.eq x z).mpr (((R.eq x y).mp h₁).trans ((R.eq y z).mp h₂))
    · intro _ _; exact triv_eq he x z
  zero_ex := by
    refine U_of_models fun W _ _ _ => ?_
    simp only [models_iff]; simp
    intro e
    by_cases he : ∀ y, y ∉ e
    · have R := reads he
      obtain ⟨y, hy⟩ := R.surj 0; exact ⟨y, (R.zero y).mpr hy⟩
    · exact ⟨e, triv_zero he e⟩
  one_ex := by
    refine U_of_models fun W _ _ _ => ?_
    simp only [models_iff]; simp
    intro e
    by_cases he : ∀ y, y ∉ e
    · have R := reads he
      obtain ⟨y, hy⟩ := R.surj 1; exact ⟨y, (R.one y).mpr hy⟩
    · exact ⟨e, triv_one he e⟩
  add_ex := by
    refine U_of_models fun W _ _ _ => ?_
    simp only [models_iff]; simp
    intro e a b
    by_cases he : ∀ y, y ∉ e
    · have R := reads he
      obtain ⟨y, hy⟩ := R.surj (pr he a + pr he b); exact ⟨y, (R.add a b y).mpr hy.symm⟩
    · exact ⟨e, triv_add he a b e⟩
  mul_ex := by
    refine U_of_models fun W _ _ _ => ?_
    simp only [models_iff]; simp
    intro e a b
    by_cases he : ∀ y, y ∉ e
    · have R := reads he
      obtain ⟨y, hy⟩ := R.surj (pr he a * pr he b); exact ⟨y, (R.mul a b y).mpr hy.symm⟩
    · exact ⟨e, triv_mul he a b e⟩
  zero_fun := by
    refine U_of_models fun W _ _ _ => ?_
    simp only [models_iff]; simp
    intro e y z
    by_cases he : ∀ y, y ∉ e
    · have R := reads he
      intro h₁ h₂; exact (R.eq y z).mpr (((R.zero y).mp h₁).trans ((R.zero z).mp h₂).symm)
    · intro _ _; exact triv_eq he y z
  one_fun := by
    refine U_of_models fun W _ _ _ => ?_
    simp only [models_iff]; simp
    intro e y z
    by_cases he : ∀ y, y ∉ e
    · have R := reads he
      intro h₁ h₂; exact (R.eq y z).mpr (((R.one y).mp h₁).trans ((R.one z).mp h₂).symm)
    · intro _ _; exact triv_eq he y z
  add_fun := by
    refine U_of_models fun W _ _ _ => ?_
    simp only [models_iff]; simp
    intro e a b y z
    by_cases he : ∀ y, y ∉ e
    · have R := reads he
      intro h₁ h₂; exact (R.eq y z).mpr (((R.add a b y).mp h₁).symm.trans ((R.add a b z).mp h₂))
    · intro _ _; exact triv_eq he y z
  mul_fun := by
    refine U_of_models fun W _ _ _ => ?_
    simp only [models_iff]; simp
    intro e a b y z
    by_cases he : ∀ y, y ∉ e
    · have R := reads he
      intro h₁ h₂; exact (R.eq y z).mpr (((R.mul a b y).mp h₁).symm.trans ((R.mul a b z).mp h₂))
    · intro _ _; exact triv_eq he y z
  zero_cong := by
    refine U_of_models fun W _ _ _ => ?_
    simp only [models_iff]; simp
    intro e y z
    by_cases he : ∀ y, y ∉ e
    · have R := reads he
      intro h₁ h₂; exact (R.zero z).mpr (((R.eq y z).mp h₁).symm.trans ((R.zero y).mp h₂))
    · intro _ _; exact triv_zero he z
  one_cong := by
    refine U_of_models fun W _ _ _ => ?_
    simp only [models_iff]; simp
    intro e y z
    by_cases he : ∀ y, y ∉ e
    · have R := reads he
      intro h₁ h₂; exact (R.one z).mpr (((R.eq y z).mp h₁).symm.trans ((R.one y).mp h₂))
    · intro _ _; exact triv_one he z
  add_cong₁ := by
    refine U_of_models fun W _ _ _ => ?_
    simp only [models_iff]; simp
    intro e a c b y
    by_cases he : ∀ y, y ∉ e
    · have R := reads he
      intro h₁ h₂; exact (R.add c b y).mpr (by rw [← (R.eq a c).mp h₁]; exact (R.add a b y).mp h₂)
    · intro _ _; exact triv_add he c b y
  add_cong₂ := by
    refine U_of_models fun W _ _ _ => ?_
    simp only [models_iff]; simp
    intro e a b c y
    by_cases he : ∀ y, y ∉ e
    · have R := reads he
      intro h₁ h₂; exact (R.add a c y).mpr (by rw [← (R.eq b c).mp h₁]; exact (R.add a b y).mp h₂)
    · intro _ _; exact triv_add he a c y
  add_cong₃ := by
    refine U_of_models fun W _ _ _ => ?_
    simp only [models_iff]; simp
    intro e a b y z
    by_cases he : ∀ y, y ∉ e
    · have R := reads he
      intro h₁ h₂; exact (R.add a b z).mpr (by rw [← (R.eq y z).mp h₁]; exact (R.add a b y).mp h₂)
    · intro _ _; exact triv_add he a b z
  mul_cong₁ := by
    refine U_of_models fun W _ _ _ => ?_
    simp only [models_iff]; simp
    intro e a c b y
    by_cases he : ∀ y, y ∉ e
    · have R := reads he
      intro h₁ h₂; exact (R.mul c b y).mpr (by rw [← (R.eq a c).mp h₁]; exact (R.mul a b y).mp h₂)
    · intro _ _; exact triv_mul he c b y
  mul_cong₂ := by
    refine U_of_models fun W _ _ _ => ?_
    simp only [models_iff]; simp
    intro e a b c y
    by_cases he : ∀ y, y ∉ e
    · have R := reads he
      intro h₁ h₂; exact (R.mul a c y).mpr (by rw [← (R.eq b c).mp h₁]; exact (R.mul a b y).mp h₂)
    · intro _ _; exact triv_mul he a c y
  mul_cong₃ := by
    refine U_of_models fun W _ _ _ => ?_
    simp only [models_iff]; simp
    intro e a b y z
    by_cases he : ∀ y, y ∉ e
    · have R := reads he
      intro h₁ h₂; exact (R.mul a b z).mpr (by rw [← (R.eq y z).mp h₁]; exact (R.mul a b y).mp h₂)
    · intro _ _; exact triv_mul he a b z

/-- `U` proves `∃e Mark e`. -/
theorem markAx_U : theoryU ⊢ markAx tmpl := by
  apply SetTheory.complete.{0}
  intro W _ _ _
  obtain ⟨e, he⟩ := empty_of_U (W := W)
  simp only [models_iff, markAx, tmpl]
  simpa [emptyF] using ⟨e, he⟩

end ZF207.Halting
