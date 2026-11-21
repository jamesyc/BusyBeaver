module
public import I0451.Standalone.Statement
public import I0451.Independence
public import I0451.Standalone.SigmaReflection

/-! Align the independent membership-model statement with the
proof-theoretic formulation and its exact literal tape. -/
@[expose] public section
namespace I0451.Standalone

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open I0451.Logic (NamedFormula berkeleyTheory zfcI0 zfI0)
open I0451.Logic.SetAssignments
open ZF207.OmegaInterpretation

def foundationTheory : Theory → SetTheory
  | .berkeley => berkeleyTheory
  | .zfcI0 => zfcI0
  | .zfI0 => zfI0

instance (T : Theory) : 𝗭𝗙 ⪯ foundationTheory T := by
  cases T <;> simp only [foundationTheory] <;> infer_instance

instance (T : Theory) : 𝗘𝗤 ℒₛₑₜ ⪯ foundationTheory T :=
  WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₛₑₜ ⪯ 𝗭𝗙) inferInstance

attribute [local irreducible] I0451.Logic.i0SetAxiom berkeleySetAxiom I0451.i0Consistency

set_option maxHeartbeats 1200000 in
theorem models_iff_foundation {V : Type} [SetStructure V] [Nonempty V] (T : Theory) :
    Models T (fun x y : V => x ∈ y) ↔ V↓[ℒₛₑₜ] ⊧* foundationTheory T := by
  have equivalence (φ : SetTheorySentence) :
      (∀ s, eval (fun x y : V => x ∈ y) s (ofFoundationSentence φ)) ↔ V↓[ℒₛₑₜ] ⊧ φ :=
    ⟨fun h => (ofFoundationSentence_eval φ (fun _ => Classical.arbitrary V)).mp (h _),
      fun h s => (ofFoundationSentence_eval φ s).mpr h⟩
  constructor
  · intro ⟨base, extra⟩
    have ZF := zf_of_model base
    constructor
    intro σ declared
    cases T with
    | berkeley =>
      change σ ∈ 𝗭𝗙 ∪ {berkeleySetAxiom} at declared
      rcases declared with zf | ax
      · exact ZF.models_set zf
      · have eq : σ = berkeleySetAxiom := ax
        rw [eq]
        exact (equivalence _).mp extra
    | zfI0 =>
      change σ ∈ 𝗭𝗙 ∪ {I0451.Logic.i0SetAxiom} at declared
      rcases declared with zf | ax
      · exact ZF.models_set zf
      · have eq : σ = I0451.Logic.i0SetAxiom := ax
        rw [eq]
        exact (equivalence _).mp extra
    | zfcI0 =>
      change σ ∈ (𝗭𝗙 ∪ 𝗔𝗖) ∪ {I0451.Logic.i0SetAxiom} at declared
      rcases declared with (zf | choice) | ax
      · exact ZF.models_set zf
      · have eq : σ = Axiom.choice := choice
        rw [eq]
        exact choice_iff.mp extra.1
      · have eq : σ = I0451.Logic.i0SetAxiom := ax
        rw [eq]
        exact (equivalence _).mp extra.2
  · intro modeled
    let : V↓[ℒₛₑₜ] ⊧* foundationTheory T := modeled
    let : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := models_of_subtheory (U := foundationTheory T) inferInstance
    refine ⟨model_of_zf, ?_⟩
    cases T with
    | berkeley => exact (equivalence _).mpr (modeled.models_set (.inr rfl))
    | zfI0 => exact (equivalence _).mpr (modeled.models_set (.inr rfl))
    | zfcI0 =>
      exact ⟨choice_iff.mpr (modeled.models_set (.inl (.inr rfl))),
        (equivalence _).mpr (modeled.models_set (.inr rfl))⟩

private theorem valid_of_interpretation (T : Theory) {f : NamedFormula} {φ : SetTheorySentence}
    (meaning : ∀ (V : Type) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (s : Nat → V),
      eval (fun x y : V => x ∈ y) s f ↔ V↓[ℒₛₑₜ] ⊧ φ) :
    Provable T f ↔ foundationTheory T ⊢ φ := by
  constructor
  · intro valid
    apply SetTheory.complete.{0}
    intro V _ _ model
    let s : Nat → V := fun _ => Classical.arbitrary V
    let : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := models_of_subtheory (U := foundationTheory T) model
    exact (meaning V s).mp (valid V _ inferInstance ((models_iff_foundation T).mpr model) s)
  · intro proof V E nonempty model s
    let : Nonempty V := nonempty
    let : SetStructure V := ⟨fun a b => E b a⟩
    have target := (models_iff_foundation T).mp model
    let : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := models_of_subtheory (U := foundationTheory T) target
    exact (meaning V s).mpr (models_of_provable target proof)

theorem provable_iff (T : Theory) (φ : SetTheorySentence) :
    Provable T (ofFoundationSentence φ) ↔ foundationTheory T ⊢ φ :=
  valid_of_interpretation T (fun _ _ _ _ s => ofFoundationSentence_eval φ s)

theorem provable_negation_iff (T : Theory) (φ : SetTheorySentence) :
    Provable T (.imp (ofFoundationSentence φ) .falsity) ↔ foundationTheory T ⊢ ∼φ :=
  valid_of_interpretation T (fun V _ _ _ s => by
    simp only [eval, models_iff, Semiformula.Realize, LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
    exact not_congr (ofFoundationSentence_eval φ s))

theorem represents {p : ArithmeticSentence} (shaped : SigmaBridge.Good p) :
    RepresentsArithmetic (SigmaBridge.formula p) (ofFoundationSentence (arithmeticTranslation.translate p)) := by
  refine ⟨SigmaBridge.formula_bound p shaped, ofFoundationSentence_closed _, ?_⟩
  intro V E nonempty model s env _
  let : Nonempty V := nonempty
  let : SetStructure V := ⟨fun a b => E b a⟩
  let : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := zf_of_model model
  have ordinary := I0451.Omega.translated_models (V := V) p
  have arithmetic := SigmaBridge.formula_zf (V := V) p shaped ![] env (fun i => i.elim0)
  have rel : (fun x y : V => x ∈ y) = E := rfl
  rw [rel] at arithmetic
  exact (ofFoundationSentence_eval _ s).trans (ordinary.trans (by
    simpa only [models_iff, Semiformula.Realize, ← Semiformula.Evalb.eq_1] using arithmetic.symm))

theorem sound_zfcI0 (sound : SigmaOneSound .zfcI0) : ArithmeticSigmaOneSound zfcI0 := by
  intro σ proof
  have good : SigmaBridge.Good σ.val := SigmaBridge.good_of_hierarchy σ.sigma_prop (.inl ⟨rfl, le_rfl⟩)
  have truth := sound _ _ (represents good) ((provable_iff .zfcI0 _).mpr proof) (fun _ => 0)
  have out := (SigmaBridge.formula_nat σ.val good ![] (fun _ => 0) (fun i => i.elim0)).mp truth
  simpa only [models_iff, Semiformula.Realize, ← Semiformula.Evalb.eq_1] using out

/-- The standalone hypothesis ranges over exactly the ordinary Σ₁
sentences, with their correct semantics in every ZF model. -/
theorem sigma_sound_iff : SigmaOneSound .zfcI0 ↔ ArithmeticSigmaOneSound zfcI0 := by
  refine ⟨sound_zfcI0, ?_⟩
  intro sound p φ semantic valid s
  let reflected := SigmaBridge.reflect 0 p semantic.1
  have good : SigmaBridge.Good reflected.expression.val :=
    SigmaBridge.good_of_hierarchy reflected.expression.sigma_prop (.inl ⟨rfl, le_rfl⟩)
  let sentence := arithmeticTranslation.translate reflected.expression.val
  have faithful : RepresentsArithmetic p (ofFoundationSentence sentence) :=
    Eq.mp (congrArg (fun q => RepresentsArithmetic q (ofFoundationSentence sentence)) reflected.sameSyntax)
      (represents good)
  have meaning (V : Type) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (env : Nat → V) :
      eval (fun x y : V => x ∈ y) env φ ↔ V↓[ℒₛₑₜ] ⊧ sentence := by
    have natural (i : Nat) : NatObject (fun x y : V => x ∈ y) ((fun _ : Nat => (∅ : V)) i) :=
      (natObject_iff _).mpr empty_mem_ω
    exact (semantic.2.2 V _ inferInstance model_of_zf env (fun _ => ∅) natural).trans
      ((faithful.2.2 V _ inferInstance model_of_zf env (fun _ => ∅) natural).symm.trans
        (ofFoundationSentence_eval _ env))
  have source : zfcI0 ⊢ arithmeticTranslation.translate reflected.expression.val :=
    (valid_of_interpretation .zfcI0 meaning).mp valid
  have trueArithmetic := sound reflected.expression source
  have truth := (SigmaBridge.formula_nat reflected.expression.val good ![] s (fun i => i.elim0)).mpr
    (by simpa only [models_iff, Semiformula.Realize, ← Semiformula.Evalb.eq_1] using trueArithmetic)
  simpa only [reflected.sameSyntax] using truth

set_option maxHeartbeats 1300000 in
theorem exact451Claim : Claim451 := by
  have good : SigmaBridge.Good arithmeticHalting.val :=
    SigmaBridge.good_of_hierarchy arithmeticHalting.sigma_prop (.inl ⟨rfl, le_rfl⟩)
  refine ⟨?_, ofFoundationSentence setHalting, represents good, ?_⟩
  · intro s
    exact (SigmaBridge.formula_nat _ good ![] s (fun i => i.elim0)).trans
      (by simpa only [models_iff, Semiformula.Realize, ← Semiformula.Evalb.eq_1] using arithmetic_halts_exact)
  · intro consistent sound relative
    have conB : Entailment.Consistent berkeleyTheory := by
      apply Entailment.consistent_iff_unprovable_bot.mpr
      exact fun bad => consistent
        ((valid_of_interpretation .berkeley (φ := ⊥) (f := .falsity) (fun _ _ _ _ _ => Iff.rfl)).mpr bad)
    have woodin : WoodinConsistency :=
      (provable_iff .berkeley (arithmeticTranslation.translate i0Consistency)).mp relative
    obtain ⟨never, ⟨noHalt, noNonhalt⟩, ⟨noHaltZF, noNonhaltZF⟩⟩ :=
      exact451_independence conB (sound_zfcI0 sound) woodin
    exact ⟨never, ⟨fun h => noHalt ((provable_iff .zfcI0 _).mp h),
        fun h => noNonhalt ((provable_negation_iff .zfcI0 _).mp h)⟩,
      ⟨fun h => noHaltZF ((provable_iff .zfI0 _).mp h),
        fun h => noNonhaltZF ((provable_negation_iff .zfI0 _).mp h)⟩⟩

end I0451.Standalone
