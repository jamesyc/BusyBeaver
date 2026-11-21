module
public import I0451.Omega.ArithmeticConsequences
public import Internal.Arith.StandardSemantics

/-! A computably coded reading of arithmetic in a set model.
The interpretation uses the original omega operations. An arbitrary
set argument is read as zero if it lies outside omega, so the shared
proof compiler can use a total domain. -/
@[expose] public section
namespace I0451.Omega

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open ZF207.Internal.Arith ZF207.OmegaInterpretation
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

def numberValueDef : SetTheorySemisentence 2 :=
  “y x. (!domain x ∧ y = x) ∨ (¬!domain x ∧ !isEmpty y)”

def omegaReader : Interp where
  mark := isEmpty
  dom := “e x. ⊤”
  eq := “e x y. ∃ u v, !numberValueDef u x ∧ !numberValueDef v y ∧ u = v”
  lt := “e x y. ∃ u v, !numberValueDef u x ∧ !numberValueDef v y ∧ u ∈ v”
  zero := “e x. ∃ u, !numberValueDef u x ∧ !isEmpty u”
  one := “e x. ∃ u z, !isEmpty z ∧ !numberValueDef u x ∧ !succGraph u z”
  add := “e a b y. ∃ u v w, !numberValueDef u a ∧ !numberValueDef v b ∧ !numberValueDef w y ∧ !addGraph w v u”
  mul := “e a b y. ∃ u v w, !numberValueDef u a ∧ !numberValueDef v b ∧ !numberValueDef w y ∧ !mulGraph w v u”

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local notation "A" => arithmeticTranslation.Model V

noncomputable def projectOmega (x : V) : A := by
  classical
  exact if h : x ∈ (ω : V) then ⟨x, (domain_eval ![x]).mpr h⟩ else 0

theorem projectOmega_surjective : Function.Surjective (projectOmega (V := V)) := by
  intro x
  refine ⟨x.val, ?_⟩
  unfold projectOmega
  rw [dite_eq_left (model_mem_omega x)]

theorem numberValue_defines :
    DefinedFunction (fun v : Fin 1 → V => (projectOmega (v 0)).val) numberValueDef := by
  refine .mk fun v => ?_
  have empty : Defined (fun e : Fin 1 → V => e 0 = ∅) isEmpty := .mk zero_eval
  have natural : Defined (fun e : Fin 1 → V => e 0 ∈ (ω : V)) domain := .mk domain_eval
  classical
  by_cases h : v 1 ∈ (ω : V) <;>
    simp [numberValueDef, natural.iff, empty.iff, projectOmega, h, val_zero, zero_def]

attribute [local irreducible] numberValueDef

theorem omegaReader_reads (e : V) : Reads omegaReader e projectOmega := by
  have empty : Defined (fun v : Fin 1 → V => v 0 = ∅) isEmpty := .mk zero_eval
  refine ⟨projectOmega_surjective, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp [omegaReader]
  · intro x y
    simp [omegaReader, numberValue_defines.iff, Subtype.ext_iff]
  · intro x y
    simp [omegaReader, numberValue_defines.iff]
  · intro x
    simp [omegaReader, numberValue_defines.iff, empty.iff]
    rw [← model_zero_value (V := V)]
    exact ⟨DirectTranslation.Model.ext, congrArg DirectTranslation.Model.val⟩
  · intro x
    simp [omegaReader, numberValue_defines.iff, empty.iff, succ.defined.iff, eq_comm]
    rw [← model_one_value (V := V)]
    exact ⟨DirectTranslation.Model.ext, congrArg DirectTranslation.Model.val⟩
  · intro a b y
    simp [omegaReader, numberValue_defines.iff, add_graph_defined.iff, eq_comm]
    rw [← val_add]
    exact ⟨DirectTranslation.Model.ext, congrArg DirectTranslation.Model.val⟩
  · intro a b y
    simp [omegaReader, numberValue_defines.iff, mul_graph_defined.iff, eq_comm]
    rw [← val_mul]
    exact ⟨DirectTranslation.Model.ext, congrArg DirectTranslation.Model.val⟩


section Syntax

variable {W : Type} [ORingStructure W] [W↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def omegaReaderCodeDef : 𝚺ᴬ₁.Semisentence 2 :=
  .mkSigma “y σ. ∃ b, !qqBvarDef b 0 ∧ ∃ m, !(markAtDef omegaReader) m b ∧
    ∃ j, !(JDef omegaReader) j b 1 σ ∧ ∃ i, !(impGraph ℒₛₑₜ) i m j ∧ !qqAllDef y i”

theorem omegaReaderCode_defines : 𝚺ᴬ₁-Function₁ (kax omegaReader : W → W) via omegaReaderCodeDef :=
  .mk fun v => by
    simp [omegaReaderCodeDef, kax, jhat, (markAt_defined omegaReader).iff,
      (J_defined omegaReader).iff, imp.defined.iff]

theorem omegaReaderCode_defined : 𝚺ᴬ₁-Function₁ (kax omegaReader : W → W) :=
  omegaReaderCode_defines.to_definable

theorem omegaReaderCode_fixed {σ : W} (wf : IsFormula ℒₒᵣ σ) (closed : shift ℒₒᵣ σ = σ) :
    shift ℒₛₑₜ (kax omegaReader σ) = kax omegaReader σ := by
  have mark : IsSemiformula ℒₛₑₜ 1 (markAt omegaReader (^#0 : W)) :=
    markAt_semiformula omegaReader (by simp)
  have translated := jhat_semiformula omegaReader wf
  have bound : IsSemiformula ℒₒᵣ 1 σ := ⟨wf.isUFormula, le_trans wf.bv_le (by simp)⟩
  have body : shift ℒₛₑₜ (jhat omegaReader σ) = jhat omegaReader σ := by
    have commute := J_shift omegaReader 1 σ bound (^#0) (by simp)
    simpa [jhat, closed] using commute.symm
  have marker : shift ℒₛₑₜ (markAt omegaReader (^#0 : W)) = markAt omegaReader (^#0 : W) := by
    rw [shift_markAt omegaReader (show IsSemiterm ℒₛₑₜ 1 (^#0 : W) by simp)]; simp
  simp [kax, Bootstrapping.imp, mark.isUFormula, translated.isUFormula, shift_neg mark, marker, body]

end Syntax

theorem reader_closed (σ : ArithmeticSentence) :
    (kaxP omegaReader σ).freeVariables = ∅ := by
  apply Semiformula.freeVariables_eq_empty_of_shift_eq
  apply (Semiformula.quote_inj_iff (V := Nat)).mp
  rw [Semiformula.quote_shift, quote_kaxP]
  apply omegaReaderCode_fixed (Sentence.quote_isSemiformula₀ σ)
  rw [Sentence.quote_def, ← Semiformula.quote_shift]
  congr 1
  unfold Rewriting.emb Rewriting.shift
  rw [← TransitiveRewriting.comp_app]
  congr 2
  ext x <;> simp

def readArithmetic (σ : ArithmeticSentence) : SetTheorySentence :=
  (kaxP omegaReader σ).toEmpty (reader_closed σ)

theorem quote_readArithmetic (σ : ArithmeticSentence) :
    (⌜readArithmetic σ⌝ : Nat) = kax omegaReader (⌜σ⌝ : Nat) := by
  rw [Sentence.quote_def, readArithmetic, Semiformula.emb_toEmpty, quote_kaxP]

theorem readArithmetic_models (σ : ArithmeticSentence) :
    V↓[ℒₛₑₜ] ⊧ readArithmetic σ ↔ A↓[ℒₒᵣ] ⊧ σ := by
  have evalEq : V↓[ℒₛₑₜ] ⊧ readArithmetic σ ↔
      (kaxP omegaReader σ).Eval ![] (fun _ => (∅ : V)) := by
    unfold readArithmetic
    exact (Semiformula.eval_toEmpty (f := fun _ : Nat => (∅ : V)) (reader_closed σ)).symm
  rw [evalEq]
  simp only [kaxP, Semiformula.eval_all, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, eval_tpl]
  have args (x : V) : (fun i => Semiterm.val ![x] (fun _ => (∅ : V))
      ((![#0] : Fin 1 → Semiterm ℒₛₑₜ Nat 1) i)) = ![x] := by
    funext i
    rw [Fin.fin_one_eq_zero i]
    rfl
  simp only [args, LogicalConnective.Prop.or_eq, LogicalConnective.Prop.neg_eq]
  have formula (x : V) :
      (Jx omegaReader #0 (Rew.castLE (by simp : 0 ≤ 1) ▹ (Rewriting.emb σ : Proposition ℒₒᵣ))).Eval
        ![x] (fun _ => (∅ : V)) ↔ A↓[ℒₒᵣ] ⊧ σ := by
    rw [eval_Jx (omegaReader_reads x) _ (#0) ![x] _ (by simp)]
    simp [Semiformula.eval_castLE, Semiformula.eval_emb, models_iff, Semiformula.Realize, Matrix.empty_eq]
  rw [show (∀ x : V, ¬ V ⊧/![x] omegaReader.mark ∨
      (Jx omegaReader #0 (Rew.castLE (by simp : 0 ≤ 1) ▹ (Rewriting.emb σ : Proposition ℒₒᵣ))).Eval
        ![x] (fun _ => (∅ : V))) ↔ _ from forall_congr' fun x => or_congr Iff.rfl (formula x)]
  have marker : V ⊧/![∅] omegaReader.mark := by simp [omegaReader, isEmpty, models_iff]
  exact ⟨fun h => (h ∅).resolve_left (fun fails => fails marker), fun holds _ => .inr holds⟩

end I0451.Omega
