module
public import I0451.Omega.CodedTranslation
public import I0451.Logic.Tait.Native
public import I0451.Logic.UniformCraig
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.D1

/-! A uniform witness-based presentation of the arithmetic and
set-language theorems certified by the machine's native calculus. -/
@[expose] public section
namespace I0451.Omega

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.SetTheory
open FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open I0451.Arithmetization I0451.Logic I0451.Logic.Tait

open ZF207.Internal.Arith ZF207.CKernel.Generic

noncomputable def nativeSetEnumeration : 𝚺ᴬ₁.Semisentence 1 :=
  .mkSigma “sentence. ∃ formula, !chiSDef formula 0 sentence ∧ !nativeDerivableDef formula”

noncomputable def nativeArithmeticEnumeration : 𝚺ᴬ₁.Semisentence 1 :=
  .mkSigma “sentence. ∃ form, !omegaReaderCodeDef form sentence ∧ !nativeSetEnumeration form”

def nativeSetTheory : SetTheory :=
  UniformCraig.theory ℒₛₑₜ nativeSetEnumeration

def nativeArithmeticTheory : ArithmeticTheory :=
  UniformCraig.theory ℒₒᵣ nativeArithmeticEnumeration

noncomputable instance : nativeSetTheory.Δ₁ := UniformCraig.theory_delta _ _
noncomputable instance : nativeArithmeticTheory.Δ₁ := UniformCraig.theory_delta _ _

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem nativeSetEnumeration_eval (sentence : V) :
    nativeSetEnumeration.val.Evalb ![sentence] ↔ NativeDerivable (chiS 0 sentence) := by
  have derives : ∀ f : V, nativeDerivableDef.val.Eval ![f] Empty.elim ↔ NativeDerivable f :=
    nativeDerivable_eval
  simp [nativeSetEnumeration, Disj.chiS_defined.iff, derives]

attribute [local irreducible] nativeSetEnumeration

theorem nativeArithmeticEnumeration_eval (sentence : V) :
    nativeArithmeticEnumeration.val.Evalb ![sentence] ↔
      NativeDerivable (chiS 0 (kax omegaReader sentence)) := by
  have setEnum : ∀ f : V, nativeSetEnumeration.val.Eval ![f] Empty.elim ↔
      NativeDerivable (chiS 0 f) := nativeSetEnumeration_eval
  simp [nativeArithmeticEnumeration, omegaReaderCode_defines.iff, setEnum]

theorem from_native_axiom {p : V} (shape : IsFormula ℒₛₑₜ p)
    (closed : shift ℒₛₑₜ p = p) (proof : NativeDerivable (chiS 0 p)) :
    ∃ stamp, (p ^⋏ qqVerums stamp) ∈ nativeSetTheory.Δ₁Class (V := V) :=
  UniformCraig.padded_axiom ℒₛₑₜ shape closed ((nativeSetEnumeration_eval p).mpr proof)

private theorem chiS_and {offset p q : V} (hp : IsUFormula ℒₛₑₜ p) (hq : IsUFormula ℒₛₑₜ q) :
    chiS offset (p ^⋏ q) = cand (chiS offset p) (chiS offset q) := by
  simp [chiS, tr_and hp hq, posPair]

private theorem chiS_verum (offset : V) : chiS offset (^⊤ : V) = cneg 1 := by
  simp [chiS, tr_verum, posPair]

private theorem native_conjunction {p q : V} (hp : NativeDerivable p) (hq : NativeDerivable q) :
    NativeDerivable (cand p q) :=
  (Logic.Ctx.andIntro (S := NativeDerivable.hilbert) (Γ := []) (.thm hp) (.thm hq)).empty

private theorem native_verums (n : V) : NativeDerivable (chiS 0 (qqVerums n)) := by
  have top : NativeDerivable (cneg (1 : V)) := (NativeDerivable.hilbert : Logic V).identity 1
  induction n using ISigma1.sigma1_succ_induction
  · have proof := nativeDerivable_defined (V := V) |>.to_definable
    definability
  · rw [qqVerums_zero, chiS_verum]
    exact top
  · rename_i n ih
    rw [qqVerums_succ, chiS_and (by simp) (IsSemiformula.qqVerums (n := 0) n).isUFormula, chiS_verum]
    exact native_conjunction top ih

theorem native_set_axiom_translates {p : V} (axiomMember : p ∈ nativeSetTheory.Δ₁Class (V := V))
    (offset : V) : NativeDerivable (chiS offset p) := by
  obtain ⟨body, _, stamp, _, rfl, bodyWf, _, paddingClosed, enumerated⟩ :=
    (UniformCraig.mem_iff ℒₛₑₜ nativeSetEnumeration p).mp axiomMember
  have wf := (IsSemiformula.qqVerums (n := (0 : V)) stamp).isUFormula (L := ℒₛₑₜ)
  rw [chiS_closed (by simp [bodyWf.isUFormula, wf]) paddingClosed offset, chiS_and bodyWf.isUFormula wf]
  exact native_conjunction ((nativeSetEnumeration_eval body).mp
    ((UniformCraig.witness_spec nativeSetEnumeration body).mpr ⟨stamp, enumerated⟩)) (native_verums stamp)

theorem native_set_refutation_translates [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (refutation : Bootstrapping.Provable nativeSetTheory (^⊥ : V)) : NativeDerivable (1 : V) := by
  apply (nativeDerivable_eval _).mp
  exact refutation_tr (nativeLogic (V := V)) nativeSetTheory
    (fun p present offset => (nativeDerivable_eval _).mpr (native_set_axiom_translates present offset))
    refutation

set_option maxHeartbeats 1200000 in
theorem nativeSet_theorem_compiles [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] {σ : SetTheorySentence} (proof : nativeSetTheory ⊢ σ) :
    NativeDerivable (chiS 0 (⌜σ⌝ : V)) := by
  let L : IntLogic V := nativeLogic
  have derives : Bootstrapping.Provable nativeSetTheory (⌜σ⌝ : V) :=
    internalize_provability proof
  obtain ⟨d, witness⟩ := derives
  have result := derivation_tr L nativeSetTheory
    (fun p present offset => (nativeDerivable_eval _).mpr (native_set_axiom_translates present offset))
    (d+d) witness.2 d (by simp) le_rfl le_rfl
  rw [witness.1] at result
  have onlyMember : L.T.Prov (I0451.Logic.Tait.imp (seqC ({(⌜σ⌝ : V)} : V) d) (chiS 0 (⌜σ⌝ : V))) := by
    apply seqC_elim L
    intro p has
    have same : p = (⌜σ⌝ : V) := by simpa using has
    subst p
    have closed : shift ℒₛₑₜ (⌜σ⌝ : V) = ⌜σ⌝ := by
      rw [Sentence.quote_def, ← Semiformula.quote_shift]
      simp
    rw [chiS_closed (Sentence.quote_isUFormula σ) closed d]
    exact L.T.toLogic.identity _
  exact (nativeDerivable_eval _).mp (L.T.mp result onlyMember)

theorem nativeSet_theorem_of_compiled {σ : SetTheorySentence} (proof : NativeDerivable (chiS 0 (⌜σ⌝ : Nat))) :
    nativeSetTheory ⊢ σ := by
  have closed : shift ℒₛₑₜ (⌜σ⌝ : Nat) = ⌜σ⌝ := by
    rw [Sentence.quote_def, ← Semiformula.quote_shift]
    simp
  obtain ⟨stamp, stamped⟩ := from_native_axiom (Sentence.quote_isSemiformula₀ σ) closed proof
  have mem : σ.padding stamp ∈ nativeSetTheory := by
    have admitted := (UniformCraig.mem_iff ℒₛₑₜ nativeSetEnumeration _).mp stamped
    change UniformCraig.Axiom ℒₛₑₜ nativeSetEnumeration (⌜σ.padding stamp⌝ : Nat)
    rw [Bootstrapping.Sentence.quote_padding]
    simpa only [natCast_nat] using admitted
  exact FFL.Entailment.K_left (FFL.Entailment.by_axm mem)

theorem nativeArithmetic_theorem_of_compiled {σ : ArithmeticSentence}
    (proof : NativeDerivable (chiS 0 (⌜readArithmetic σ⌝ : Nat))) :
    nativeArithmeticTheory ⊢ σ := by
  rw [quote_readArithmetic] at proof
  have closed : shift ℒₒᵣ (⌜σ⌝ : Nat) = ⌜σ⌝ := by
    rw [Sentence.quote_def, ← Semiformula.quote_shift]
    simp
  obtain ⟨stamp, stamped⟩ := UniformCraig.padded_axiom ℒₒᵣ
    (Sentence.quote_isSemiformula₀ σ) closed ((nativeArithmeticEnumeration_eval _).mpr proof)
  have mem : σ.padding stamp ∈ nativeArithmeticTheory := by
    have admitted := (UniformCraig.mem_iff ℒₒᵣ nativeArithmeticEnumeration _).mp stamped
    change UniformCraig.Axiom ℒₒᵣ nativeArithmeticEnumeration (⌜σ.padding stamp⌝ : Nat)
    rw [Bootstrapping.Sentence.quote_padding]
    simpa only [natCast_nat] using admitted
  exact FFL.Entailment.K_left (FFL.Entailment.by_axm mem)

end I0451.Omega
