module
public import I0451.Logic.RankCollection
public import I0451.CommandOutputs
public import I0451.Commands.ExtraMeaning
public import Foundation.FirstOrder.LK.Completeness.CounterModel

/-! A first-order model-theoretic formulation of the literal search's
nonhalting direction. The compressed axiom is the parsed EXTRA sentence. -/
@[expose] public section
namespace I0451.Logic

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

def compressedSetAxiom : SetTheorySentence :=
  (SetSyntax.translate (fun i => Semiterm.fvar i) SetSentences.berkeleyFormula :
    SetTheorySemiproposition 0).univCl

def compressedTheory : SetTheory := 𝗭𝗙 ∪ {compressedSetAxiom}

variable {V : Type} [SetStructure V] [Nonempty V]

theorem compressed_models_iff (irrefl : ∀ x : V, x ∉ x) :
    V↓[ℒₛₑₜ] ⊧ compressedSetAxiom ↔ SetSentences.BerkeleyFormula (fun x y : V => x ∈ y) := by
  unfold compressedSetAxiom
  simp only [models_iff, Semiformula.eval_univCl]
  have form (s : Nat → V) :
      (SetSyntax.translate (fun i => Semiterm.fvar i) SetSentences.berkeleyFormula :
        SetTheorySemiproposition 0).Eval ![] s ↔
          SetSentences.BerkeleyFormula (fun x y : V => x ∈ y) := by
    rw [SetSyntax.translate_eval]
    simp only [Semiterm.val_fvar]
    have sound := SetSentences.berkeley_formula_eval (E := fun x y : V => x ∈ y) irrefl s
    rw [SetSentences.berkeleyCode, eval_formula] at sound
    exact sound
  simp only [form, forall_const]

omit [Nonempty V] in
theorem literal_nonhalting_of_model (point : V) (bundle : BundleModel (fun x y : V => x ∈ y))
    (foundation : SetSentences.Foundation (fun x y : V => x ∈ y))
    (compressed : SetSentences.BerkeleyFormula (fun x y : V => x ∈ y)) :
    ¬ Halts literal (blank 0) := by
  intro halt
  have contradiction := Runtime.literal_halts_iff_derives.mp halt
  have invalid := contradiction.sound bundle
    (fun s => (Runtime.literal_foundation_eval (E := fun x y : V => x ∈ y) bundle.irrefl s).mpr foundation)
    (fun s => (Runtime.literal_berkeley_eval (E := fun x y : V => x ∈ y) bundle.irrefl s).mpr compressed) (fun _ => point)
  exact eval_false (E := fun x y : V => x ∈ y) _ bundle.irrefl invalid

attribute [local irreducible] compressedSetAxiom

set_option maxHeartbeats 1200000 in
theorem literal_nonhalting_of_compressed_model [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
    (compressed : V↓[ℒₛₑₜ] ⊧ compressedSetAxiom) :
    ¬ Halts literal (blank 0) := by
  have c : ZFModel.BoundedCollection (V := V) := ZFModel.boundedCollection_of_zf
  have bundle : BundleModel (fun x y : V => x ∈ y) := ZFModel.bundleModel c
  have p : SetSentences.BerkeleyFormula (fun x y : V => x ∈ y) :=
    (compressed_models_iff (V := V) (fun x => mem_irrefl x)).mp compressed
  let point : V := ∅
  have foundational := ZFModel.foundation (V := V)
  exact literal_nonhalting_of_model point bundle foundational p

instance : 𝗭𝗙 ⪯ compressedTheory :=
  FFL.Entailment.WeakerThan.ofSubset fun _ h => Or.inl h

instance : 𝗘𝗤 ℒₛₑₜ ⪯ compressedTheory :=
  FFL.Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₛₑₜ ⪯ 𝗭𝗙) inferInstance

set_option maxHeartbeats 1200000 in
theorem literal_nonhalting_of_compressed_consistency
    (consistent : FFL.Entailment.Consistent compressedTheory) :
    ¬ Halts literal (blank 0) := by
  intro halt
  apply FFL.Entailment.consistent_iff_unprovable_bot.mp consistent
  apply SetTheory.complete.{0}
  intro M _ _ _
  let : M↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := models_of_subtheory (U := compressedTheory) inferInstance
  have axiomModel : M↓[ℒₛₑₜ] ⊧ compressedSetAxiom :=
    Theory.models M compressedTheory (Or.inr rfl)
  exact (literal_nonhalting_of_compressed_model axiomModel halt).elim

end I0451.Logic
