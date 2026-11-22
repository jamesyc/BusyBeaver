module
public import ZF192Support.SetTheory.GateModel.QModel
@[expose] public section
/-! # A model of ZF inside any structure satisfying the gate -/
namespace ZF192Support.GateModel
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

section
variable {M : Type*} [SetStructure M] [ZFMinus M]

lemma vec_one {N : Type*} (v : Fin 1 → N) : ![v 0] = v := by
  funext i; rw [Subsingleton.elim i 0]; rfl

lemma vec_two {N : Type*} (v : Fin 2 → N) : ![v 0, v 1] = v := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ j => rw [Subsingleton.elim j 0]; rfl

instance WFPart.models_BST : (WFPart M)↓[ℒₛₑₜ] ⊧* 𝗕𝗦𝗧 := ⟨fun φ hφ => by
  cases hφ with
  | equality φ h =>
    exact (inferInstance : (WFPart M)↓[ℒₛₑₜ] ⊧* 𝗘𝗤 ℒₛₑₜ).models_set h
  | empty_set =>
    have : ∃ E : WFPart M, SetTheory.IsEmpty E := WFPart.exists_empty
    simpa [models_iff] using this
  | extensionality =>
    have : ∀ x y : WFPart M, x = y ↔ ∀ z, z ∈ x ↔ z ∈ y :=
      fun x y => ⟨fun h z => h ▸ Iff.rfl, WFPart.ext⟩
    simpa [models_iff] using this
  | pairing =>
    have : ∀ x y : WFPart M, ∃ z, ∀ w, w ∈ z ↔ w = x ∨ w = y := WFPart.exists_pair
    simpa [models_iff] using this
  | union =>
    have : ∀ x : WFPart M, ∃ y, ∀ z, z ∈ y ↔ ∃ w ∈ x, z ∈ w := WFPart.exists_union
    simpa [models_iff] using this
  | power_set =>
    have : ∀ x : WFPart M, ∃ y, ∀ z, z ∈ y ↔ z ⊆ x := WFPart.exists_power
    simpa [models_iff] using this
  | infinity =>
    have : ∃ I : WFPart M, (∀ E : WFPart M, (∀ Z, Z ∉ E) → E ∈ I) ∧
        ∀ X ∈ I, ∀ X' : WFPart M, (∀ Z, Z ∈ X' ↔ Z = X ∨ Z ∈ X) → X' ∈ I :=
      WFPart.exists_inductive
    have hs : ∀ a b : WFPart M, (Semiformula.Eval ![a, b] Empty.elim) isSucc ↔
        ∀ z, z ∈ a ↔ z = b ∨ z ∈ b := fun a b => by simp [isSucc]
    simpa [models_iff, SetTheory.IsEmpty, hs] using this
  | foundation =>
    have : ∀ x : WFPart M, IsNonempty x → ∃ y ∈ x, ∀ z ∈ x, z ∉ y :=
      fun x hx => WFPart.foundation x hx.nonempty
    simpa [models_iff] using this⟩

instance WFPart.models_SEP : (WFPart M)↓[ℒₛₑₜ] ⊧* 𝗦𝗘𝗣 := ⟨fun φ hφ => by
  cases hφ with
  | separation φ =>
    have : ∀ (f : ℕ → WFPart M) (x : WFPart M), ∃ y, ∀ z, z ∈ y ↔ z ∈ x ∧ φ.Eval ![z] f :=
      fun f x => WFPart.exists_sep x _
        (Language.Definable.of_iff (definable_eval φ f) fun v => by
          show φ.Eval ![v 0] f ↔ φ.Eval v f; rw [vec_one])
    simpa [models_iff, Semiformula.eval_univCl, Axiom.separationSchema] using this⟩

instance WFPart.models_REPL : (WFPart M)↓[ℒₛₑₜ] ⊧* 𝗥𝗘𝗣𝗟 := ⟨fun φ hφ => by
  cases hφ with
  | replacement φ =>
    have : ∀ f : ℕ → WFPart M, (∀ x, ∃! y, φ.Eval ![x, y] f) →
        ∀ X : WFPart M, ∃ Y, ∀ y, y ∈ Y ↔ ∃ x ∈ X, φ.Eval ![x, y] f :=
      fun f hf X => WFPart.exists_repl X _
        (Language.Definable.of_iff (definable_eval φ f) fun v => by
          show φ.Eval ![v 0, v 1] f ↔ φ.Eval v f; rw [vec_two])
        (fun A B C hB hC => (hf A).unique hB hC)
    simpa [models_iff, Semiformula.eval_univCl, Axiom.replacementSchema] using this⟩

instance WFPart.models_ZF : (WFPart M)↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := ⟨fun φ hφ => by
  rcases hφ with (h | h) | h
  · exact WFPart.models_BST.models_set h
  · exact WFPart.models_SEP.models_set h
  · exact WFPart.models_REPL.models_set h⟩

end

/-- Every nonempty structure satisfying the gate contains, by a definable
interpretation, a model of ZF. -/
theorem gate_interprets_zf {V : Type*} [SetStructure V] [Nonempty V] [GateHull V]
    {e : V} (he : SetTheory.IsEmpty e) :
    (WFPart (Q he))↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := inferInstance

end ZF192Support.GateModel
