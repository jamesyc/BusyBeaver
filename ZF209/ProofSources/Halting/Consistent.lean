module
public import Halting.Sound
@[expose] public section
/-! # `T` is consistent if ZF is

A sentence whose translation C proves holds in every model of ZF (`true_of_cprov`). A model of ZF
satisfies the gate theory, so at its empty set the templates read the natural numbers of the gate
model; every axiom `σ ⋏ ⊤ⁿ` of `T` comes with a C-proof of `kaxS σ`, hence `σ` holds there. -/
namespace ZF209.Halting
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.SetTheory FFL.Entailment
open ZF209.Independence ZF209.GateModel ZF209.OmegaInterpretation ZF209.Internal.Arith
open ZF209.Internal.Tait (chiS)

lemma eval_verumsS {L : Language} {M : Type*} [Tarski.Structure L M] (b : Fin 0 → M) (f : Empty → M) :
    ∀ n, (verumsS n : Sentence L).Eval b f
  | 0 => by simp [verumsS]
  | n + 1 => by simpa [verumsS] using eval_verumsS b f n

theorem true_of_cprov {θ : Sentence ℒₛₑₜ} (h : CProv (chiS 0 (⌜θ⌝ : ℕ))) {V : Type}
    [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V↓[ℒₛₑₜ] ⊧ θ := by
  have hx := exact_true (exactProvable_of_cprov h) (V := V) (fun _ => ∅)
  rw [chiS_quote] at hx
  have := (ev_trX (V := V) (Rewriting.emb θ : Semiproposition ℒₛₑₜ 0) 0 0 (fun _ => ∅) rfl
    (fun i => i.elim0)).1.mp hx
  simpa [models_iff, Semiformula.eval_emb, Matrix.empty_eq] using this

/-- `T ι` is consistent if ZF is. -/
theorem consistent [Consistent (𝗭𝗙 : SetTheory)] : Consistent (theoryT tmpl) := by
  obtain ⟨V, _, _, _⟩ := exists_zf_model
  obtain ⟨e, he⟩ := empty_of_models (W := V)
  haveI : GateHull (NQ (fun x y : V => x ∈ y)) := gateHull_of_codeGate he (codeGate_of_models (W := V))
  have hA : (arithmeticTranslation.Model (WFPart (Q (nq_isEmpty
      (mem := fun x y : V => x ∈ y) he))))↓[ℒₒᵣ] ⊧* theoryT tmpl := ⟨fun σ₀ hσ₀ => by
    obtain ⟨s, -, n, -, hp, hs, hssh, -, ht, hm⟩ := hσ₀
    obtain ⟨φ, hφ⟩ := Bootstrapping.IsSemiformula.sound hs
    obtain ⟨σ, rfl⟩ := exists_sentence_of_shift ℒₒᵣ (φ := φ) (by rw [hφ]; exact hssh)
    have hsq : s = ⌜σ⌝ := by rw [← hφ, Sentence.quote_def]
    subst hsq
    have hq : σ₀ = σ ⋏ verumsS n := (Sentence.quote_inj_iff (V := ℕ)).mp (by
      rw [hp]; simp [quote_verumsS])
    subst hq
    have hk : V↓[ℒₛₑₜ] ⊧ kaxS σ := true_of_cprov (by
      rw [quote_kaxS]; exact (D_iff' _).mpr ⟨n, ht, hm⟩)
    have hσ := (kaxS_iff σ).mp hk e he
    simpa [models_iff, eval_verumsS] using hσ⟩
  exact consistent_of_model (theoryT tmpl) (arithmeticTranslation.Model (WFPart (Q (nq_isEmpty
      (mem := fun x y : V => x ∈ y) he))))

end ZF209.Halting
