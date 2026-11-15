module
public import Halting.Premise
@[expose] public section
/-! # `U`-theorems are exactly the sentences whose translations C proves

* `cprov_of_U`: `U ⊢ θ` gives a C-proof of `chiS 0 ⌜θ⌝` in `ℕ` (stage 2 at `V = ℕ`; `U`'s
  axioms have C-proofs by `D_craig`).
* `U_of_cprov`: a C-proof of `chiS 0 ⌜θ⌝` puts `θ ⋏ ⊤ⁿ` into `U` (Craig padding).
* `T_of_cprov`: a C-proof of `chiS 0 (kax ι ⌜σ⌝)` puts `σ ⋏ ⊤ⁿ` into `T ι`. -/
namespace ZF209.Halting
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ZFR.ArithmeticRepresentation ZF209.Internal.Arith
open ZF209.Internal.Tait (chiS)

lemma shift_quote_sentence {L : Language} [L.Encodable] [L.LORDefinable] {V : Type}
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (σ : Sentence L) : shift L (⌜σ⌝ : V) = ⌜σ⌝ := by
  rw [Sentence.quote_def, ← Semiformula.quote_shift]; simp

/-- The padding `⊤ⁿ` as an external sentence. -/
def verumsS {L : Language} : ℕ → Sentence L
  | 0 => ⊤
  | n + 1 => ⊤ ⋏ verumsS n

lemma quote_verumsS {L : Language} [L.Encodable] [L.LORDefinable] {V : Type}
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : ∀ n : ℕ, (⌜(verumsS n : Sentence L)⌝ : V) = qqVerums (n : V)
  | 0 => by
    show (⌜(⊤ : Sentence L)⌝ : V) = qqVerums ((0 : ℕ) : V)
    rw [Sentence.quote_verum]; simp
  | n + 1 => by
    show (⌜(⊤ ⋏ verumsS n : Sentence L)⌝ : V) = qqVerums ((n + 1 : ℕ) : V)
    rw [Sentence.quote_and, Sentence.quote_verum, quote_verumsS n]; simp

lemma verumsS_provable {L : Language} {T : Theory L} : ∀ n, T ⊢ (verumsS n : Sentence L)
  | 0 => by simp [verumsS]
  | n + 1 => by simpa [verumsS] using Entailment.K_intro (by simp) (verumsS_provable n)

section
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

lemma craigR_pad {L : Language} [L.Encodable] [L.LORDefinable] {G : CodeFn} {s n : V}
    (hs : IsFormula L s) (hsh : shift L s = s) (hp : shift L (s ^⋏ qqVerums n) = s ^⋏ qqVerums n)
    (ht : modelTrace cRule n) (hm : modelMember (chiS 0 (G.f V s)) n) :
    CraigR L G (s ^⋏ qqVerums n) :=
  ⟨s, (lt_K!_left _ _).le, n, le_trans (le_qqVerums n) (lt_K!_right _ _).le, rfl, hs, hsh, hp, ht, hm⟩

/-- An internal `U`-proof of a sentence gives a C-proof of its translation. -/
lemma D_of_provable {θ : Sentence ℒₛₑₜ} (h : Bootstrapping.Provable theoryU (⌜θ⌝ : V)) :
    D.val.Evalb ![chiS 0 (⌜θ⌝ : V)] := by
  let L := (provRules (M := V)).intLogic
  have hU : ∀ p ∈ theoryU.Δ₁Class (V := V), ∀ m, L.T.Prov (chiS m p) := fun p hp m =>
    (L.pr_iff _).mp (D_craig ((mem_craig_iff ℒₛₑₜ idFn p).mp hp) m)
  obtain ⟨d, hd⟩ := internal_provable_iff_internal_derivable.mp h
  have hs := ZF209.Internal.Tait.derivation_tr L theoryU hU (d + d) hd.2 d (by simp) le_rfl le_rfl
  rw [hd.1] at hs
  have hθ : IsUFormula ℒₛₑₜ (⌜θ⌝ : V) := (Sentence.quote_isSemiformula₀ θ).isUFormula
  have e : L.Pr (ZF209.Internal.imp (ZF209.Internal.Tait.seqC ({(⌜θ⌝ : V)} : V) d) (chiS d ⌜θ⌝)) :=
    ZF209.Internal.Tait.seqC_elim L fun r hr => by
      have : r = ⌜θ⌝ := by simpa using hr
      subst this
      exact (L.pr_iff _).mpr (by simpa using L.S.toLogic.identity (chiS d (⌜θ⌝ : V)))
  have hd' : L.Pr (chiS d (⌜θ⌝ : V)) :=
    (L.pr_iff _).mpr (L.T.mp ((L.pr_iff _).mp (by simpa using hs)) ((L.pr_iff _).mp e))
  rw [ZF209.Internal.Tait.chiS_closed hθ (shift_quote_sentence θ) d] at hd'
  exact hd'

end

/-- `U ⊢ θ` gives a C-proof of `chiS 0 ⌜θ⌝`. -/
theorem cprov_of_U {θ : Sentence ℒₛₑₜ} (h : theoryU ⊢ θ) : CProv (chiS 0 (⌜θ⌝ : ℕ)) :=
  D_of_provable (tprovable_iff_provable.mp (internal_provable_of_outer_provable (V := ℕ) h))

/-- A C-proof of `chiS 0 ⌜θ⌝` makes `θ` a `U`-theorem. -/
theorem U_of_cprov {θ : Sentence ℒₛₑₜ} (h : CProv (chiS 0 (⌜θ⌝ : ℕ))) : theoryU ⊢ θ := by
  obtain ⟨n, hn, hm⟩ := (D_iff' _).mp h
  have hmem : θ ⋏ verumsS n ∈ theoryU := by
    show CraigR ℒₛₑₜ idFn (⌜θ ⋏ verumsS n⌝ : ℕ)
    have e : (⌜θ ⋏ verumsS n⌝ : ℕ) = ⌜θ⌝ ^⋏ qqVerums n := by simp [quote_verumsS]
    rw [e]
    refine craigR_pad (by simp) (shift_quote_sentence θ) ?_ hn hm
    rw [← e]; exact shift_quote_sentence _
  exact Entailment.K_left (Entailment.by_axm hmem)

/-- A C-proof of `chiS 0 (kax ι ⌜σ⌝)` makes `σ` a `T ι`-theorem. -/
theorem T_of_cprov (ι : Interp) {σ : ArithmeticSentence}
    (h : CProv (chiS 0 (kax ι (⌜σ⌝ : ℕ)))) : theoryT ι ⊢ σ := by
  obtain ⟨n, hn, hm⟩ := (D_iff' _).mp h
  have hmem : σ ⋏ verumsS n ∈ theoryT ι := by
    show CraigR ℒₒᵣ (kaxFn ι) (⌜σ ⋏ verumsS n⌝ : ℕ)
    have e : (⌜σ ⋏ verumsS n⌝ : ℕ) = ⌜σ⌝ ^⋏ qqVerums n := by simp [quote_verumsS]
    rw [e]
    refine craigR_pad (by simp) (shift_quote_sentence σ) ?_ hn hm
    rw [← e]; exact shift_quote_sentence _
  exact Entailment.K_left (Entailment.by_axm hmem)

end ZF209.Halting
