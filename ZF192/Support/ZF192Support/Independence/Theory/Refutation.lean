module
public import ZF192Support.Independence.Theory.Definitions
public import ZF192Support.Calculus.Internal.Derivation
public import ZF192Support.Independence.Arithmetization.Closing
@[expose] public section
/-! # The internal premise

In a model `V` of PA, the axioms of `U ι` have C-proofs: a padded axiom `θ ⋏ ⊤ⁿ` comes with
a trace of `chiS 0 θ`, and `⊤ⁿ` and conjunction are handled by the kernel; the marker axiom
is a standard sentence, so its C-proof in `ℕ` lifts to `V`. -/
namespace ZF192Support.Halting
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ZFR.ArithmeticRepresentation ZF192Support.Internal.Arith
open ZF192Support.Internal (cneg cand)
open ZF192Support.Internal.Tait (chiS)
open ZF192Support.CKernel.Generic ZF192Support.CKernel.Generic.Logic

section
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

lemma chiS_and {m p q : V} (hp : IsUFormula ℒₛₑₜ p) (hq : IsUFormula ℒₛₑₜ q) :
    chiS m (p ^⋏ q) = cand (chiS m p) (chiS m q) := by
  simp [chiS, ZF192Support.Internal.Tait.tr_and hp hq, ZF192Support.Internal.Tait.posPair]

lemma chiS_verum (m : V) : chiS m (^⊤ : V) = cneg 1 := by
  simp [chiS, ZF192Support.Internal.Tait.tr_verum, ZF192Support.Internal.Tait.posPair]

/-- The kernel read through `D`. -/
noncomputable abbrev KL : ZF192Support.Internal.Tait.IntLogic V := (provRules (M := V)).intLogic

lemma D_iff_S (x : V) : D.val.Evalb ![x] ↔ (KL (V := V)).S.Prov x :=
  ((KL (V := V)).prov_iff x).symm

lemma D_cand {a b : V} (ha : D.val.Evalb ![a]) (hb : D.val.Evalb ![b]) :
    D.val.Evalb ![cand a b] := by
  rw [D_iff_S] at ha hb ⊢
  have := (Ctx.andIntro (S := (KL (V := V)).S.toLogic) (Γ := []) (.thm ha) (.thm hb)).empty
  simpa using this

lemma D_top : D.val.Evalb ![(cneg 1 : V)] := by
  rw [D_iff_S]
  simpa [cneg] using (KL (V := V)).S.toLogic.identity 1

lemma D_verums : ∀ n : V, D.val.Evalb ![chiS 0 (qqVerums n)] := by
  have h : ∀ n : V, (KL (V := V)).Pr (chiS 0 (qqVerums n)) := by
    intro n
    induction n using ISigma1.sigma1_succ_induction
    · definability
    · show (KL (V := V)).Pr (chiS 0 (qqVerums 0))
      rw [qqVerums_zero, chiS_verum]; exact D_top
    · rename_i n ih
      rw [qqVerums_succ, chiS_and (by simp) (IsSemiformula.qqVerums (n := 0) n).isUFormula,
        chiS_verum]
      exact D_cand D_top ih
  exact h

/-- Padded C-theorems have C-proofs at every offset. -/
lemma D_craig {p : V} (hp : CraigR ℒₛₑₜ idFn p) (m : V) : D.val.Evalb ![chiS m p] := by
  obtain ⟨s, -, n, -, rfl, hs, -, hsh, ht, hm⟩ := hp
  have hsu : IsUFormula ℒₛₑₜ s := hs.isUFormula
  have hvu : IsUFormula ℒₛₑₜ (qqVerums n : V) := (IsSemiformula.qqVerums (n := 0) n).isUFormula
  rw [ZF192Support.Internal.Tait.chiS_closed (by simp [hsu, hvu]) hsh m, chiS_and hsu hvu]
  exact D_cand ((D_iff _).mpr ⟨n, ht, hm⟩) (D_verums n)

/-- A standard C-theorem is a `D`-theorem of `V`. -/
lemma D_of_nat {x : ℕ} (h : CProv x) : D.val.Evalb ![(x : V)] :=
  ZF192Support.Internal.prov_of_nat x h

variable (ι : Interp)

lemma markAt_bvar : markAt ι (^#0 : V) = ⌜ι.mark⌝ := by
  have h1 : IsSemiformula ℒₛₑₜ 1 (tq ι.mark : V) := by simpa using tq_semiformula (V := V) ι.mark
  have hw : IsSemitermVec ℒₛₑₜ 1 1 (^#0 ∷ (0 : V)) := by
    rw [show (1 : V) = 0 + 1 by simp]; simp
  have e : subst ℒₛₑₜ (^#0 ∷ (0 : V)) (tq ι.mark : V) = (tq ι.mark : V) :=
    subst_eq_self h1 hw (fun i hi => by
      rcases (lt_one_iff_eq_zero.mp hi) with rfl; simp)
  unfold markAt
  rw [e]; exact tq_eq _

end

section
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

lemma insert_formulaSet {p s : V} (hp : IsFormula ℒₛₑₜ p) (hs : IsFormulaSet ℒₛₑₜ s) :
    IsFormulaSet ℒₛₑₜ (insert p s) := by
  intro y hy
  rcases mem_bitInsert_iff.mp hy with rfl | hy
  · exact hp
  · exact hs y hy

variable {U : Theory ℒₛₑₜ} [U.Δ₁]

/-- A padded axiom `θ ⋏ v` gives `θ` in any context. -/
lemma derivable_of_padded {θ v s : V} (hθ : IsFormula ℒₛₑₜ θ) (hv : IsFormula ℒₛₑₜ v)
    (hs : IsFormulaSet ℒₛₑₜ s) (hax : θ ^⋏ v ∈ U.Δ₁Class) : Derivable U (insert θ s) := by
  have hθs := insert_formulaSet hθ hs
  have hand : IsFormula ℒₛₑₜ (θ ^⋏ v) := by simp [hθ, hv]
  have d₁ : Derivable U (insert (θ ^⋏ v) (insert θ s)) :=
    Derivable.by_axm (insert_formulaSet hand hθs) _ (by simp) hax
  have hnθ : IsFormula ℒₛₑₜ (neg ℒₛₑₜ θ) := IsSemiformula.neg_iff.mpr hθ
  have hnv : IsFormula ℒₛₑₜ (neg ℒₛₑₜ v) := IsSemiformula.neg_iff.mpr hv
  have hneg : neg ℒₛₑₜ (θ ^⋏ v) = neg ℒₛₑₜ θ ^⋎ neg ℒₛₑₜ v := by
    simp [hθ.isUFormula, hv.isUFormula]
  have d₂ : Derivable U (insert (neg ℒₛₑₜ (θ ^⋏ v)) (insert θ s)) := by
    rw [hneg]
    have hS : IsFormulaSet ℒₛₑₜ (insert (neg ℒₛₑₜ θ ^⋎ neg ℒₛₑₜ v) (insert θ s)) :=
      insert_formulaSet (by simp [hnθ, hnv]) hθs
    refine Derivable.or_m (p := neg ℒₛₑₜ θ) (q := neg ℒₛₑₜ v) (by simp) ?_
    exact Derivable.em (insert_formulaSet hnθ (insert_formulaSet hnv hS)) θ (by simp) (by simp)
  exact Derivable.cut (θ ^⋏ v) d₁ d₂

instance : 𝚺ᴬ₁-Predicate (fun x : V => Derivable U x) := Derivable.definable

/-- `⊤ⁿ` is derivable in any context. -/
lemma derivable_verums {s : V} (hs : IsFormulaSet ℒₛₑₜ s) :
    ∀ n : V, Derivable U (insert (qqVerums n) s) := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · definability
  · simpa using Derivable.verum (T := U) (insert_formulaSet (by simp) hs) (by simp)
  · rename_i n ih
    rw [qqVerums_succ]
    have hv : IsFormula ℒₛₑₜ (qqVerums n : V) := IsSemiformula.qqVerums n
    have hS := insert_formulaSet (show IsFormula ℒₛₑₜ (^⊤ ^⋏ qqVerums n : V) by simp) hs
    refine Derivable.and_m (p := ^⊤) (q := qqVerums n) (by simp) ?_ ?_
    · exact Derivable.verum (insert_formulaSet (by simp) hS) (by simp)
    · refine Derivable.wk (insert_formulaSet hv hS) ?_ ih
      intro y hy
      rcases mem_bitInsert_iff.mp hy with rfl | hy
      · simp
      · simp [hy]

lemma shift_verums : ∀ n : V, shift ℒₛₑₜ (qqVerums n) = qqVerums n := by
  intro n
  induction n using ISigma1.sigma1_succ_induction
  · definability
  · simp
  · rename_i n ih
    rw [qqVerums_succ, shift_and (by simp) (IsSemiformula.qqVerums (n := 0) n).isUFormula,
      shift_verum, ih]

variable (ι : Interp)

lemma kax_shift {σ : V} (hσ : IsFormula ℒₒᵣ σ) (hsh : shift ℒₒᵣ σ = σ) :
    shift ℒₛₑₜ (kax ι σ) = kax ι σ := by
  have hm1 : IsSemiformula ℒₛₑₜ 1 (markAt ι (^#0 : V)) := markAt_semiformula ι (by simp)
  have hj1 := jhat_semiformula ι hσ
  have hσ1 : IsSemiformula ℒₒᵣ 1 σ := ⟨hσ.isUFormula, le_trans hσ.bv_le (by simp)⟩
  have ej : shift ℒₛₑₜ (jhat ι σ) = jhat ι σ := by
    have := J_shift ι 1 σ hσ1 (^#0) (by simp)
    simpa [jhat, hsh] using this.symm
  have em : shift ℒₛₑₜ (markAt ι (^#0 : V)) = markAt ι (^#0 : V) := by
    rw [shift_markAt ι (show IsSemiterm ℒₛₑₜ 1 (^#0 : V) by simp)]; simp
  simp [kax, imp, hm1.isUFormula, hj1.isUFormula, shift_neg hm1, em, ej]

/-- `U` derives the translations of `T`'s axioms from the marker. -/
theorem axStep : AxStep ι (theoryT ι) theoryU V := by
  intro p hp ε he
  obtain ⟨s, -, n, -, rfl, hs, hssh, -, ht, hm⟩ := (mem_craig_iff ℒₒᵣ (kaxFn ι) p).mp hp
  have hK : IsFormula ℒₛₑₜ (kax ι s) := kax_formula ι hs
  have hv : IsFormula ℒₛₑₜ (qqVerums n : V) := IsSemiformula.qqVerums n
  have hKsh : shift ℒₛₑₜ (kax ι s) = kax ι s := kax_shift ι hs hssh
  have hq : kax ι s ^⋏ qqVerums n ∈ theoryU.Δ₁Class (V := V) := by
    refine (mem_craig_iff ℒₛₑₜ idFn _).mpr ⟨kax ι s, (lt_K!_left _ _).le, n,
      le_trans (le_qqVerums n) (lt_K!_right _ _).le, rfl, hK, hKsh, ?_, ht, hm⟩
    simp [hK.isUFormula, hv.isUFormula, hKsh, shift_verums]
  have hM : IsFormula ℒₛₑₜ (markAt ι ε) := markAt_semiformula ι he
  have hJ : IsFormula ℒₛₑₜ (J ι ε 0 s) := J_semiformula ι 0 s hs ε he
  have hS : IsFormulaSet ℒₛₑₜ (insert (neg ℒₛₑₜ (markAt ι ε)) (insert (J ι ε 0 s) (0 : V))) :=
    pair_formulaSet (IsSemiformula.neg_iff.mpr hM) hJ
  have hJs := derivable_of_kax' ι hs he (derivable_of_padded hK hv hS hq)
  have eJ : J ι ε 0 (s ^⋏ qqVerums n) = J ι ε 0 s ^⋏ qqVerums n := by
    rw [J_and hs.isUFormula (IsSemiformula.qqVerums (n := 0) n).isUFormula, J_verums]
  rw [eJ]
  have hJv : IsFormula ℒₛₑₜ (J ι ε 0 s ^⋏ qqVerums n) := by simp [hJ, hv]
  have hT : IsFormulaSet ℒₛₑₜ (insert (neg ℒₛₑₜ (markAt ι ε))
      (insert (J ι ε 0 s ^⋏ qqVerums n) (0 : V))) :=
    pair_formulaSet (IsSemiformula.neg_iff.mpr hM) hJv
  refine Derivable.and_m (p := J ι ε 0 s) (q := qqVerums n) (by simp) ?_ (derivable_verums hT n)
  refine Derivable.wk (insert_formulaSet hJ hT) ?_ hJs
  intro y hy
  rcases mem_bitInsert_iff.mp hy with rfl | hy
  · simp
  · rcases mem_bitInsert_iff.mp hy with rfl | hy
    · simp
    · simp at hy

/-- With the axiom `∃e Mark e` derivable, `¬Mark &x` refutes `U`. -/
theorem refute_of_mark' {x : V} (hex : Derivable U (insert (^∃ (markAt ι (^#0 : V))) (0 : V)))
    (h : Derivable U (insert (neg ℒₛₑₜ (markAt ι (^&x))) (0 : V))) :
    Bootstrapping.Provable U (^⊥ : V) := by
  have h₀ := mark_descend ι x h
  have hm1 : IsSemiformula ℒₛₑₜ 1 (markAt ι (^#0 : V)) := markAt_semiformula ι (by simp)
  have hall : Derivable U (insert (^∀ (neg ℒₛₑₜ (markAt ι (^#0 : V)))) (0 : V)) :=
    Derivable.all (IsSemiformula.neg_iff.mpr hm1) (by simpa [markAt_free, setShift_zero] using h₀)
  have h₂ : Derivable U (0 : V) :=
    Derivable.cut (^∀ (neg ℒₛₑₜ (markAt ι (^#0 : V)))) (by simpa using hall)
      (by simpa [hm1.isUFormula] using hex)
  refine (internal_provable_iff_internal_derivable).mpr
    (Derivable.wk (singleton_formulaSet (by simp)) (fun y hy => by simp at hy) h₂)

end

end ZF192Support.Halting
