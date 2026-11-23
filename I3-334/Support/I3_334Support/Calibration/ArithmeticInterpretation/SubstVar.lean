module
public import I3_334Support.Calibration.ArithmeticInterpretation.Commute
@[expose] public section
/-! # The arithmetic translation commutes with substitution of variables

For a vector `w` of variables (bound or free), `J m (subst w p) = subst w (J n p)`:
the graphs and atoms use only bound variables of their own and the template
codes, so a substitution of variables passes through them. -/
namespace PalomarI3380.Calibration.ArithmeticInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (ι : Interp)

/-- `w` consists of variables. -/
def VarVec (n w : V) : Prop :=
  ∀ i < n, (∃ z < w.[i], w.[i] = ^#z) ∨ (∃ x < w.[i], w.[i] = ^&x)

lemma lt_qqBvar (z : V) : z < ^#z := lt_of_le_of_lt (le_pair_right 0 z) (by simp [qqBvar])
lemma lt_qqFvar (x : V) : x < ^&x := lt_of_le_of_lt (le_pair_right 1 x) (by simp [qqFvar])

lemma VarVec.cases {n w i : V} (h : VarVec n w) (hi : i < n) :
    (∃ z, w.[i] = ^#z) ∨ (∃ x, w.[i] = ^&x) := by
  rcases h i hi with ⟨z, _, hz⟩ | ⟨x, _, hx⟩
  · exact Or.inl ⟨z, hz⟩
  · exact Or.inr ⟨x, hx⟩

lemma VarVec.of_cases {n w : V} (h : ∀ i < n, (∃ z, w.[i] = ^#z) ∨ (∃ x, w.[i] = ^&x)) :
    VarVec n w := by
  intro i hi
  rcases h i hi with ⟨z, hz⟩ | ⟨x, hx⟩
  · exact Or.inl ⟨z, by rw [hz]; exact lt_qqBvar z, hz⟩
  · exact Or.inr ⟨x, by rw [hx]; exact lt_qqFvar x, hx⟩

instance varVec_definable : 𝚫ᴬ₁-Relation (VarVec : V → V → Prop) := by
  unfold VarVec; definability

instance varVec_definable' (Γ m) : Γᴬ_[m + 1]-Relation (VarVec : V → V → Prop) :=
  varVec_definable.of_deltaOne

/-- A variable vector of ℒₒᵣ terms is also a vector of `GraphLanguage` terms. -/
lemma VarVec.set {n m w : V} (hw : IsSemitermVec ℒₒᵣ n m w) (hv : VarVec n w) :
    IsSemitermVec GraphLanguage n m w := by
  refine IsSemitermVec.iff.mpr ⟨hw.lh, fun i hi => ?_⟩
  have := hw.nth hi
  rcases hv.cases hi with ⟨z, hz⟩ | ⟨x, hx⟩
  · rw [hz] at this ⊢; simpa using this
  · rw [hx]; simp

@[simp] lemma nth_qVec_zero {w : V} : (qVec GraphLanguage w).[0] = ^#0 := by simp [qVec]

lemma nth_qVec_succ {k w i : V} (hw : IsUTermVec GraphLanguage k w) (hi : i < k) :
    (qVec GraphLanguage w).[i + 1] = termBShift GraphLanguage w.[i] := by
  simp [qVec, hw.lh.symm, nth_termBShiftVec hw hi]

/-- Substitution into a template instance. -/
lemma subst_eqAt {k m u ε a b : V} (hu : IsSemitermVec GraphLanguage k m u) (he : IsSemiterm GraphLanguage k ε)
    (ha : IsSemiterm GraphLanguage k a) (hb : IsSemiterm GraphLanguage k b) :
    subst GraphLanguage u (eqAt ι ε a b) =
      eqAt ι (termSubst GraphLanguage u ε) (termSubst GraphLanguage u a) (termSubst GraphLanguage u b) := by
  have h3 : IsSemiformula GraphLanguage 3 (tq ι.eq : V) := by simpa using tq_semiformula (V := V) ι.eq
  have hw : IsSemitermVec GraphLanguage 3 k (ε ∷ a ∷ b ∷ (0 : V)) := by
    rw [show (3 : V) = 0 + 1 + 1 + 1 by norm_num]; simp [he, ha, hb]
  have hw2 : IsUTermVec GraphLanguage 2 (a ∷ b ∷ (0 : V)) := by simp [ha.isUTerm, hb.isUTerm]
  unfold eqAt
  rw [substs_substs h3 hu hw, show (3 : V) = 2 + 1 by norm_num,
    termSubstVec_cons he.isUTerm hw2, termSubstVec_cons₂ ha.isUTerm hb.isUTerm]

lemma subst_un (φ : Semisentence GraphLanguage 2) {k m u ε a : V} (hu : IsSemitermVec GraphLanguage k m u)
    (he : IsSemiterm GraphLanguage k ε) (ha : IsSemiterm GraphLanguage k a) :
    subst GraphLanguage u (un (tq φ) ε a) = un (tq φ) (termSubst GraphLanguage u ε) (termSubst GraphLanguage u a) := by
  have h2 : IsSemiformula GraphLanguage 2 (tq φ : V) := by simpa using tq_semiformula (V := V) φ
  have hw : IsSemitermVec GraphLanguage 2 k (ε ∷ a ∷ (0 : V)) := by
    rw [show (2 : V) = 0 + 1 + 1 by simp [one_add_one_eq_two]]; simp [he, ha]
  unfold un
  rw [substs_substs h2 hu hw, termSubstVec_cons₂ he.isUTerm ha.isUTerm]

lemma subst_bs {n m w ε : V} (hw : IsSemitermVec GraphLanguage n m w) (he : IsSemiterm GraphLanguage n ε) :
    termSubst GraphLanguage (qVec GraphLanguage w) (bs ε) = bs (termSubst GraphLanguage w ε) :=
  substs_qVec_bShift he hw

lemma qVec_eq {n w : V} (hw : IsUTermVec GraphLanguage n w) :
    qVec GraphLanguage w = ^#0 ∷ termBShiftVec GraphLanguage n w := by
  simp [Bootstrapping.qVec, hw.lh]

lemma semitermVec_succ {L : Language} [L.Encodable] [L.LORDefinable] {n m X : V}
    (h : IsSemitermVec L n m X) : IsSemitermVec L n (m + 1) X := by
  refine IsSemitermVec.iff.mpr ⟨h.lh, fun i hi => ?_⟩
  have := IsSemiterm.def.mp (h.nth hi)
  exact IsSemiterm.def.mpr ⟨this.1, le_trans this.2 (by simp)⟩

lemma qVec_semitermVec {k m w : V} (hw : IsSemitermVec GraphLanguage k m w) :
    IsSemitermVec GraphLanguage (k + 1 + 1) (m + 1 + 1) (qVec GraphLanguage (qVec GraphLanguage w)) := hw.qVec.qVec

lemma nth_qVec2_zero {w : V} : (qVec GraphLanguage (qVec GraphLanguage w)).[0] = ^#0 := by simp

lemma nth_qVec2_one {k m w : V} (hw : IsSemitermVec GraphLanguage k m w) :
    (qVec GraphLanguage (qVec GraphLanguage w)).[1] = ^#1 := by
  rw [show (1 : V) = 0 + 1 by simp, nth_qVec_succ hw.qVec.isUTerm (by simp)]; simp

lemma nth_qVec2_succ_succ {k m w i : V} (hw : IsSemitermVec GraphLanguage k m w) (hi : i < k) :
    (qVec GraphLanguage (qVec GraphLanguage w)).[i + 1 + 1] = termBShift GraphLanguage (termBShift GraphLanguage w.[i]) := by
  rw [nth_qVec_succ hw.qVec.isUTerm (by simpa using hi), nth_qVec_succ hw.isUTerm hi]

lemma VarVec.termSubst_bv2 {n m w i : V} (hw : IsSemitermVec GraphLanguage n m w) (hv : VarVec n w)
    (hi : i < n) :
    termSubst GraphLanguage (bv2 m) w.[i] = termBShift GraphLanguage (termBShift GraphLanguage w.[i]) := by
  rcases hv.cases hi with ⟨z, hz⟩ | ⟨x, hx⟩
  · have hzm : z < m := by have := hw.nth hi; rw [hz] at this; simpa using this
    rw [hz, termSubst_bvar, nth_bv2 hzm]; simp [add_assoc, one_add_one_eq_two]
  · rw [hx]; simp

lemma VarVec.termSubst_bv3 {n m w i : V} (hw : IsSemitermVec GraphLanguage n m w) (hv : VarVec n w)
    (hi : i < n) :
    termSubst GraphLanguage (bv3 m) w.[i] =
      termBShift GraphLanguage (termBShift GraphLanguage (termBShift GraphLanguage w.[i])) := by
  rcases hv.cases hi with ⟨z, hz⟩ | ⟨x, hx⟩
  · have hzm : z < m := by have := hw.nth hi; rw [hz] at this; simpa using this
    rw [hz, termSubst_bvar, nth_bv3 hzm]; simp [add_assoc]; norm_num
  · rw [hx]; simp

lemma nth_qVec2_lt_two {k m w c : V} (hw : IsSemitermVec GraphLanguage k m w) (hc : c < 2) :
    (qVec GraphLanguage (qVec GraphLanguage w)).[c] = ^#c := by
  rcases zero_or_succ c with rfl | ⟨c, rfl⟩
  · simp
  · have : c = 0 := by
      have : c + 1 < 1 + 1 := by simpa [one_add_one_eq_two] using hc
      simpa using this
    subst this; simpa using nth_qVec2_one hw

/-- The re-indexing vectors of atoms commute with a substitution of variables. -/
lemma atom_vec {n m w c : V} (hw : IsSemitermVec GraphLanguage n m w) (hv : VarVec n w) (hc : c < 2) :
    termSubstVec GraphLanguage (n + 1) (qVec GraphLanguage (qVec GraphLanguage w)) (^#c ∷ bv2 n) =
      termSubstVec GraphLanguage (n + 1) (^#c ∷ bv2 m) (^#0 ∷ termBShiftVec GraphLanguage n w) := by
  have h1 : IsUTermVec GraphLanguage (n + 1) (^#c ∷ bv2 n) := (bv2_semitermVec n).isUTerm.adjoin (by simp)
  have h2 : IsUTermVec GraphLanguage (n + 1) (^#0 ∷ termBShiftVec GraphLanguage n w) :=
    hw.termBShiftVec.isUTerm.adjoin (by simp)
  apply nth_ext' (n + 1) (by simp [h1]) (by simp [h2])
  intro i hi
  rw [nth_termSubstVec h1 hi, nth_termSubstVec h2 hi]
  rcases zero_or_succ i with rfl | ⟨j, rfl⟩
  · simp [nth_qVec2_lt_two hw hc]
  · have hj : j < n := by simpa using hi
    have hwj := hw.nth hj
    rw [nth_adjoin_succ, nth_adjoin_succ, nth_bv2 hj, termSubst_bvar,
      show j + 2 = j + 1 + 1 by simp [add_assoc, one_add_one_eq_two],
      nth_qVec2_succ_succ hw hj, nth_termBShiftVec hw.isUTerm hj, substs_cons_bShift hwj,
      hv.termSubst_bv2 hw hj]

/-- The re-indexing vectors of graphs commute with a substitution of variables. -/
lemma graph_vec {n m w c : V} (hw : IsSemitermVec GraphLanguage n m w) (hv : VarVec n w) (hc : c < 2) :
    termSubstVec GraphLanguage (n + 1) (qVec GraphLanguage (qVec GraphLanguage (^#0 ∷ termBShiftVec GraphLanguage n w)))
        (^#c ∷ bv3 n) =
      termSubstVec GraphLanguage (n + 1) (^#c ∷ bv3 m) (^#0 ∷ termBShiftVec GraphLanguage n w) := by
  have hu : IsSemitermVec GraphLanguage (n + 1) (m + 1) (^#0 ∷ termBShiftVec GraphLanguage n w) :=
    IsSemitermVec.cons_iff.mpr ⟨by simp, hw.termBShiftVec⟩
  have h1 : IsUTermVec GraphLanguage (n + 1) (^#c ∷ bv3 n) := (bv3_semitermVec n).isUTerm.adjoin (by simp)
  apply nth_ext' (n + 1) (by simp [h1]) (by simp [hu.isUTerm])
  intro i hi
  rw [nth_termSubstVec h1 hi, nth_termSubstVec hu.isUTerm hi]
  rcases zero_or_succ i with rfl | ⟨j, rfl⟩
  · simp [nth_qVec2_lt_two hu hc]
  · have hj : j < n := by simpa using hi
    have hwj := hw.nth hj
    rw [nth_adjoin_succ, nth_adjoin_succ, nth_bv3 hj, termSubst_bvar,
      show j + 3 = j + 1 + 1 + 1 by simp [add_assoc]; norm_num,
      nth_qVec2_succ_succ hu (by simpa using hj), nth_adjoin_succ,
      nth_termBShiftVec hw.isUTerm hj, substs_cons_bShift hwj, hv.termSubst_bv3 hw hj]

/-! ## Graphs, atoms and formulas -/

lemma subst_op (φ : Semisentence GraphLanguage 4) {n m w ε : V} (hw : IsSemitermVec GraphLanguage n m w)
    (he : IsSemiterm GraphLanguage n ε) :
    subst GraphLanguage (qVec GraphLanguage (qVec GraphLanguage (qVec GraphLanguage w)))
        (subst GraphLanguage (bs (bs (bs ε)) ∷ ^#1 ∷ ^#0 ∷ ^#2 ∷ (0 : V)) (tq φ : V)) =
      subst GraphLanguage (bs (bs (bs (termSubst GraphLanguage w ε))) ∷ ^#1 ∷ ^#0 ∷ ^#2 ∷ (0 : V)) (tq φ : V) := by
  have h4 : IsSemiformula GraphLanguage 4 (tq φ : V) := by simpa using tq_semiformula (V := V) φ
  have hu := hw.qVec
  have he3 := bs_semiterm (bs_semiterm (bs_semiterm he))
  have o₃ : IsSemitermVec GraphLanguage 3 (n + 1 + 1 + 1) (^#1 ∷ ^#0 ∷ ^#2 ∷ (0 : V)) := by
    rw [show (3 : V) = 0 + 1 + 1 + 1 by norm_num]
    exact vec_bvar_cons (lt_add_three one_lt_three') (vec_bvar_cons (lt_add_three zero_lt_three')
      (vec_bvar_cons (lt_add_three two_lt_three') (by simp)))
  have o : IsSemitermVec GraphLanguage 4 (n + 1 + 1 + 1) (bs (bs (bs ε)) ∷ ^#1 ∷ ^#0 ∷ ^#2 ∷ (0 : V)) := by
    rw [show (4 : V) = 3 + 1 by norm_num]
    exact IsSemitermVec.cons_iff.mpr ⟨he3, o₃⟩
  have hq := hu.qVec.qVec
  rw [substs_substs h4 hq o]
  congr 1
  have e2 : (qVec GraphLanguage (qVec GraphLanguage (qVec GraphLanguage w))).[2] = ^#2 := by
    rw [show (2 : V) = 0 + 1 + 1 by simp [one_add_one_eq_two], nth_qVec2_succ_succ hu (by simp)]
    simp [add_assoc, one_add_one_eq_two]
  rw [show (4 : V) = 0 + 1 + 1 + 1 + 1 by norm_num,
    termSubstVec_cons he3.isUTerm (by simpa [show (0 : V) + 1 + 1 + 1 = 3 by norm_num] using
      o₃.isUTerm),
    termSubstVec_cons (by simp) (by simp [show (0 : V) + 1 + 1 = 2 by simp [one_add_one_eq_two]]),
    termSubstVec_cons (by simp) (by simp), termSubstVec_cons (by simp) (by simp),
    subst_bs hw.qVec.qVec (bs_semiterm (bs_semiterm he)), subst_bs hw.qVec (bs_semiterm he),
    subst_bs hw he]
  simp [nth_qVec2_one hu, e2]

lemma subst_binG (φ : Semisentence GraphLanguage 4) {n m w ε A B : V} (hw : IsSemitermVec GraphLanguage n m w)
    (hv : VarVec n w) (he : IsSemiterm GraphLanguage n ε) (hA : IsSemiformula GraphLanguage (n + 1) A)
    (hB : IsSemiformula GraphLanguage (n + 1) B) :
    subst GraphLanguage (^#0 ∷ termBShiftVec GraphLanguage n w) (binG (tq φ) ε n A B) =
      binG (tq φ) (termSubst GraphLanguage w ε) m (subst GraphLanguage (^#0 ∷ termBShiftVec GraphLanguage n w) A)
        (subst GraphLanguage (^#0 ∷ termBShiftVec GraphLanguage n w) B) := by
  have hqe := qVec_eq hw.isUTerm
  set u := ^#0 ∷ termBShiftVec GraphLanguage n w
  have hu : IsSemitermVec GraphLanguage (n + 1) (m + 1) u :=
    IsSemitermVec.cons_iff.mpr ⟨by simp, hw.termBShiftVec⟩
  have h4 : IsSemiformula GraphLanguage 4 (tq φ : V) := by simpa using tq_semiformula (V := V) φ
  have e : ∀ k : V, k + 1 + 1 + 1 = k + 3 := fun k => by rw [add_assoc, add_assoc]; norm_num
  have l : ∀ k : V, IsSemitermVec GraphLanguage (k + 1) (k + 1 + 1 + 1) (^#1 ∷ bv3 k) := fun k =>
    vec_bvar_cons (lt_add_three one_lt_three') (by rw [e]; exact bv3_semitermVec k)
  have r : ∀ k : V, IsSemitermVec GraphLanguage (k + 1) (k + 1 + 1 + 1) (^#0 ∷ bv3 k) := fun k =>
    vec_bvar_cons (lt_add_three zero_lt_three') (by rw [e]; exact bv3_semitermVec k)
  have o : IsSemitermVec GraphLanguage 4 (n + 1 + 1 + 1) (bs (bs (bs ε)) ∷ ^#1 ∷ ^#0 ∷ ^#2 ∷ (0 : V)) := by
    rw [show (4 : V) = 0 + 1 + 1 + 1 + 1 by norm_num]
    exact IsSemitermVec.cons_iff.mpr ⟨bs_semiterm (bs_semiterm (bs_semiterm he)),
      vec_bvar_cons (lt_add_three one_lt_three') (vec_bvar_cons (lt_add_three zero_lt_three')
      (vec_bvar_cons (lt_add_three two_lt_three') (by simp)))⟩
  have hq := hu.qVec.qVec
  have hsA := (hA.subst (l n)).isUFormula
  have hsB := (hB.subst (r n)).isUFormula
  have hsO := (h4.subst o).isUFormula
  have hop := subst_op φ hw he
  rw [hqe] at hop
  simp only [binG]
  rw [substs_ex (by simp [hsA, hsB, hsO]), substs_ex (by simp [hsA, hsB, hsO]),
    substs_and (by simp [hsA, hsB]) hsO, substs_and hsA hsB,
    substs_substs hA hq (l n), substs_substs hB hq (r n), hop,
    graph_vec hw hv one_lt_two, graph_vec hw hv zero_lt_two',
    substs_substs hA (l m) hu, substs_substs hB (r m) hu]

lemma termBShiftVec_lang {n w : V} (hw : IsUTermVec ℒₒᵣ n w) (hv : VarVec n w) :
    termBShiftVec ℒₒᵣ n w = termBShiftVec GraphLanguage n w := by
  have hw' : IsUTermVec GraphLanguage n w := ⟨hw.lh, fun i hi => by
    rcases hv.cases hi with ⟨z, hz⟩ | ⟨x, hx⟩ <;> simp [*]⟩
  apply nth_ext' n (by simp [hw]) (by simp [hw'])
  intro i hi
  rw [nth_termBShiftVec hw hi, nth_termBShiftVec hw' hi]
  rcases hv.cases hi with ⟨z, hz⟩ | ⟨x, hx⟩
  · simp [hz]
  · simp [hx]

lemma termSubst_add {w a b : V} (ha : IsUTerm ℒₒᵣ a) (hb : IsUTerm ℒₒᵣ b) :
    termSubst ℒₒᵣ w (a ^+ b) = termSubst ℒₒᵣ w a ^+ termSubst ℒₒᵣ w b := by
  unfold qqAdd
  rw [termSubst_func (by simp) (by simp [ha, hb]), termSubstVec_cons₂ ha hb]

lemma termSubst_mul {w a b : V} (ha : IsUTerm ℒₒᵣ a) (hb : IsUTerm ℒₒᵣ b) :
    termSubst ℒₒᵣ w (a ^* b) = termSubst ℒₒᵣ w a ^* termSubst ℒₒᵣ w b := by
  unfold qqMul
  rw [termSubst_func (by simp) (by simp [ha, hb]), termSubstVec_cons₂ ha hb]

lemma termSubst_zero (w : V) : termSubst ℒₒᵣ w (𝟎 : V) = 𝟎 := by
  rw [qqZero_eq_qqFunc, termSubst_func (by simp) (by simp)]; simp

lemma termSubst_one (w : V) : termSubst ℒₒᵣ w (𝟏 : V) = 𝟏 := by
  rw [qqOne_eq_qqFunc, termSubst_func (by simp) (by simp)]; simp

/-- Graphs commute with substitutions of variables. -/
lemma G_subst {ε n m w : V} (hw : IsSemitermVec ℒₒᵣ n m w) (hv : VarVec n w)
    (he : IsSemiterm GraphLanguage n ε) : ∀ t, IsSemiterm ℒₒᵣ n t →
      G ι (termSubst GraphLanguage w ε) m (termSubst ℒₒᵣ w t) =
        subst GraphLanguage (^#0 ∷ termBShiftVec GraphLanguage n w) (G ι ε n t) := by
  have hws := hv.set hw
  have hqe := qVec_eq hws.isUTerm
  have hu : IsSemitermVec GraphLanguage (n + 1) (m + 1) (^#0 ∷ termBShiftVec GraphLanguage n w) :=
    IsSemitermVec.cons_iff.mpr ⟨by simp, hws.termBShiftVec⟩
  have hbs : termSubst GraphLanguage (^#0 ∷ termBShiftVec GraphLanguage n w) (bs ε) = bs (termSubst GraphLanguage w ε) := by
    rw [← hqe]; exact subst_bs hws he
  refine IsSemiterm.induction 𝚷 (P := fun t =>
    G ι (termSubst GraphLanguage w ε) m (termSubst ℒₒᵣ w t) =
      subst GraphLanguage (^#0 ∷ termBShiftVec GraphLanguage n w) (G ι ε n t)) ?_ ?_ ?_ ?_
  · definability
  · intro z hz
    rw [termSubst_bvar, G_bvar, subst_eqAt ι hu (bs_semiterm he) (a := ^#0) (b := ^#(z + 1))
      (by simp) (by simp [hz]), hbs]
    rw [termSubst_bvar, termSubst_bvar, nth_adjoin_zero, nth_adjoin_succ,
      nth_termBShiftVec hws.isUTerm hz]
    rcases hv.cases hz with ⟨a, ha⟩ | ⟨b, hb⟩
    · rw [ha]; simp
    · rw [hb]; simp
  · intro x
    rw [termSubst_fvar, G_fvar, G_fvar, subst_eqAt ι hu (bs_semiterm he) (a := ^#0) (b := ^&x)
      (by simp) (by simp), hbs]
    simp
  · intro k f v hf hvv ih
    rcases lor_func_cases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have : v = 0 := by simpa using hvv
      subst this
      rw [show (^func (0 : V) (zeroIndex : V) 0 : V) = 𝟎 by rw [qqZero_eq_qqFunc], termSubst_zero,
        G_zero, G_zero, subst_un ι.zero hu (bs_semiterm he) (show IsSemiterm GraphLanguage (n + 1) ^#0
          by simp), hbs]
      simp
    · have : v = 0 := by simpa using hvv
      subst this
      rw [show (^func (0 : V) (oneIndex : V) 0 : V) = 𝟏 by rw [qqOne_eq_qqFunc], termSubst_one,
        G_one, G_one, subst_un ι.one hu (bs_semiterm he) (show IsSemiterm GraphLanguage (n + 1) ^#0
          by simp), hbs]
      simp
    · have h0 := hvv.nth zero_lt_two'
      have h1 := hvv.nth one_lt_two
      rw [← vec2_eq' hvv.lh, show (^func (2 : V) (addIndex : V) (v.[0] ∷ v.[1] ∷ 0) : V) =
        v.[0] ^+ v.[1] by rfl, termSubst_add h0.isUTerm h1.isUTerm,
        G_add ι (hw.termSubst h0).isUTerm (hw.termSubst h1).isUTerm, G_add ι h0.isUTerm h1.isUTerm,
        ih 0 zero_lt_two', ih 1 one_lt_two,
        subst_binG ι.add hws hv he (G_semiformula ι he _ h0) (G_semiformula ι he _ h1)]
    · have h0 := hvv.nth zero_lt_two'
      have h1 := hvv.nth one_lt_two
      rw [← vec2_eq' hvv.lh, show (^func (2 : V) (mulIndex : V) (v.[0] ∷ v.[1] ∷ 0) : V) =
        v.[0] ^* v.[1] by rfl, termSubst_mul h0.isUTerm h1.isUTerm,
        G_mul ι (hw.termSubst h0).isUTerm (hw.termSubst h1).isUTerm, G_mul ι h0.isUTerm h1.isUTerm,
        ih 0 zero_lt_two', ih 1 one_lt_two,
        subst_binG ι.mul hws hv he (G_semiformula ι he _ h0) (G_semiformula ι he _ h1)]

lemma subst_relT2 (R : V) {n m w ε : V} (hw : IsSemitermVec GraphLanguage n m w)
    (he : IsSemiterm GraphLanguage n ε) :
    subst GraphLanguage (qVec GraphLanguage (qVec GraphLanguage w)) (subst GraphLanguage (bs (bs ε) ∷ ^#1 ∷ ^#0 ∷ (0 : V)) (relT ι R)) =
      subst GraphLanguage (bs (bs (termSubst GraphLanguage w ε)) ∷ ^#1 ∷ ^#0 ∷ (0 : V)) (relT ι R) := by
  have hR : IsSemiformula GraphLanguage 3 (relT ι R) := relT_semiformula ι R le_rfl
  have he2 := bs_semiterm (bs_semiterm he)
  have o₂ : IsSemitermVec GraphLanguage 2 (n + 1 + 1) (^#1 ∷ ^#0 ∷ (0 : V)) := by
    rw [show (2 : V) = 0 + 1 + 1 by simp [one_add_one_eq_two]]
    exact vec_bvar_cons (lt_add_two one_lt_two) (vec_bvar_cons (lt_add_two zero_lt_two') (by simp))
  have o : IsSemitermVec GraphLanguage 3 (n + 1 + 1) (bs (bs ε) ∷ ^#1 ∷ ^#0 ∷ (0 : V)) := by
    rw [show (3 : V) = 2 + 1 by norm_num]
    exact IsSemitermVec.cons_iff.mpr ⟨he2, o₂⟩
  rw [substs_substs hR hw.qVec.qVec o]
  congr 1
  rw [show (3 : V) = 0 + 1 + 1 + 1 by norm_num,
    termSubstVec_cons he2.isUTerm (by simpa [show (0 : V) + 1 + 1 = 2 by simp [one_add_one_eq_two]]
      using o₂.isUTerm),
    termSubstVec_cons (by simp) (by simp), termSubstVec_cons (by simp) (by simp),
    subst_bs hw.qVec (bs_semiterm he), subst_bs hw he]
  simp [nth_qVec2_one hw]

lemma subst_atomJ {ε n m w R t₀ t₁ : V} (hw : IsSemitermVec ℒₒᵣ n m w) (hv : VarVec n w)
    (he : IsSemiterm GraphLanguage n ε) (h₀ : IsSemiterm ℒₒᵣ n t₀) (h₁ : IsSemiterm ℒₒᵣ n t₁) :
    subst GraphLanguage w (atomJ ι ε n R t₀ t₁) =
      atomJ ι (termSubst GraphLanguage w ε) m R (termSubst ℒₒᵣ w t₀) (termSubst ℒₒᵣ w t₁) := by
  have hws := hv.set hw
  have hu : IsSemitermVec GraphLanguage (n + 1) (m + 1) (^#0 ∷ termBShiftVec GraphLanguage n w) :=
    IsSemitermVec.cons_iff.mpr ⟨by simp, hws.termBShiftVec⟩
  have e : ∀ k : V, k + 1 + 1 = k + 2 := fun k => by rw [add_assoc, one_add_one_eq_two]
  have l : ∀ k : V, IsSemitermVec GraphLanguage (k + 1) (k + 1 + 1) (^#1 ∷ bv2 k) := fun k =>
    vec_bvar_cons (lt_add_two one_lt_two) (by rw [e]; exact bv2_semitermVec k)
  have r : ∀ k : V, IsSemitermVec GraphLanguage (k + 1) (k + 1 + 1) (^#0 ∷ bv2 k) := fun k =>
    vec_bvar_cons (lt_add_two zero_lt_two') (by rw [e]; exact bv2_semitermVec k)
  have o : IsSemitermVec GraphLanguage 3 (n + 1 + 1) (bs (bs ε) ∷ ^#1 ∷ ^#0 ∷ (0 : V)) := by
    rw [show (3 : V) = 0 + 1 + 1 + 1 by norm_num]
    exact IsSemitermVec.cons_iff.mpr ⟨bs_semiterm (bs_semiterm he),
      vec_bvar_cons (lt_add_two one_lt_two) (vec_bvar_cons (lt_add_two zero_lt_two') (by simp))⟩
  have hR : IsSemiformula GraphLanguage 3 (relT ι R) := relT_semiformula ι R le_rfl
  have g₀ := G_semiformula ι he t₀ h₀
  have g₁ := G_semiformula ι he t₁ h₁
  have hsA := (g₀.subst (l n)).isUFormula
  have hsB := (g₁.subst (r n)).isUFormula
  have hsO := (hR.subst o).isUFormula
  have hq := hws.qVec.qVec
  simp only [atomJ]
  rw [substs_ex (by simp [hsA, hsB, hsO]), substs_ex (by simp [hsA, hsB, hsO]),
    substs_and (by simp [hsA, hsB]) hsO, substs_and hsA hsB,
    substs_substs g₀ hq (l n), substs_substs g₁ hq (r n), subst_relT2 ι R hws he,
    atom_vec hws hv one_lt_two, atom_vec hws hv zero_lt_two',
    G_subst ι hw hv he t₀ h₀, G_subst ι hw hv he t₁ h₁,
    substs_substs g₀ (l m) hu, substs_substs g₁ (r m) hu]

lemma VarVec.qVec {n m w : V} (hw : IsSemitermVec ℒₒᵣ n m w) (hv : VarVec n w) :
    VarVec (n + 1) (qVec ℒₒᵣ w) := by
  apply VarVec.of_cases
  intro i hi
  rcases zero_or_succ i with rfl | ⟨j, rfl⟩
  · left; exact ⟨0, by simp [Bootstrapping.qVec]⟩
  · have hj : j < n := by simpa using hi
    rw [show (Bootstrapping.qVec ℒₒᵣ w).[j + 1] = termBShift ℒₒᵣ w.[j] by
      simp only [Bootstrapping.qVec, nth_adjoin_succ]
      rw [hw.lh, nth_termBShiftVec hw.isUTerm hj]]
    rcases hv.cases hj with ⟨z, hz⟩ | ⟨x, hx⟩
    · left; exact ⟨z + 1, by rw [hz]; simp⟩
    · right; exact ⟨x, by rw [hx]; simp⟩

lemma qVec_lang {n w : V} (hw : IsUTermVec ℒₒᵣ n w) (hv : VarVec n w) :
    qVec ℒₒᵣ w = qVec GraphLanguage w := by
  simp [qVec, ← hw.lh, termBShiftVec_lang hw hv]

/-- The translation commutes with substitutions of variables. -/
theorem J_subst : ∀ n p : V, IsSemiformula ℒₒᵣ n p → ∀ ε, IsSemiterm GraphLanguage n ε →
    ∀ m w : V, IsSemitermVec ℒₒᵣ n m w → VarVec n w →
      J ι (termSubst GraphLanguage w ε) m (subst ℒₒᵣ w p) = subst GraphLanguage w (J ι ε n p) := by
  intro n p hp
  revert n p
  apply IsSemiformula.induction1 𝚷 (P := fun n p => ∀ ε, IsSemiterm GraphLanguage n ε →
    ∀ m w : V, IsSemitermVec ℒₒᵣ n m w → VarVec n w →
      J ι (termSubst GraphLanguage w ε) m (subst ℒₒᵣ w p) = subst GraphLanguage w (J ι ε n p))
  · definability
  · intro n k r v hr hv ε he m w hw hvw
    have := rel_two_lor hr; subst this
    have h0 := hv.nth zero_lt_two'
    have h1 := hv.nth one_lt_two
    rw [substs_rel hr hv.isUTerm, J_rel hr (hw.termSubstVec hv).isUTerm, J_rel hr hv.isUTerm,
      subst_atomJ ι hw hvw he h0 h1, nth_termSubstVec hv.isUTerm zero_lt_two',
      nth_termSubstVec hv.isUTerm one_lt_two]
  · intro n k r v hr hv ε he m w hw hvw
    have := rel_two_lor hr; subst this
    have h0 := hv.nth zero_lt_two'
    have h1 := hv.nth one_lt_two
    rw [substs_nrel hr hv.isUTerm, J_nrel hr (hw.termSubstVec hv).isUTerm, J_nrel hr hv.isUTerm,
      substs_neg (atomJ_semiformula ι he h0 h1) (hvw.set hw), subst_atomJ ι hw hvw he h0 h1,
      nth_termSubstVec hv.isUTerm zero_lt_two', nth_termSubstVec hv.isUTerm one_lt_two]
  · intro n ε _ m w _ _; simp
  · intro n ε _ m w _ _; simp
  · intro n p q hp hq ihp ihq ε he m w hw hvw
    rw [substs_and hp.isUFormula hq.isUFormula, J_and (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      J_and hp.isUFormula hq.isUFormula, ihp ε he m w hw hvw, ihq ε he m w hw hvw,
      substs_and (J_semiformula ι n p hp ε he).isUFormula (J_semiformula ι n q hq ε he).isUFormula]
  · intro n p q hp hq ihp ihq ε he m w hw hvw
    rw [substs_or hp.isUFormula hq.isUFormula, J_or (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      J_or hp.isUFormula hq.isUFormula, ihp ε he m w hw hvw, ihq ε he m w hw hvw,
      substs_or (J_semiformula ι n p hp ε he).isUFormula (J_semiformula ι n q hq ε he).isUFormula]
  · intro n p hp ih ε he m w hw hvw
    have hd := un_semiformula (V := V) ι.dom (bs_semiterm he) (a := ^#0) (by simp)
    have hj := J_semiformula ι _ p hp _ (bs_semiterm he)
    have hq := hw.qVec
    have hql := qVec_lang hw.isUTerm hvw
    have hqs : IsSemitermVec GraphLanguage (n + 1) (m + 1) (qVec GraphLanguage w) := hql ▸ (hvw.qVec hw).set hq
    have hbs : termSubst GraphLanguage (qVec GraphLanguage w) (bs ε) = bs (termSubst GraphLanguage w ε) :=
      subst_bs (hvw.set hw) he
    have := ih _ (bs_semiterm he) (m + 1) (qVec ℒₒᵣ w) hq (hvw.qVec hw)
    rw [hql, hbs] at this
    rw [substs_all hp.isUFormula, J_all (hp.subst hq).isUFormula, J_all hp.isUFormula, hql,
      this, substs_all (by simp [hd.isUFormula, hj.isUFormula]),
      substs_or (by simp [hd.isUFormula]) hj.isUFormula,
      substs_neg hd hqs, subst_un ι.dom hqs (bs_semiterm he) (show IsSemiterm GraphLanguage (n + 1) ^#0
        by simp), hbs]
    simp
  · intro n p hp ih ε he m w hw hvw
    have hd := un_semiformula (V := V) ι.dom (bs_semiterm he) (a := ^#0) (by simp)
    have hj := J_semiformula ι _ p hp _ (bs_semiterm he)
    have hq := hw.qVec
    have hql := qVec_lang hw.isUTerm hvw
    have hqs : IsSemitermVec GraphLanguage (n + 1) (m + 1) (qVec GraphLanguage w) := hql ▸ (hvw.qVec hw).set hq
    have hbs : termSubst GraphLanguage (qVec GraphLanguage w) (bs ε) = bs (termSubst GraphLanguage w ε) :=
      subst_bs (hvw.set hw) he
    have := ih _ (bs_semiterm he) (m + 1) (qVec ℒₒᵣ w) hq (hvw.qVec hw)
    rw [hql, hbs] at this
    rw [substs_ex hp.isUFormula, J_exs (hp.subst hq).isUFormula, J_exs hp.isUFormula, hql,
      this, substs_ex (by simp [hd.isUFormula, hj.isUFormula]),
      substs_and hd.isUFormula hj.isUFormula, subst_un ι.dom hqs (bs_semiterm he)
        (show IsSemiterm GraphLanguage (n + 1) ^#0 by simp), hbs]
    simp

end PalomarI3380.Calibration.ArithmeticInterpretation
