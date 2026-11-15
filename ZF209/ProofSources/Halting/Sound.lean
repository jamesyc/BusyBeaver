module
public import Halting.Absorb
public import CKernel.Nat
public import SearchProvability
public import FoundationReverseCalibration
public import DiagonalGateEndpoint
public import SourceZFConsistency
public import Halting.ChiX
@[expose] public section
/-! # Soundness of C in models of ZF

A standard `cRule`-trace consists of theorems of the machine's calculus (`ExactProvable`), which
translate to source theorems (the old reverse translation, gate discharged) and so hold in every
model of ZF. -/
namespace ZF209.Halting
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.SetTheory
open ZFR.ArithmeticRepresentation C209Soundness

lemma codes_nat_head {f : CKernel.Generic.Codes ℕ → ℕ} :
    f (ZF209.Internal.codes : CKernel.Generic.Codes ℕ) = f CKernel.natCodes := by
  rw [ZF209.Internal.codes_nat]

lemma imp_nat (a b : ℕ) : ZF209.Internal.imp a b = impCode a b := by
  have := congrArg (fun K : CKernel.Generic.Codes ℕ => K.imp a b) ZF209.Internal.codes_nat
  simpa [ZF209.Internal.codes, CKernel.natCodes] using this

lemma all_nat (i b : ℕ) : ZF209.Internal.all i b = allCode i b := by
  have := congrArg (fun K : CKernel.Generic.Codes ℕ => K.all i b) ZF209.Internal.codes_nat
  simpa [ZF209.Internal.codes, CKernel.natCodes] using this

lemma cAxiom_nat {r : ℕ} (h : cAxiom r) : ExactProvable r := by
  obtain ⟨a, d, h', u, H⟩ := h
  rw [ZF209.Internal.codes_nat] at H
  rcases H with rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨hu, rfl⟩ | ⟨hd, hh, rfl⟩
  · exact C209Search.proved_zero
  · exact CKernel.natSys.h6 d a h'
  · exact CKernel.natSys.h5 d h'
  · exact CKernel.natSys.h4 h' d a
  · exact CKernel.natSys.h3 h' d a
  · exact CKernel.natSys.h2 d a h'
  · exact CKernel.natSys.h1 d h'
  · have hu' : u = d ∨ u < d := hu
    exact CKernel.natSys.r8 d a h' u (show u ≤ d from hu'.elim (fun h => h ▸ Nat.le_refl _) Nat.le_of_lt)
  · exact CKernel.natSys.gate h' d a hh hd

/-- Every entry of a standard trace is a theorem of the machine's calculus. -/
theorem trace_provable : ∀ p : ℕ, modelTrace cRule p → ∀ x, modelMember x p → ExactProvable x := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp x hx
    by_cases hz : p = 0
    · subst hz; simp [modelMember, modelMemberCode_zero] at hx
    have hpos : 0 < p := Nat.pos_of_ne_zero hz
    have he : p = modelListCons (modelListHead p) (modelListTail p) :=
      (modelList_reconstruct p hpos).symm
    rw [he, modelTrace_cons] at hp
    rw [he, modelMember_cons] at hx
    have ht := modelListTail_lt p hpos
    have ihT := ih _ ht hp.1
    rcases hx with rfl | hx
    · rcases hp.2 with hax | ⟨b, hb, hi⟩ | ⟨i, b, hb, hr⟩
      · exact cAxiom_nat hax
      · exact CKernel.natSys.mp (ihT b hb) (by simpa [imp_nat, CKernel.natSys, CKernel.natCodes] using ihT _ hi)
      · rw [hr, all_nat]; exact CKernel.natSys.gen i (ihT b hb)
    · exact ihT x hx

theorem exactProvable_of_cprov {x : ℕ} (h : CProv x) : ExactProvable x := by
  obtain ⟨p, hp, hm⟩ := (D_iff' x).mp h
  exact trace_provable p hp x hm

/-- The gate obligation of the reverse translation, discharged. -/
theorem gate_ok : ZFR.GateTranslationObligation :=
  ZFR.gate_obligation_of_distinct fun a d h had hah hdh =>
    ZFR.source_literal_gate_of_positive a d h had hah
      (ZFR.FoundationBridge.positive_source_of_axiom_translation
        ZFR.FoundationBridge.foundation_axiom_translation a d h had hah hdh)

/-- Theorems of the machine's calculus hold in every model of ZF. -/
theorem exact_true {x : ℕ} (hx : ExactProvable x) {V : Type} [SetStructure V] [Nonempty V]
    [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] (s : ℕ → V) : evalCode (fun a b : V => a ∈ b) x s := by
  obtain ⟨xs, hxs, hm⟩ := hx
  obtain ⟨Γ, hΓ, hd⟩ := ZFR.exact_history_translation gate_ok hxs x hm
  have ht := ZFR.NDSemantics.sound (fun a b : V => a ∈ b) hd s
    (fun q hq => ZFR.NDSemantics.all_source_zf_axioms_valid V q (hΓ q hq) s)
  rw [ZFR.translateCode, ZFR.eval_translate] at ht
  exact ht

/-! ## Evaluating codes -/

section Eval
variable {α : Type*} (mem : α → α → Prop) (s : Assignment α)

lemma mem_nat (a b : ℕ) : ZF209.Internal.mem a b = memCode a b := by
  have := congrArg (fun K : CKernel.Generic.Codes ℕ => K.mem a b) ZF209.Internal.codes_nat
  simpa [ZF209.Internal.codes, CKernel.natCodes] using this

lemma ev_imp (a b : ℕ) :
    evalCode mem (ZF209.Internal.imp a b) s ↔ (evalCode mem a s → evalCode mem b s) := by
  rw [imp_nat, show impCode a b = (Formula.imp (decode a) (decode b)).code by
    simp [impCode, Formula.code, decode_code], evalCode_of_formula]
  rfl

lemma ev_all (x a : ℕ) :
    evalCode mem (ZF209.Internal.all x a) s ↔ ∀ v, evalCode mem a (update s x v) := by
  rw [all_nat, show allCode x a = (Formula.all x (decode a)).code by
    simp [allCode, Formula.code, decode_code], evalCode_of_formula]
  rfl

lemma ev_mem (a b : ℕ) : evalCode mem (ZF209.Internal.mem a b) s ↔ mem (s a) (s b) := by
  rw [mem_nat, show memCode a b = (Formula.mem a b).code by simp [memCode, Formula.code],
    evalCode_of_formula]
  rfl

lemma ev_one : evalCode mem 1 s ↔ mem (s 0) (s 0) := by
  have : (1 : ℕ) = ZF209.Internal.mem 0 0 := by rw [mem_nat]; rfl
  rw [this, ev_mem]

end Eval

/-! ## Derived connectives and atoms in models of ZF -/

section ZFEval
open ZF209.Internal.Tait
variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local notation "ev" => evalCode (fun a b : V => a ∈ b)

lemma upd0 {s : Assignment V} {x : ℕ} (hx : x ≠ 0) (v : V) : update s x v 0 = s 0 := by
  simp [update, Ne.symm hx]

lemma ev_cneg (A : ℕ) {s : Assignment V} (h0 : s 0 = ∅) :
    ev (ZF209.Internal.cneg A) s ↔ ¬ev A s := by
  simp [ZF209.Internal.cneg, ev_imp, ev_one, h0]

lemma ev_cand (A B : ℕ) {s : Assignment V} (h0 : s 0 = ∅) :
    ev (ZF209.Internal.cand A B) s ↔ ev A s ∧ ev B s := by
  simp only [ZF209.Internal.cand, ev_cneg _ h0, ev_imp]; tauto

lemma ev_ciff (A B : ℕ) {s : Assignment V} (h0 : s 0 = ∅) :
    ev (ZF209.Internal.ciff A B) s ↔ (ev A s ↔ ev B s) := by
  simp only [ZF209.Internal.ciff, ev_cand _ _ h0, ev_imp]; tauto

lemma ev_cex (x A : ℕ) {s : Assignment V} (h0 : s 0 = ∅) (hx : x ≠ 0) :
    ev (ZF209.Internal.cex x A) s ↔ ∃ v, ev A (update s x v) := by
  simp only [ZF209.Internal.cex, ev_cneg _ h0, ev_all]
  simp only [fun v => ev_cneg A (s := update s x v) (by rw [upd0 hx]; exact h0)]
  push Not; rfl

lemma ev_ciff_upd (A B x : ℕ) (v : V) {s : Assignment V} (h0 : s 0 = ∅) (hx : x ≠ 0) :
    ev (ZF209.Internal.ciff A B) (update s x v) ↔
      (ev A (update s x v) ↔ ev B (update s x v)) :=
  ev_ciff A B (by rw [upd0 hx]; exact h0)

lemma ev_cand_upd (A B x : ℕ) (v : V) {s : Assignment V} (h0 : s 0 = ∅) (hx : x ≠ 0) :
    ev (ZF209.Internal.cand A B) (update s x v) ↔ ev A (update s x v) ∧ ev B (update s x v) :=
  ev_cand A B (by rw [upd0 hx]; exact h0)

lemma rlab_ne_zero (k : ℕ) : rlab k ≠ 0 := by simp [rlab]
lemma xlab_ne_zero (f d : ℕ) : xlab f d ≠ 0 := by simp [xlab]
lemma ylab_ne_zero (j : ℕ) : ylab j ≠ 0 := by simp [ylab]

lemma ev_ceqv (a b : ℕ) {s : Assignment V} (h0 : s 0 = ∅) (ha : a ≠ rlab 0) (hb : b ≠ rlab 0) :
    ev (ceqv a b) s ↔ s a = s b := by
  simp only [ceqv, ev_cand _ _ h0, ev_all, ev_ciff_upd _ _ _ _ h0 (rlab_ne_zero 0), ev_mem]
  simp [update, ha, hb]
  constructor
  · rintro ⟨h₁, -⟩; exact mem_ext h₁
  · rintro h; simp [h]

lemma rlab_inj {j k : ℕ} (h : rlab j = rlab k) : j = k := by
  simpa [rlab] using h

lemma ev_atomL1' (a b r₁ r₂ : ℕ) {s : Assignment V} (h0 : s 0 = ∅) (h1 : r₁ ≠ 0) (h2 : r₂ ≠ 0)
    (h12 : r₁ ≠ r₂) (h10 : r₁ ≠ rlab 0) (h20 : r₂ ≠ rlab 0) (ha0 : a ≠ rlab 0) (hb0 : b ≠ rlab 0)
    (ha1 : a ≠ r₁) (ha2 : a ≠ r₂) (hb1 : b ≠ r₁) (hb2 : b ≠ r₂) :
    ev (ZF209.Internal.cex r₁ (ZF209.Internal.cex r₂ (ZF209.Internal.cand
      (ZF209.Internal.cand (ceqv a r₁) (ceqv b r₂)) (ZF209.Internal.mem r₁ r₂)))) s ↔ s a ∈ s b := by
  rw [ev_cex _ _ h0 h1]
  constructor
  · rintro ⟨u, hu⟩
    have e1 : update s r₁ u 0 = ∅ := by rw [upd0 h1]; exact h0
    rw [ev_cex _ _ e1 h2] at hu
    obtain ⟨w, hw⟩ := hu
    have e2 : update (update s r₁ u) r₂ w 0 = ∅ := by rw [upd0 h2]; exact e1
    rw [ev_cand _ _ e2, ev_cand _ _ e2, ev_ceqv _ _ e2 ha0 h10, ev_ceqv _ _ e2 hb0 h20, ev_mem] at hw
    simp [update, ha1, ha2, hb1, hb2, h12, Ne.symm h12] at hw
    obtain ⟨⟨e3, e4⟩, hm⟩ := hw
    rw [e3, e4]; exact hm
  · intro hm
    refine ⟨s a, ?_⟩
    have e1 : update s r₁ (s a) 0 = ∅ := by rw [upd0 h1]; exact h0
    rw [ev_cex _ _ e1 h2]
    refine ⟨s b, ?_⟩
    have e2 : update (update s r₁ (s a)) r₂ (s b) 0 = ∅ := by rw [upd0 h2]; exact e1
    rw [ev_cand _ _ e2, ev_cand _ _ e2, ev_ceqv _ _ e2 ha0 h10, ev_ceqv _ _ e2 hb0 h20, ev_mem]
    simp [update, ha1, ha2, hb1, hb2, h12, Ne.symm h12, hm]

lemma ev_atomL1 (a b : ℕ) {s : Assignment V} (h0 : s 0 = ∅) (ha : NotRes a) (hb : NotRes b) :
    ev (atomL 1 a b) s ↔ s a ∈ s b := by
  simp only [atomL, _root_.one_ne_zero, if_false]
  exact ev_atomL1' a b _ _ h0 (by simp [rlab]) (by simp [rlab]) (by simp [rlab]) (by simp [rlab])
    (by simp [rlab]) ha.1 hb.1 ha.2.1 ha.2.2 hb.2.1 hb.2.2

lemma xlab_ne_xlab {f d d' : ℕ} (h : d' ≠ d) : xlab f d' ≠ xlab f d := by
  simpa [xlab] using h

lemma ylab_ne_xlab (j f d : ℕ) : ylab j ≠ xlab f d := by simp [ylab, xlab]

lemma notRes_xlab0 (f d : ℕ) : NotRes (xlab f d) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [xlab, rlab]

lemma notRes_ylab0 (j : ℕ) : NotRes (ylab j) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [ylab, rlab]

/-- The environment invariant: bound labels are below the current depth. -/
def EnvOK {n : ℕ} (e d : ℕ) : Prop := ∀ i : Fin n, ∃ d' < d, e.[(i : ℕ)] = xlab 0 d'

lemma tlab_val {n : ℕ} (e : ℕ) (t : SyntacticSemiterm ℒₛₑₜ n) (s : Assignment V) :
    s (tlab e 0 t) = t.val (fun i => s (e.[(i : ℕ)])) (fun j => s (ylab j)) := by
  rcases t with i | j | ⟨f, _⟩
  · simp [tlab]
  · simp [tlab]
  · exact nomatch f

lemma tlab_notRes {n : ℕ} {e d : ℕ} (he : EnvOK (n := n) e d) (t : SyntacticSemiterm ℒₛₑₜ n) :
    NotRes (tlab e 0 t) := by
  rcases t with i | j | ⟨f, _⟩
  · obtain ⟨d', -, h⟩ := he i; simpa [tlab, h] using notRes_xlab0 0 d'
  · simpa [tlab] using notRes_ylab0 j
  · exact nomatch f

lemma env_step {n : ℕ} {e d : ℕ} (he : EnvOK (n := n) e d) :
    EnvOK (n := n + 1) (xlab 0 d ∷ e) (d + 1) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ⟨d, Nat.lt_succ_self d, by simp⟩
  · obtain ⟨d', hd', h⟩ := he j
    exact ⟨d', Nat.lt_succ_of_lt hd', by simpa using h⟩

lemma vec_step {n : ℕ} {e d : ℕ} (he : EnvOK (n := n) e d) (s : Assignment V) (v : V) :
    (fun i : Fin (n + 1) => update s (xlab 0 d) v ((xlab 0 d ∷ e).[(i : ℕ)])) =
      v :> fun i => s (e.[(i : ℕ)]) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [update]
  · obtain ⟨d', hd', h⟩ := he j
    have hne : e.[(j : ℕ)] ≠ xlab 0 d := by rw [h]; exact xlab_ne_xlab (Nat.ne_of_lt hd')
    simp [update, hne]

lemma f_step (s : Assignment V) (v : V) (d : ℕ) :
    (fun j => update s (xlab 0 d) v (ylab j)) = fun j => s (ylab j) := by
  funext j; simp [update, ylab_ne_xlab]

theorem ev_trX {n : ℕ} (φ : Semiproposition ℒₛₑₜ n) : ∀ (e d : ℕ) (s : Assignment V), s 0 = ∅ →
    EnvOK (n := n) e d →
    (ev (trX 0 0 e d φ).1 s ↔ φ.Eval (fun i => s (e.[(i : ℕ)])) (fun j => s (ylab j))) ∧
    (ev (trX 0 0 e d φ).2 s ↔ ¬φ.Eval (fun i => s (e.[(i : ℕ)])) (fun j => s (ylab j))) := by
  induction φ using Semiformula.rec' with
  | hverum =>
    intro e d s h0 _
    simp [trX, ev_cneg _ h0, ev_one, h0]
  | hfalsum =>
    intro e d s h0 _
    simp [trX, ev_cneg _ h0, ev_one, h0]
  | hrel R v =>
    intro e d s h0 he
    rename_i k
    match k, R with
    | 2, .eq =>
      have key : ev (atomX e 0 (Language.Set.Rel.eq : (ℒₛₑₜ).Rel 2) v) s ↔
          (Semiformula.rel Language.Set.Rel.eq v).Eval (fun i => s (e.[(i : ℕ)])) (fun j => s (ylab j)) := by
        simp only [atomX, atomL, if_true]
        rw [ev_ceqv _ _ h0 (tlab_notRes he _).1 (tlab_notRes he _).1, tlab_val e (v 0) s, tlab_val e (v 1) s]
        simp [Semiformula.eval_rel]; rfl
      simp only [trX]
      exact ⟨key, by rw [ev_cneg _ h0, key]⟩
    | 2, .mem =>
      have key : ev (atomX e 0 (Language.Set.Rel.mem : (ℒₛₑₜ).Rel 2) v) s ↔
          (Semiformula.rel Language.Set.Rel.mem v).Eval (fun i => s (e.[(i : ℕ)])) (fun j => s (ylab j)) := by
        simp only [atomX]
        rw [ev_atomL1 _ _ h0 (tlab_notRes he _) (tlab_notRes he _), tlab_val e (v 0) s, tlab_val e (v 1) s]
        simp [Semiformula.eval_rel]; rfl
      simp only [trX]
      exact ⟨key, by rw [ev_cneg _ h0, key]⟩
  | hnrel R v =>
    intro e d s h0 he
    rename_i k
    match k, R with
    | 2, .eq =>
      have key : ev (atomX e 0 (Language.Set.Rel.eq : (ℒₛₑₜ).Rel 2) v) s ↔
          (Semiformula.rel Language.Set.Rel.eq v).Eval (fun i => s (e.[(i : ℕ)])) (fun j => s (ylab j)) := by
        simp only [atomX, atomL, if_true]
        rw [ev_ceqv _ _ h0 (tlab_notRes he _).1 (tlab_notRes he _).1, tlab_val e (v 0) s, tlab_val e (v 1) s]
        simp [Semiformula.eval_rel]; rfl
      simp only [trX, Semiformula.eval_nrel]
      refine ⟨by rw [ev_cneg _ h0, key]; simp [Semiformula.eval_rel], by rw [key]; simp [Semiformula.eval_rel]⟩
    | 2, .mem =>
      have key : ev (atomX e 0 (Language.Set.Rel.mem : (ℒₛₑₜ).Rel 2) v) s ↔
          (Semiformula.rel Language.Set.Rel.mem v).Eval (fun i => s (e.[(i : ℕ)])) (fun j => s (ylab j)) := by
        simp only [atomX]
        rw [ev_atomL1 _ _ h0 (tlab_notRes he _) (tlab_notRes he _), tlab_val e (v 0) s, tlab_val e (v 1) s]
        simp [Semiformula.eval_rel]; rfl
      simp only [trX, Semiformula.eval_nrel]
      refine ⟨by rw [ev_cneg _ h0, key]; simp [Semiformula.eval_rel], by rw [key]; simp [Semiformula.eval_rel]⟩
  | hand p q ihp ihq =>
    intro e d s h0 he
    have hp := ihp e d s h0 he; have hq := ihq e d s h0 he
    simp only [trX, ev_cneg _ h0, ev_cand _ _ h0, hp.1, hq.1, LogicalConnective.HomClass.map_and,
      LogicalConnective.Prop.and_eq]
    constructor <;> tauto
  | hor p q ihp ihq =>
    intro e d s h0 he
    have hp := ihp e d s h0 he; have hq := ihq e d s h0 he
    simp only [trX, ev_cneg _ h0, ev_cand _ _ h0, hp.2, hq.2, LogicalConnective.HomClass.map_or,
      LogicalConnective.Prop.or_eq]
    constructor <;> tauto
  | hall p ih =>
    intro e d s h0 he
    have hv : ∀ v : V, update s (xlab 0 d) v 0 = ∅ := fun v => by rw [upd0 (xlab_ne_zero 0 d)]; exact h0
    have IH := fun v : V => ih (xlab 0 d ∷ e) (d + 1) (update s (xlab 0 d) v) (hv v) (env_step he)
    simp only [vec_step he, f_step] at IH
    have key : ev (ZF209.Internal.all (xlab 0 d) (trX 0 0 (xlab 0 d ∷ e) (d + 1) p).1) s ↔
        (∀¹ p).Eval (fun i => s (e.[(i : ℕ)])) (fun j => s (ylab j)) := by
      rw [ev_all, Semiformula.eval_all]
      exact forall_congr' fun v => (IH v).1
    simp only [trX]
    exact ⟨key, by rw [ev_cneg _ h0, key]⟩
  | hexs p ih =>
    intro e d s h0 he
    have hv : ∀ v : V, update s (xlab 0 d) v 0 = ∅ := fun v => by rw [upd0 (xlab_ne_zero 0 d)]; exact h0
    have IH := fun v : V => ih (xlab 0 d ∷ e) (d + 1) (update s (xlab 0 d) v) (hv v) (env_step he)
    simp only [vec_step he, f_step] at IH
    have key : ev (ZF209.Internal.all (xlab 0 d) (trX 0 0 (xlab 0 d ∷ e) (d + 1) p).2) s ↔
        ¬(∃¹ p).Eval (fun i => s (e.[(i : ℕ)])) (fun j => s (ylab j)) := by
      rw [ev_all, Semiformula.eval_ex]
      simp only [fun v : V => (IH v).2]
      push Not; rfl
    simp only [trX]
    exact ⟨by rw [ev_cneg _ h0, key]; tauto, key⟩

end ZFEval

end ZF209.Halting
