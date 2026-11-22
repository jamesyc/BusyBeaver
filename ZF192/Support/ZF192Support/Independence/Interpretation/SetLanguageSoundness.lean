module
public import ZF192Support.Calculus.Internal.StandardTrace
public import ZF192Support.Calculus.Internal.Quote
public import Foundation.FirstOrder.SetTheory.BST.BST
public import Foundation.FirstOrder.SetTheory.ZF.Model

@[expose] public section
/-! # Truth of the set-language translation in ZF models -/
namespace ZF192Support.Halting
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.FirstOrder.SetTheory
open ZFR.ArithmeticRepresentation CCodeSoundness

/-! ## Evaluating codes -/

section Eval
variable {α : Type*} (mem : α → α → Prop) (s : Assignment α)

lemma mem_nat (a b : ℕ) : ZF192Support.Internal.mem a b = memCode a b := by
  have := congrArg (fun K : CKernel.Generic.Codes ℕ => K.mem a b) ZF192Support.Internal.codes_nat
  simpa [ZF192Support.Internal.codes, CKernel.natCodes] using this

lemma ev_imp (a b : ℕ) :
    evalCode mem (ZF192Support.Internal.imp a b) s ↔ (evalCode mem a s → evalCode mem b s) := by
  rw [imp_nat, show impCode a b = (Formula.imp (decode a) (decode b)).code by
    simp [impCode, Formula.code, decode_code], evalCode_of_formula]
  rfl

lemma ev_all (x a : ℕ) :
    evalCode mem (ZF192Support.Internal.all x a) s ↔ ∀ v, evalCode mem a (update s x v) := by
  rw [all_nat, show allCode x a = (Formula.all x (decode a)).code by
    simp [allCode, Formula.code, decode_code], evalCode_of_formula]
  rfl

lemma ev_mem (a b : ℕ) : evalCode mem (ZF192Support.Internal.mem a b) s ↔ mem (s a) (s b) := by
  rw [mem_nat, show memCode a b = (Formula.mem a b).code by simp [memCode, Formula.code],
    evalCode_of_formula]
  rfl

lemma ev_one : evalCode mem 1 s ↔ mem (s 0) (s 0) := by
  have : (1 : ℕ) = ZF192Support.Internal.mem 0 0 := by rw [mem_nat]; rfl
  rw [this, ev_mem]

end Eval

/-! ## Derived connectives and atoms in models of ZF -/

section ZFEval
open ZF192Support.Internal.Tait
variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local notation "ev" => evalCode (fun a b : V => a ∈ b)

lemma upd0 {s : Assignment V} {x : ℕ} (hx : x ≠ 0) (v : V) : update s x v 0 = s 0 := by
  simp [update, Ne.symm hx]

lemma ev_cneg (A : ℕ) {s : Assignment V} (h0 : s 0 = ∅) :
    ev (ZF192Support.Internal.cneg A) s ↔ ¬ev A s := by
  simp [ZF192Support.Internal.cneg, ev_imp, ev_one, h0]

lemma ev_cand (A B : ℕ) {s : Assignment V} (h0 : s 0 = ∅) :
    ev (ZF192Support.Internal.cand A B) s ↔ ev A s ∧ ev B s := by
  simp only [ZF192Support.Internal.cand, ev_cneg _ h0, ev_imp]; tauto

lemma ev_ciff (A B : ℕ) {s : Assignment V} (h0 : s 0 = ∅) :
    ev (ZF192Support.Internal.ciff A B) s ↔ (ev A s ↔ ev B s) := by
  simp only [ZF192Support.Internal.ciff, ev_cand _ _ h0, ev_imp]; tauto

lemma ev_cex (x A : ℕ) {s : Assignment V} (h0 : s 0 = ∅) (hx : x ≠ 0) :
    ev (ZF192Support.Internal.cex x A) s ↔ ∃ v, ev A (update s x v) := by
  simp only [ZF192Support.Internal.cex, ev_cneg _ h0, ev_all]
  simp only [fun v => ev_cneg A (s := update s x v) (by rw [upd0 hx]; exact h0)]
  push Not; rfl

lemma ev_ciff_upd (A B x : ℕ) (v : V) {s : Assignment V} (h0 : s 0 = ∅) (hx : x ≠ 0) :
    ev (ZF192Support.Internal.ciff A B) (update s x v) ↔
      (ev A (update s x v) ↔ ev B (update s x v)) :=
  ev_ciff A B (by rw [upd0 hx]; exact h0)

lemma ev_cand_upd (A B x : ℕ) (v : V) {s : Assignment V} (h0 : s 0 = ∅) (hx : x ≠ 0) :
    ev (ZF192Support.Internal.cand A B) (update s x v) ↔ ev A (update s x v) ∧ ev B (update s x v) :=
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
    ev (ZF192Support.Internal.cex r₁ (ZF192Support.Internal.cex r₂ (ZF192Support.Internal.cand
      (ZF192Support.Internal.cand (ceqv a r₁) (ceqv b r₂)) (ZF192Support.Internal.mem r₁ r₂)))) s ↔ s a ∈ s b := by
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
    have key : ev (ZF192Support.Internal.all (xlab 0 d) (trX 0 0 (xlab 0 d ∷ e) (d + 1) p).1) s ↔
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
    have key : ev (ZF192Support.Internal.all (xlab 0 d) (trX 0 0 (xlab 0 d ∷ e) (d + 1) p).2) s ↔
        ¬(∃¹ p).Eval (fun i => s (e.[(i : ℕ)])) (fun j => s (ylab j)) := by
      rw [ev_all, Semiformula.eval_ex]
      simp only [fun v : V => (IH v).2]
      push Not; rfl
    simp only [trX]
    exact ⟨by rw [ev_cneg _ h0, key]; tauto, key⟩

end ZFEval

end ZF192Support.Halting
