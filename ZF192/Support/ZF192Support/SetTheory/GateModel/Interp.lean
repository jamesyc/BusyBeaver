module
public import Foundation.FirstOrder.SetTheory.Basic.Model
@[expose] public section
/-! # Pulling definable predicates back along an interpretation

An interpretation of a set structure `N` in `M` consists of a definable domain,
a map onto `N`, and definable relations on `M` that read membership and equality
of `N`. Every predicate definable over `N` then pulls back to a definable
predicate over `M`. -/
namespace ZF192Support.GateModel
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

/-- An interpretation of `N` in `M`. -/
structure Interp (M N : Type*) [SetStructure M] [SetStructure N] where
  dom : M → Prop
  π : M → N
  surj : ∀ y : N, ∃ x, dom x ∧ π x = y
  mem : M → M → Prop
  mem_iff : ∀ x y, dom x → dom y → (mem x y ↔ π x ∈ π y)
  eq : M → M → Prop
  eq_iff : ∀ x y, dom x → dom y → (eq x y ↔ π x = π y)
  dom_def : ℒₛₑₜ-predicate dom
  mem_def : ℒₛₑₜ-relation mem
  eq_def : ℒₛₑₜ-relation eq

/-- Formulas over `M` with free variables in `ℕ` define predicates with parameters. -/
lemma definable_eval {M : Type*} [SetStructure M] {k : ℕ}
    (φ : Semiformula ℒₛₑₜ ℕ k) (f : ℕ → M) :
    Language.Definable ℒₛₑₜ (fun v : Fin k → M => φ.Eval v f) :=
  ⟨⟨Rew.rewriteMap f ▹ φ, fun v => by simp [Semiformula.eval_rewriteMap]⟩⟩

namespace Interp
variable {M N : Type*} [SetStructure M] [SetStructure N] (I : Interp M N)

/-- A chosen preimage in the domain. -/
noncomputable def pre (y : N) : M := Classical.choose (I.surj y)

lemma pre_dom (y : N) : I.dom (I.pre y) := (Classical.choose_spec (I.surj y)).1

lemma π_pre (y : N) : I.π (I.pre y) = y := (Classical.choose_spec (I.surj y)).2

/-- Terms of `N` read in `M`. -/
noncomputable def tm {k : ℕ} : Semiterm ℒₛₑₜ N k → (Fin k → M) → M
  | .bvar i, v => v i
  | .fvar y, _ => I.pre y
  | .func f _, _ => Empty.elim f

lemma tm_dom {k : ℕ} (t : Semiterm ℒₛₑₜ N k) {v : Fin k → M} (hv : ∀ i, I.dom (v i)) :
    I.dom (I.tm t v) := by
  cases t with
  | bvar i => exact hv i
  | fvar y => exact I.pre_dom y
  | func f _ => exact Empty.elim f

lemma π_tm {k : ℕ} (t : Semiterm ℒₛₑₜ N k) (v : Fin k → M) :
    I.π (I.tm t v) = t.val (I.π ∘ v) id := by
  cases t with
  | bvar i => rfl
  | fvar y => exact I.π_pre y
  | func f _ => exact Empty.elim f

lemma definable_tm₂ {k : ℕ} (R : M → M → Prop) (hR : ℒₛₑₜ-relation R)
    (t₀ t₁ : Semiterm ℒₛₑₜ N k) :
    Language.Definable ℒₛₑₜ (fun v : Fin k → M => R (I.tm t₀ v) (I.tm t₁ v)) := by
  cases t₀ with
  | func f _ => exact Empty.elim f
  | bvar i =>
    cases t₁ with
    | func f _ => exact Empty.elim f
    | bvar j => simp only [tm]; definability
    | fvar y => simp only [tm]; definability
  | fvar x =>
    cases t₁ with
    | func f _ => exact Empty.elim f
    | bvar j => simp only [tm]; definability
    | fvar y => simp only [tm]; definability

lemma definable_dom (k : ℕ) : Language.Definable ℒₛₑₜ (fun v : Fin k → M => ∀ i, I.dom (v i)) := by
  have := I.dom_def
  exact Language.Definable.fintype_all fun i => by definability

omit [SetStructure M] in
lemma cons_succ {k : ℕ} (w : Fin (k + 1) → M) : (w 0 :> fun i => w i.succ) = w := by
  funext i; cases i using Fin.cases <;> rfl

lemma comp_cons {k : ℕ} (x : M) (v : Fin k → M) : I.π ∘ (x :> v) = I.π x :> (I.π ∘ v) := by
  funext i; cases i using Fin.cases <;> rfl

/-- The pullback of any formula over `N` is definable over `M`. -/
theorem pullback {k : ℕ} (φ : Semiformula ℒₛₑₜ N k) :
    Language.Definable ℒₛₑₜ (fun v : Fin k → M => (∀ i, I.dom (v i)) ∧ φ.Eval (I.π ∘ v) id) := by
  induction φ using Semiformula.rec' with
  | hverum => exact Language.Definable.of_iff (I.definable_dom _) fun v => by simp
  | hfalsum => exact Language.Definable.of_iff (Language.Definable.const False) fun v => by simp
  | hrel r ts =>
    cases r with
    | eq =>
      refine Language.Definable.of_iff
        ((I.definable_dom _).and (I.definable_tm₂ I.eq I.eq_def (ts 0) (ts 1))) fun v => ?_
      change (_ ∧ (ts 0).val (I.π ∘ v) id = (ts 1).val (I.π ∘ v) id) ↔ _
      exact ⟨fun ⟨hv, h⟩ => ⟨hv, (I.eq_iff _ _ (I.tm_dom _ hv) (I.tm_dom _ hv)).mpr
          (by rw [I.π_tm, I.π_tm]; exact h)⟩,
        fun ⟨hv, h⟩ => ⟨hv, by
          rw [← I.π_tm, ← I.π_tm]
          exact (I.eq_iff _ _ (I.tm_dom _ hv) (I.tm_dom _ hv)).mp h⟩⟩
    | mem =>
      refine Language.Definable.of_iff
        ((I.definable_dom _).and (I.definable_tm₂ I.mem I.mem_def (ts 0) (ts 1))) fun v => ?_
      change (_ ∧ (ts 0).val (I.π ∘ v) id ∈ (ts 1).val (I.π ∘ v) id) ↔ _
      exact ⟨fun ⟨hv, h⟩ => ⟨hv, (I.mem_iff _ _ (I.tm_dom _ hv) (I.tm_dom _ hv)).mpr
          (by rw [I.π_tm, I.π_tm]; exact h)⟩,
        fun ⟨hv, h⟩ => ⟨hv, by
          rw [← I.π_tm, ← I.π_tm]
          exact (I.mem_iff _ _ (I.tm_dom _ hv) (I.tm_dom _ hv)).mp h⟩⟩
  | hnrel r ts =>
    cases r with
    | eq =>
      refine Language.Definable.of_iff
        ((I.definable_dom _).and (I.definable_tm₂ I.eq I.eq_def (ts 0) (ts 1)).not) fun v => ?_
      change (_ ∧ ¬(ts 0).val (I.π ∘ v) id = (ts 1).val (I.π ∘ v) id) ↔ _
      exact ⟨fun ⟨hv, h⟩ => ⟨hv, fun h' => h (by
          rw [← I.π_tm, ← I.π_tm]
          exact (I.eq_iff _ _ (I.tm_dom _ hv) (I.tm_dom _ hv)).mp h')⟩,
        fun ⟨hv, h⟩ => ⟨hv, fun h' => h
          ((I.eq_iff _ _ (I.tm_dom _ hv) (I.tm_dom _ hv)).mpr (by rw [I.π_tm, I.π_tm]; exact h'))⟩⟩
    | mem =>
      refine Language.Definable.of_iff
        ((I.definable_dom _).and (I.definable_tm₂ I.mem I.mem_def (ts 0) (ts 1)).not) fun v => ?_
      change (_ ∧ ¬(ts 0).val (I.π ∘ v) id ∈ (ts 1).val (I.π ∘ v) id) ↔ _
      exact ⟨fun ⟨hv, h⟩ => ⟨hv, fun h' => h (by
          rw [← I.π_tm, ← I.π_tm]
          exact (I.mem_iff _ _ (I.tm_dom _ hv) (I.tm_dom _ hv)).mp h')⟩,
        fun ⟨hv, h⟩ => ⟨hv, fun h' => h
          ((I.mem_iff _ _ (I.tm_dom _ hv) (I.tm_dom _ hv)).mpr (by rw [I.π_tm, I.π_tm]; exact h'))⟩⟩
  | hand φ ψ ihφ ihψ =>
    exact Language.Definable.of_iff (ihφ.and ihψ) fun v => by simp; tauto
  | hor φ ψ ihφ ihψ =>
    exact Language.Definable.of_iff (ihφ.or ihψ) fun v => by simp; tauto
  | hall φ ih =>
    have hd := I.dom_def
    have h₁ : Language.Definable ℒₛₑₜ (fun w : Fin (_ + 1) → M =>
        I.dom (w 0) → (∀ i, I.dom (w i)) ∧ φ.Eval (I.π ∘ w) id) :=
      (show Language.Definable ℒₛₑₜ (fun w : Fin (_ + 1) → M => I.dom (w 0)) by definability).imp ih
    have h₂ := (I.definable_dom _).and (Language.Definable.all (R := fun v x =>
      I.dom x → (∀ i, I.dom ((x :> v) i)) ∧ φ.Eval (I.π ∘ (x :> v)) id)
      (Language.Definable.of_iff h₁ fun w => by simp only [cons_succ]))
    refine Language.Definable.of_iff h₂ fun v => ?_
    simp only [Semiformula.eval_all]
    constructor
    · rintro ⟨hv, h⟩
      refine ⟨hv, fun x hx => ⟨fun i => ?_, ?_⟩⟩
      · cases i using Fin.cases
        · exact hx
        · exact hv _
      · rw [I.comp_cons]; exact h _
    · rintro ⟨hv, h⟩
      refine ⟨hv, fun y => ?_⟩
      have := (h (I.pre y) (I.pre_dom y)).2
      rwa [I.comp_cons, I.π_pre] at this
  | hexs φ ih =>
    have hd := I.dom_def
    have h₁ : Language.Definable ℒₛₑₜ (fun w : Fin (_ + 1) → M =>
        I.dom (w 0) ∧ (∀ i, I.dom (w i)) ∧ φ.Eval (I.π ∘ w) id) :=
      (show Language.Definable ℒₛₑₜ (fun w : Fin (_ + 1) → M => I.dom (w 0)) by definability).and ih
    have h₂ := (I.definable_dom _).and (Language.Definable.exs (R := fun v x =>
      I.dom x ∧ (∀ i, I.dom ((x :> v) i)) ∧ φ.Eval (I.π ∘ (x :> v)) id)
      (Language.Definable.of_iff h₁ fun w => by simp only [cons_succ]))
    refine Language.Definable.of_iff h₂ fun v => ?_
    simp only [Semiformula.eval_ex]
    constructor
    · rintro ⟨hv, y, h⟩
      refine ⟨hv, I.pre y, I.pre_dom y, fun i => ?_, ?_⟩
      · cases i using Fin.cases
        · exact I.pre_dom y
        · exact hv _
      · rw [I.comp_cons, I.π_pre]; exact h
    · rintro ⟨hv, x, hx, -, h⟩
      exact ⟨hv, I.π x, by rwa [I.comp_cons] at h⟩

/-- Definable predicates on `N` pull back to definable predicates on `M`. -/
theorem pullback_pred {P : N → Prop} (hP : ℒₛₑₜ-predicate P) :
    ℒₛₑₜ-predicate (fun x : M => I.dom x ∧ P (I.π x)) := by
  obtain ⟨φ, hφ⟩ := hP.definable
  refine Language.Definable.of_iff (I.pullback φ) fun v => ?_
  rw [hφ (I.π ∘ v)]
  exact ⟨fun ⟨h, hp⟩ => ⟨fun i => by rw [Subsingleton.elim i 0]; exact h, hp⟩,
    fun ⟨h, hp⟩ => ⟨h 0, hp⟩⟩

/-- Definable relations on `N` pull back to definable relations on `M`. -/
theorem pullback_rel {R : N → N → Prop} (hR : ℒₛₑₜ-relation R) :
    ℒₛₑₜ-relation (fun x y : M => I.dom x ∧ I.dom y ∧ R (I.π x) (I.π y)) := by
  obtain ⟨φ, hφ⟩ := hR.definable
  refine Language.Definable.of_iff (I.pullback φ) fun v => ?_
  rw [hφ (I.π ∘ v)]
  constructor
  · rintro ⟨h0, h1, hr⟩
    refine ⟨fun i => ?_, hr⟩
    cases i using Fin.cases with
    | zero => exact h0
    | succ j => rw [Subsingleton.elim j 0]; exact h1
  · rintro ⟨h, hr⟩
    exact ⟨h 0, h 1, hr⟩

end Interp

end ZF192Support.GateModel
