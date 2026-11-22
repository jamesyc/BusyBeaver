module

public import Foundation.FirstOrder.LK.Completeness.CounterModel
public import Foundation.Vorspiel.ExistsUnique
@[expose] public section
set_option autoImplicit true
/-!
# (Direct) Interpretation
-/

namespace FFL.FirstOrder

@[ext]
structure DirectTranslation {L₁ : Language} [L₁.Eq] (T : Theory L₁) [𝗘𝗤 _ ⪯ T] (L₂ : Language)
    [L₂.Eq] where
  domain : Semiformula.Operator L₁ 1
  rel {k} : L₂.Rel k → Semiformula.Operator L₁ k
  func {k} : L₂.Func k → Semiformula.Operator L₁ (k + 1)
  domain_nonempty :
    T ⊢ “∃ x, %domain x”
  func_defined {k} (f : L₂.Func k) :
    T ⊢ ∀¹* “(⋀ i, %domain #(i : Fin k)) → ∃! y, %domain y ∧ %(func f) y ⋯”
  preserve_eq :
    T ⊢ “∀ x y, %domain x → %domain y → (%(rel Language.Eq.eq) x y ↔ x = y)”

namespace DirectTranslation

variable {L₁ L₂ : Language} [L₁.Eq] [L₂.Eq] {T : Theory L₁} [𝗘𝗤 _ ⪯ T]

variable (π : DirectTranslation T L₂)

def fal (φ : Semiformula L₁ ξ (n + 1)) : Semiformula L₁ ξ n := ∀¹[π.domain.operator ![#0]] φ

def exs (φ : Semiformula L₁ ξ (n + 1)) : Semiformula L₁ ξ n := ∃¹[π.domain.operator ![#0]] φ

notation:64 "∀_[" π "] " ψ => fal π ψ
notation:64 "∃_[" π "] " ψ => exs π ψ

@[simp] lemma neg_fal (φ : Semiformula L₁ ξ (n + 1)) : ∼(∀_[π] φ) = ∃_[π] ∼φ := by simp [fal, exs]

@[simp] lemma neg_exs (φ : Semiformula L₁ ξ (n + 1)) : ∼(∃_[π] φ) = ∀_[π] ∼φ := by simp [fal, exs]

def varEqual : Semiterm L₂ ξ n → Semiformula L₁ ξ (n + 1)
  |                     #x => “z. z = #x.succ”
  |                     &x => “z. z = &x”
  | .func (arity := k) f v =>
    ∀¹^[k] (
      (Matrix.conj fun i ↦
        π.domain.operator ![#(i.addCast (n + 1))] ⋏
        Rew.subst (#(i.addCast (n + 1)) :> fun j ↦ #((j.addNat 1).addNat k)) ▹ varEqual (v i))
      🡒 (π.func f).operator
        (#((0 : Fin (n + 1)).addNat k) :> fun i ↦ #(i.addCast (n + 1)))
    )

def translateRel {k} (r : L₂.Rel k) (v : Fin k → Semiterm L₂ ξ n) : Semiformula L₁ ξ n :=
  ∀¹^[k] (
    (Matrix.conj fun i ↦
      π.domain.operator ![#(i.addCast n)] ⋏
      Rew.subst (#(i.addCast n) :> fun j ↦ #(j.addNat k)) ▹ π.varEqual (v i))
    🡒 (π.rel r).operator (fun i ↦ #(i.addCast n))
  )

def translateAux {n} : Semiformula L₂ ξ n → Semiformula L₁ ξ n
  | .rel r v  => π.translateRel r v
  | .nrel r v => ∼π.translateRel r v
  |         ⊤ => ⊤
  |         ⊥ => ⊥
  |     φ ⋏ ψ => translateAux φ ⋏ translateAux ψ
  |     φ ⋎ ψ => translateAux φ ⋎ translateAux ψ
  |      ∀¹ φ => ∀_[π] translateAux φ
  |      ∃¹ φ => ∃_[π] translateAux φ

lemma translateAux_neg {n : ℕ} (φ : Semiformula L₂ ξ n) :
    π.translateAux (∼φ) = ∼π.translateAux φ := by
  induction φ using Semiformula.rec' <;> simp [translateAux, *]

def translate : Semiformula L₂ ξ n →ˡᶜ Semiformula L₁ ξ n where
  toTr := π.translateAux
  map_top' := rfl
  map_bot' := rfl
  map_and' := fun _ _ ↦ rfl
  map_or' := fun _ _ ↦ rfl
  map_neg' := by simp [translateAux_neg]
  map_imply' := by simp [Semiformula.imp_eq, translateAux, translateAux_neg, ←Semiformula.neg_eq]

variable {π}

lemma translate_rel {k} (R : L₂.Rel k) (v : Fin k → Semiterm L₂ ξ n) :
    π.translate (Semiformula.rel R v) = π.translateRel R v := rfl

lemma translate_nrel {k} (R : L₂.Rel k) (v : Fin k → Semiterm L₂ ξ n) :
    π.translate (Semiformula.nrel R v) = ∼π.translateRel R v := rfl

lemma translate_all (φ : Semiformula L₂ ξ (n + 1)) :
    π.translate (∀¹ φ) = ∀_[π] π.translate φ := rfl

lemma translate_ex (φ : Semiformula L₂ ξ (n + 1)) :
    π.translate (∃¹ φ) = ∃_[π] π.translate φ := rfl

section semantics

open Semiformula

variable {M : Type*} [Tarski.Structure L₁ M]

variable (π)

def Dom (x : M) : Prop := π.domain.val ![x]

variable {π}

lemma dom_iff {x : M} : π.Dom x ↔ π.domain.val ![x] := iff_of_eq rfl

lemma domain_exists [Nonempty M] [M↓[L₁] ⊧* T] : ∃ x : M, π.Dom x := by
  simpa [models_iff] using! models_of_provable (M := M) inferInstance π.domain_nonempty

variable (π M)

@[pp_using_anonymous_constructor, ext]
structure Model where
  val : M
  dom : π.Dom val

variable {π M}

attribute [coe] Model.val

instance : CoeOut (π.Model M) M := ⟨Model.val⟩

namespace Model

@[simp] lemma pval_sub_domain (x : π.Model M) : π.domain.val ![(x : M)] := x.dom

instance [Nonempty M] [M↓[L₁] ⊧* T] : Nonempty (π.Model M) := by
  rcases π.domain_exists (M := M) with ⟨x, hx⟩; exact ⟨⟨x, hx⟩⟩

@[simp] lemma coe_mem_domain (x : π.Model M) : π.Dom (x : M) := x.dom

@[simp] lemma val_mk (x : M) (hx : π.Dom x) : ↑(⟨x, hx⟩ : π.Model M) = x := rfl

@[simp] lemma eta (x : π.Model M) (h : π.Dom (x : M)) : (⟨(x : M), h⟩ : π.Model M) = x := rfl

@[simp] lemma val_inj_iff {x y : π.Model M} : x.val = y.val ↔ x = y :=
  ⟨fun h ↦ by ext; exact h, by rintro rfl; rfl⟩

@[simp] lemma val_mk_eq_iff {x y : M} {hx : π.Dom x} {hy : π.Dom y} :
    (⟨x, hx⟩ : π.Model M) = (⟨y, hy⟩ : π.Model M) ↔ x = y := by simp

lemma forall_iff {P : π.Model M → Prop} :
    (∀ x, P x) ↔ ∀ x hx, P ⟨x, hx⟩ :=
  ⟨fun h x hx ↦ h ⟨x, hx⟩, fun h ⟨x, hx⟩ ↦ h x hx⟩

lemma exists_iff {P : π.Model M → Prop} :
    (∃ x, P x) ↔ ∃ x hx, P ⟨x, hx⟩ :=
  ⟨fun ⟨⟨x, hx⟩, h⟩ ↦ ⟨x, hx, h⟩, fun ⟨x, hx, h⟩ ↦ ⟨⟨x, hx⟩, h⟩⟩

@[simp] lemma eval_fal {φ : Semiformula L₁ ξ (n + 1)} :
    Semiformula.Eval (M := M) e ε (∀_[π] φ) ↔
      ∀ x : π.Model M, Semiformula.Eval (M := M) (x :> e) ε φ := by
  simp [fal, forall_iff, Dom]

@[simp] lemma eval_exs {φ : Semiformula L₁ ξ (n + 1)} :
    Semiformula.Eval (M := M) e ε (∃_[π] φ) ↔
      ∃ x : π.Model M, Semiformula.Eval (M := M) (x :> e) ε φ := by
  simp [exs, exists_iff, Dom]

variable [Nonempty M] [M↓[L₁] ⊧* T] [Tarski.Structure.Eq L₁ M]

lemma func_existsUnique_on_dom {k} (f : L₂.Func k) :
    ∀ (v : Fin k → M), (∀ i, π.Dom (v i)) → ∃! y, π.Dom y ∧ (π.func f).val (y :> v) := by
  simpa [Dom, models_iff, Function.comp_def, Matrix.constant_eq_singleton] using
    models_of_provable (M := M) inferInstance (π.func_defined f)

lemma func_existsUnique {k} (f : L₂.Func k) (v : Fin k → π.Model M) :
    ∃! y : π.Model M, (π.func f).val ((y : M) :> fun i ↦ (v i : M)) := by
  have : ∃! y, π.Dom y ∧ (π.func f).val (y :> fun i ↦ (v i : M)) :=
    func_existsUnique_on_dom (π := π) f (fun i ↦ (v i : M)) (fun i ↦ by simp)
  rcases this.exists with ⟨y, hy, Hy⟩
  exact ExistsUnique.intro ⟨y, hy⟩ (by simpa using Hy)
    fun z Hz ↦ by
      rcases show y = ↑z from this.unique ⟨hy, Hy⟩ ⟨z.dom, Hz⟩
      simp

variable (π M)

noncomputable instance struc : Tarski.Structure L₂ (π.Model M) where
  rel _ R v := (π.rel R).val fun i ↦ (v i : M)
  func _ f v := Classical.choose! (func_existsUnique (π := π) f v)

variable {π M}

lemma rel_iff {k} (r : L₂.Rel k) (v : Fin k → π.Model M) :
    Tarski.Structure.rel r v ↔ (π.rel r).val (fun i ↦ (v i : M)) := iff_of_eq rfl

@[simp] lemma eq_iff' {a b : π.Model M} :
    (π.rel Language.Eq.eq).val ![(a : M), (b : M)] ↔ a = b := by
  have : M↓[L₁] ⊧* T := inferInstance
  have : ∀ x y : M, π.Dom x → π.Dom y → ((π.rel Language.Eq.eq).val ![x, y] ↔ x = y) := by
    simpa [models_iff, Matrix.comp_vecCons', Matrix.constant_eq_singleton, ←dom_iff]
      using models_of_provable this π.preserve_eq
  simpa using this a b

@[simp] lemma eq_iff (v : Fin 2 → π.Model M) :
    Tarski.Structure.rel (Language.Eq.eq : L₂.Rel 2) v ↔ v 0 = v 1 := by
  simp [Model.rel_iff]
  simp [Matrix.fun_eq_vec_two (v := fun i ↦ (v i : M))]

instance : Tarski.Structure.Eq L₂ (π.Model M) where
  eq a b := by simp [Operator.val, Operator.Eq.sentence_eq, eval_rel]

lemma func_iff {k} {f : L₂.Func k} {y : π.Model M} {v : Fin k → π.Model M} :
    y = Tarski.Structure.func f v ↔ (π.func f).val (↑y :> fun i ↦ (v i : M)) :=
  Classical.choose!_eq_iff_right _

lemma func_iff' {k} {f : L₂.Func k} {y : M} {v : Fin k → π.Model M} :
    y = Tarski.Structure.func f v ↔ π.Dom y ∧ (π.func f).val (y :> fun i ↦ (v i : M)) := by
  constructor
  · rintro rfl; simp [←func_iff]
  · intro h
    exact (func_existsUnique_on_dom f (fun i ↦ (v i : M)) (by simp)).unique h (by simp [←func_iff])

@[simp] lemma eval_func {k} (f : L₂.Func k) (v : Fin k → π.Model M) :
    (π.func f).val (↑(Tarski.Structure.func f v) :> fun i ↦ (v i : M)) := by simp [←func_iff]

lemma eval_varEqual_iff {t : Semiterm L₂ ξ n} {ε : ξ → π.Model M} {y : π.Model M}
    {x : Fin n → π.Model M} :
    Semiformula.Eval (M := M) (y :> fun i ↦ x i) (fun x ↦ ε x) (π.varEqual t) ↔
      y = t.val (M := π.Model M) x ε := by
  match t with
  |                     #_ => simp [varEqual]
  |                     &_ => simp [varEqual]
  | .func (arity := k) f v =>
    suffices
        (∀ w : Fin k → M,
          (∀ i, π.Dom (w i) ∧
            Semiformula.Eval (M := M) (w i :> fun i ↦ x i) (fun x ↦ ε x) (π.varEqual (v i))) →
            (π.func f).val ((y : M) :> w)) ↔
      (π.func f).val ((y : M) :> fun i ↦ ((v i).val (M := π.Model M) x ε : M)) by
        simpa [varEqual, Matrix.comp_vecCons', Matrix.constant_eq_singleton,
          Semiterm.val_func, Semiterm.val_rew, func_iff, ←dom_iff, Function.comp_def]
    constructor
    · intro h; apply h
      intro i
      simp [eval_varEqual_iff (t := v i)]
    · intro h w hw
      suffices w = fun i ↦ ↑((v i).val (M := π.Model M) x ε) by rcases this; exact h
      ext i
      let w' : π.Model M := ⟨w i, (hw i).1⟩
      have : Semiformula.Eval (M := M) (w' :> fun i ↦ x i) (fun x ↦ ε x) (π.varEqual (v i)) := by
        simp [w', hw]
      simpa [w'] using congr_arg Model.val (eval_varEqual_iff.mp this)

lemma eval_translateRel_iff {n k} {ε : ξ → π.Model M} (e : Fin n → π.Model M) (R : L₂.Rel k)
    (v : Fin k → Semiterm L₂ ξ n) :
    Semiformula.Eval (M := M) (fun i ↦ e i) (fun i ↦ ε i) (π.translateRel R v) ↔
      Tarski.Structure.rel R fun i ↦ (v i).val (M := π.Model M) e ε := by
  suffices
    (∀ w, (∀ i, π.Dom (w i) ∧
        Semiformula.Eval (M := M) (w i :> fun i ↦ ↑(e i)) (fun i ↦ ↑(ε i)) (π.varEqual (v i))) →
      (π.rel R).val w) ↔
    (π.rel R).val (fun i ↦ ((v i).val (M := π.Model M) e ε : M)) by
      simpa [translateRel, Matrix.comp_vecCons', rel_iff,
        Matrix.constant_eq_singleton, Semiterm.val_rew, ←dom_iff, Function.comp_def]
  constructor
  · intro h
    exact h (fun i ↦ ↑((v i).val (M := π.Model M) e ε)) (fun i ↦ by simp [eval_varEqual_iff])
  · intro h w hw
    suffices w = fun i ↦ ↑((v i).val (M := π.Model M) e ε) by rcases this; exact h
    ext i
    let w' : π.Model M := ⟨w i, (hw i).1⟩
    have : Semiformula.Eval (M := M) (w' :> fun i ↦ e i) (fun x ↦ ε x) (π.varEqual (v i)) := by
      simp [w', hw]
    simpa [w'] using congr_arg Model.val (eval_varEqual_iff.mp this)

lemma eval_translate_iff {φ : Semiformula L₂ ξ n} {ε : ξ → π.Model M} {e : Fin n → π.Model M} :
    Semiformula.Eval (M := M) (fun i ↦ e i) (fun i ↦ ε i) (π.translate φ) ↔ φ.Eval e ε := by
  match φ with
  |  .rel R v => simp [translate_rel, eval_rel, eval_translateRel_iff, Function.comp_def]
  | .nrel R v => simp [translate_nrel, eval_nrel, eval_translateRel_iff, Function.comp_def]
  |         ⊤ => simp
  |         ⊥ => simp
  |     φ ⋏ ψ => simp [eval_translate_iff (φ := φ), eval_translate_iff (φ := ψ)]
  |     φ ⋎ ψ => simp [eval_translate_iff (φ := φ), eval_translate_iff (φ := ψ)]
  |      ∀¹ φ =>
    simpa [translate_all, Matrix.comp_vecCons'] using
      (forall_congr' fun a : π.Model M ↦ eval_translate_iff (φ := φ) (e := a :> e) (ε := ε))
  |      ∃¹ φ =>
    simpa [translate_ex, Matrix.comp_vecCons'] using
      (exists_congr fun a : π.Model M ↦ eval_translate_iff (φ := φ) (e := a :> e) (ε := ε))

lemma evalb_translate_iff {φ : Semisentence L₂ n} {e : Fin n → π.Model M} :
    M ⊧/(fun i ↦ e i) (π.translate φ) ↔ (π.Model M) ⊧/e φ := by
  simp [←eval_translate_iff, Empty.eq_elim]

lemma evalb_cons_translate_iff {φ : Semisentence L₂ (n + 1)} {x : π.Model M}
    {e : Fin n → π.Model M} :
    M ⊧/(x :> fun i ↦ e i) (π.translate φ) ↔ (π.Model M) ⊧/(x :> e) φ := by
  simp [←eval_translate_iff, Empty.eq_elim, Matrix.comp_vecCons']

lemma evalb_singleton_translate_iff {φ : Semisentence L₂ 1} {x : π.Model M} :
    M ⊧/![x] (π.translate φ) ↔ (π.Model M) ⊧/![x] φ := by
  simp [←eval_translate_iff, Empty.eq_elim, Matrix.constant_eq_singleton]

lemma evalb_doubleton_translate_iff {φ : Semisentence L₂ 2} {x y : π.Model M} :
    M ⊧/![x, y] (π.translate φ) ↔ (π.Model M) ⊧/![x, y] φ := by
  simp [←eval_translate_iff, Empty.eq_elim, Matrix.constant_eq_singleton, Matrix.comp_vecCons']

lemma translate_iff {σ : Sentence L₂} :
    M↓[L₁] ⊧ π.translate σ ↔ (π.Model M)↓[L₂] ⊧ σ := by
  simpa [models_iff, Matrix.empty_eq, Empty.eq_elim] using
    eval_translate_iff (M := M) (π := π) (ε := Empty.elim) (e := ![]) (φ := σ)

end Model

end semantics

end DirectTranslation
end FFL.FirstOrder
