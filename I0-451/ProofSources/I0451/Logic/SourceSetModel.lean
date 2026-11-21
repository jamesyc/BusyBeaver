module
public import I0451.Logic.ParameterizedZF
public import I0451.Logic.SetSentences
public import Foundation.FirstOrder.SetTheory.Ordinal

/-! Recover the ordinary ZF model axioms from the container,
extensionality and collection principles supplied by the source
calculus, together with the emitted foundation axiom. -/
@[expose] public section
namespace I0451.Logic

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

variable {V : Type} [SetStructure V]

structure SourceSetModel (V : Type) [SetStructure V] : Prop where
  foundation : SetSentences.Foundation (fun x y : V => x ∈ y)
  extensionality : ∀ x y : V, (∀ z : V, z ∈ x ↔ z ∈ y) → x = y
  container : ∀ a : V, ∃ d : V, a ∈ d ∧ ∀ x ∈ d,
    (∃ w ∈ d, ∀ y : V, y ⊆ x → y ∈ w) ∧ x ⊆ d
  collection : ∀ R : V → V → Prop, (ℒₛₑₜ-relation R) → ∀ A : V,
    ∃ B : V, (∀ x ∈ A, (∃ y, R x y) → ∃ z ∈ B, R x z) ∧
      (∀ y ∈ B, ∃ x, R x y)

namespace SourceSetModel

variable (model : SourceSetModel V)
include model

theorem separate (A : V) (P : V → Prop) (defP : ℒₛₑₜ-predicate P) :
    ∃ B : V, ∀ y : V, y ∈ B ↔ y ∈ A ∧ P y := by
  let R (x y : V) := x = y ∧ x ∈ A ∧ P x
  have defR : ℒₛₑₜ-relation R := by unfold R; definability
  obtain ⟨B, collects, witnesses⟩ := model.collection R defR A
  refine ⟨B, fun y => ?_⟩
  constructor
  · intro present
    obtain ⟨x, eq, belongs, holds⟩ := witnesses y present
    exact eq ▸ ⟨belongs, holds⟩
  · rintro ⟨inside, holds⟩
    obtain ⟨z, has, eq, _⟩ := collects y inside ⟨y, rfl, inside, holds⟩
    exact eq.symm ▸ has

theorem empty [Nonempty V] : ∃ e : V, ∀ y : V, y ∉ e := by
  let a : V := Classical.arbitrary V
  obtain ⟨e, _, proves⟩ := model.collection (fun _ _ => False) (by definability) a
  exact ⟨e, fun y hy => (proves y hy).choose_spec⟩

theorem pair [Nonempty V] (a b : V) :
    ∃ d : V, ∀ x : V, x ∈ d ↔ x = a ∨ x = b := by
  obtain ⟨e, empty⟩ := model.empty
  obtain ⟨c, eIn, bounds⟩ := model.container e
  obtain ⟨w, wIn, power⟩ := (bounds e eIn).1
  have eInW := power e (fun _ h => h)
  have distinct : e ≠ w := fun eq => empty e (eq.symm ▸ eInW)
  let R (x y : V) := (x = e ∧ y = a) ∨ (x = w ∧ y = b)
  have defR : ℒₛₑₜ-relation R := by unfold R; definability
  obtain ⟨d, collects, witnesses⟩ := model.collection R defR c
  refine ⟨d, fun x => ?_⟩
  constructor
  · intro present
    obtain ⟨_, left | right⟩ := witnesses x present
    · exact .inl left.2
    · exact .inr right.2
  · rintro (same | same)
    · subst x
      obtain ⟨y, shows, left | right⟩ := collects e eIn ⟨a, .inl ⟨rfl,rfl⟩⟩
      · exact left.2 ▸ shows
      · exact (distinct right.1).elim
    · subst x
      obtain ⟨y, shows, left | right⟩ := collects w wIn ⟨b, .inr ⟨rfl,rfl⟩⟩
      · exact (distinct left.1.symm).elim
      · exact right.2 ▸ shows

theorem union (a : V) : ∃ b : V, ∀ x : V, x ∈ b ↔ ∃ y ∈ a, x ∈ y := by
  obtain ⟨c, ac, bounds⟩ := model.container a
  obtain ⟨b,hb⟩ := model.separate c (fun x => ∃ y ∈ a, x ∈ y) (by definability)
  refine ⟨b, fun x => (hb x).trans (and_iff_right_of_imp fun ⟨y, ya, xy⟩ =>
    (bounds y ((bounds a ac).2 y ya)).2 x xy)⟩

theorem power (a : V) : ∃ b : V, ∀ x : V, x ∈ b ↔ x ⊆ a := by
  obtain ⟨c, ac, bounds⟩ := model.container a
  obtain ⟨w, _, power⟩ := (bounds a ac).1
  obtain ⟨b,hb⟩ := model.separate w (fun x => x ⊆ a) (by definability)
  exact ⟨b, fun x => (hb x).trans (and_iff_right_of_imp (power x))⟩

theorem inductiveSet [Nonempty V] : ∃ I : V,
    (∀ e : V, (∀ y : V, y ∉ e) → e ∈ I) ∧
    ∀ x ∈ I, ∀ y : V, (∀ z : V, z ∈ y ↔ z = x ∨ z ∈ x) → y ∈ I := by
  obtain ⟨e, empty⟩ := model.empty
  obtain ⟨d, hasEmpty, bounds⟩ := model.container e
  let ordinalPart (x : V) := IsTransitive x ∧ ∀ y ∈ x, IsTransitive y
  have defPart : ℒₛₑₜ-predicate ordinalPart := by unfold ordinalPart; definability
  obtain ⟨I, has⟩ := model.separate d ordinalPart defPart
  refine ⟨I, ?_, ?_⟩
  · intro u noMembers
    have same : u = e := model.extensionality u e fun y =>
      ⟨fun found => (noMembers y found).elim, fun found => (empty y found).elim⟩
    subst u
    exact (has e).mpr ⟨hasEmpty, ⟨⟨fun x hx => (empty x hx).elim⟩, fun x hx => (empty x hx).elim⟩⟩
  · intro x xI y next
    obtain ⟨xD, trans, transMembers⟩ := (has x).mp xI
    obtain ⟨w, wD, pow⟩ := (bounds x xD).1
    have ySub : y ⊆ w := by
      intro z zy
      rcases (next z).mp zy with same | inside
      · subst z
        exact pow x (fun _ h => h)
      · exact pow z (trans.transitive z inside)
    obtain ⟨u, uD, sup⟩ := (bounds w wD).1
    have yD := (bounds u uD).2 y (sup y ySub)
    have sub : x ⊆ y := fun z h => (next z).mpr (.inr h)
    refine (has y).mpr ⟨yD, ⟨?_, ?_⟩⟩
    · refine ⟨fun z zy t tz => ?_⟩
      rcases (next z).mp zy with rfl | prev
      · exact sub t tz
      · exact sub t (trans.transitive z prev t tz)
    · intro z zy
      rcases (next z).mp zy with rfl | prev
      · exact trans
      · exact transMembers z prev

theorem replace (A : V) (R : V → V → Prop) (defR : ℒₛₑₜ-relation R)
    (total : ∀ x, ∃! y, R x y) : ∃ B : V, ∀ y, y ∈ B ↔ ∃ x ∈ A, R x y := by
  let restricted (x y : V) := x ∈ A ∧ R x y
  have restriction : ℒₛₑₜ-relation restricted := by unfold restricted; definability
  obtain ⟨B, collects, witnesses⟩ := model.collection restricted restriction A
  refine ⟨B, fun y => ⟨witnesses y, ?_⟩⟩
  rintro ⟨x, xA, atY⟩
  obtain ⟨z, zB, _, atZ⟩ := collects x xA ⟨y, xA, atY⟩
  have eq := (total x).unique atZ atY
  exact eq ▸ zB

theorem models_zf [Nonempty V] : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := by
  constructor
  rintro σ ((base | sep) | repl)
  · cases base with
    | equality _ h => exact Theory.models V (𝗘𝗤 ℒₛₑₜ) h
    | empty_set => simpa [models_iff, isEmpty, Rew.q_subst, Matrix.comp_vecCons', Function.comp_def] using model.empty
    | extensionality =>
      simp [models_iff]
      intro x y
      exact ⟨fun eq z => eq ▸ Iff.rfl, model.extensionality x y⟩
    | pairing => simpa [models_iff] using model.pair
    | union => simpa [models_iff] using model.union
    | power_set => simpa [models_iff] using model.power
    | infinity => simpa [models_iff, isEmpty, isSucc, Rew.q_subst, Matrix.comp_vecCons', Function.comp_def] using model.inductiveSet
    | foundation =>
      simp [models_iff, isNonempty, Rew.q_subst, Matrix.comp_vecCons', Function.comp_def]
      intro a witness member
      obtain ⟨x, belongs, noChain⟩ := model.foundation a ⟨witness, member⟩
      exact ⟨x, belongs, fun y inA inX => noChain y inX inA⟩
  · cases sep with
    | separation φ =>
      simp [models_iff, Axiom.separationSchema, Semiformula.eval_univCl, Matrix.comp_vecCons', Function.comp_def]
      intro s x
      have defP : ℒₛₑₜ-predicate (fun z : V => φ.Eval (fun _ => z) s) := by
        refine ⟨(Rew.rewriteMap s) ▹ φ, fun v => ?_⟩
        rw [Semiformula.eval_rewriteMap, Matrix.fun_eq_vec_one v]
        simp [Matrix.vec_single_eq_const, Function.comp_def]
      exact model.separate x _ defP
  · cases repl with
    | replacement φ =>
      simp [models_iff, Axiom.replacementSchema, Semiformula.eval_univCl, Matrix.comp_vecCons', Function.comp_def]
      intro s total X
      have defR : ℒₛₑₜ-relation (fun x y : V => φ.Eval (x :> fun _ : Fin 1 => y) s) := by
        refine ⟨(Rew.rewriteMap s) ▹ φ, fun v => ?_⟩
        rw [Semiformula.eval_rewriteMap, Matrix.fun_eq_vec_two v]
        simp [Matrix.vec_single_eq_const, Function.comp_def]
      exact model.replace X _ defR total

end SourceSetModel

end I0451.Logic
