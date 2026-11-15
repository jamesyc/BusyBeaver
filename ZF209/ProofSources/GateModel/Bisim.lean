module
public import GateModel.Hull
@[expose] public section
/-! # Marked bisimulation equality

Fix an object `e` with no members. Objects containing `e` are *marked*, and only
marked members count. Two marked objects are identified when a set of marked
pairs relates them and matches their marked members back and forth. -/
namespace ZF209.GateModel
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V]

/-- `s` is marked and its only marked member is `a`. -/
def MSing (e s a : V) : Prop := e ∈ s ∧ ∀ t, (t ∈ s ∧ e ∈ t) ↔ t = a

/-- `s` is marked and its marked members are exactly `a` and `b`. -/
def MDoub (e s a b : V) : Prop := e ∈ s ∧ ∀ t, (t ∈ s ∧ e ∈ t) ↔ (t = a ∨ t = b)

/-- `p` is a marked Kuratowski pair of `a` and `b`. -/
def MPair (e p a b : V) : Prop :=
  e ∈ p ∧ (∀ t ∈ p, e ∈ t → MSing e t a ∨ MDoub e t a b) ∧
    (∃ t ∈ p, MSing e t a) ∧ ∃ t ∈ p, MDoub e t a b

/-- `B` holds a marked pair of `a` and `b`. -/
def PairIn (e B a b : V) : Prop := ∃ p ∈ B, MPair e p a b

/-- Back-and-forth matching of marked members, up to equality or `B`. -/
def BackForth (e B x y : V) : Prop :=
  (∀ x' ∈ x, e ∈ x' → ∃ y' ∈ y, e ∈ y' ∧ (x' = y' ∨ PairIn e B x' y')) ∧
    ∀ y' ∈ y, e ∈ y' → ∃ x' ∈ x, e ∈ x' ∧ (x' = y' ∨ PairIn e B x' y')

/-- `B` is a marked bisimulation. -/
def Bisim (e B : V) : Prop := ∀ x y, PairIn e B x y → BackForth e B x y

/-- Marked bisimilarity. -/
def Eqv (e x y : V) : Prop := x = y ∨ ∃ B, Bisim e B ∧ PairIn e B x y

instance MSing.definable : ℒₛₑₜ-relation₃ (MSing (V := V)) := by
  unfold MSing; definability

instance MDoub.definable : ℒₛₑₜ-relation₄ (MDoub (V := V)) := by
  unfold MDoub; definability

instance MPair.definable : ℒₛₑₜ-relation₄ (MPair (V := V)) := by
  unfold MPair; definability

instance PairIn.definable : ℒₛₑₜ-relation₄ (PairIn (V := V)) := by
  unfold PairIn; definability


instance BackForth.definable : ℒₛₑₜ-relation₄ (BackForth (V := V)) := by
  unfold BackForth; definability

instance Bisim.definable : ℒₛₑₜ-relation (Bisim (V := V)) := by
  unfold Bisim; definability

/-- `K` bundles, for the pair `p = (a,c)`, the marked pairs `(a,b)` with `(c,b) ∈ B₂`. -/
def IsBundle (e B₂ p K : V) : Prop := ∃ a c, MPair e p a c ∧ e ∈ K ∧
  (∀ q ∈ K, e ∈ q → ∃ b, PairIn e B₂ c b ∧ MPair e q a b) ∧
  ∀ b, PairIn e B₂ c b → ∃ q ∈ K, MPair e q a b

set_option maxHeartbeats 1000000 in
instance IsBundle.definable (e B₂ : V) : ℒₛₑₜ-relation (IsBundle e B₂) := by
  unfold IsBundle; definability

section Laws
variable {e : V}

lemma MSing.mem {s a : V} (h : MSing e s a) : a ∈ s ∧ e ∈ a := (h.2 a).mpr rfl

lemma MSing.eq {s a t : V} (h : MSing e s a) (ht : t ∈ s) (het : e ∈ t) : t = a :=
  (h.2 t).mp ⟨ht, het⟩

lemma MDoub.mem_left {s a b : V} (h : MDoub e s a b) : a ∈ s ∧ e ∈ a := (h.2 a).mpr (Or.inl rfl)

lemma MDoub.mem_right {s a b : V} (h : MDoub e s a b) : b ∈ s ∧ e ∈ b :=
  (h.2 b).mpr (Or.inr rfl)

lemma MDoub.eq {s a b t : V} (h : MDoub e s a b) (ht : t ∈ s) (het : e ∈ t) : t = a ∨ t = b :=
  (h.2 t).mp ⟨ht, het⟩

lemma MSing.marked {s a : V} (h : MSing e s a) : e ∈ s := h.1

lemma MDoub.marked {s a b : V} (h : MDoub e s a b) : e ∈ s := h.1

/-- The components of a marked pair are marked. -/
lemma MPair.marked_left {p a b : V} (h : MPair e p a b) : e ∈ a := by
  obtain ⟨t, _, ht⟩ := h.2.2.1; exact ht.mem.2

lemma MPair.marked_right {p a b : V} (h : MPair e p a b) : e ∈ b := by
  obtain ⟨t, _, ht⟩ := h.2.2.2; exact ht.mem_right.2

/-- Kuratowski uniqueness for marked pairs. -/
lemma MPair.unique {p a b a' b' : V} (h : MPair e p a b) (h' : MPair e p a' b') :
    a = a' ∧ b = b' := by
  have ha : a = a' := by
    obtain ⟨t, htp, ht⟩ := h'.2.2.1
    rcases h.2.1 t htp ht.marked with hs | hd
    · exact (ht.eq hs.mem.1 hs.mem.2)
    · exact ht.eq hd.mem_left.1 hd.mem_left.2
  subst ha
  refine ⟨rfl, ?_⟩
  obtain ⟨t, htp, ht⟩ := h'.2.2.2
  obtain ⟨t₂, ht₂p, ht₂⟩ := h.2.2.2
  rcases h.2.1 t htp ht.marked with hs | hd
  · -- `t` is the singleton of `a`, so `b' = a`
    have hb' : b' = a := hs.eq ht.mem_right.1 ht.mem_right.2
    rcases h'.2.1 t₂ ht₂p ht₂.marked with hs₂ | hd₂
    · exact (hs₂.eq ht₂.mem_right.1 ht₂.mem_right.2).trans hb'.symm
    · rcases hd₂.eq ht₂.mem_right.1 ht₂.mem_right.2 with h1 | h1
      · exact h1.trans hb'.symm
      · exact h1
  · rcases hd.eq ht.mem_right.1 ht.mem_right.2 with h1 | h1
    · -- `b' = a`; then `b` is `a` or `b'`
      rcases ht.eq hd.mem_right.1 hd.mem_right.2 with h2 | h2
      · exact h2.trans h1.symm
      · exact h2
    · exact h1.symm

lemma PairIn.marked {B a b : V} (h : PairIn e B a b) : e ∈ a ∧ e ∈ b := by
  obtain ⟨p, _, hp⟩ := h; exact ⟨hp.marked_left, hp.marked_right⟩

end Laws

variable [Nonempty V] [GateHull V] {e : V} (he : SetTheory.IsEmpty e)
include he

/-- Marked singletons exist for marked objects. -/
lemma exists_msing {a : V} (ha : e ∈ a) : ∃ s, MSing e s a := by
  obtain ⟨z, hz⟩ := exists_singleton a
  obtain ⟨C, heC, hC⟩ := select he z (· = a) (by definability)
  refine ⟨C, heC, fun t => ⟨fun ht => ((hC t).mp ht).2.2, fun ht => ?_⟩⟩
  subst ht; exact (hC t).mpr ⟨hz.mem_self, ha, rfl⟩

/-- Marked doubletons exist for marked objects. -/
lemma exists_mdoub {a b : V} (ha : e ∈ a) (hb : e ∈ b) : ∃ s, MDoub e s a b := by
  obtain ⟨z, hz⟩ := exists_pair a b
  obtain ⟨C, heC, hC⟩ := select he z (fun t => t = a ∨ t = b) (by definability)
  refine ⟨C, heC, fun t => ⟨fun ht => ((hC t).mp ht).2.2, fun ht => ?_⟩⟩
  rcases ht with rfl | rfl
  · exact (hC t).mpr ⟨(hz t).mpr (Or.inl rfl), ha, Or.inl rfl⟩
  · exact (hC t).mpr ⟨(hz t).mpr (Or.inr rfl), hb, Or.inr rfl⟩

/-- Marked pairs exist for marked objects. -/
lemma exists_mpair {a b : V} (ha : e ∈ a) (hb : e ∈ b) : ∃ p, MPair e p a b := by
  obtain ⟨s, hs⟩ := exists_msing he ha
  obtain ⟨d, hd⟩ := exists_mdoub he ha hb
  obtain ⟨z, hz⟩ := exists_pair s d
  obtain ⟨C, heC, hC⟩ :=
    select he z (fun t => MSing e t a ∨ MDoub e t a b) (by definability)
  refine ⟨C, heC, fun t ht het => ((hC t).mp ⟨ht, het⟩).2.2, ⟨s, ?_, hs⟩, ⟨d, ?_, hd⟩⟩
  · exact ((hC s).mpr ⟨(hz s).mpr (Or.inl rfl), hs.marked, Or.inl hs⟩).1
  · exact ((hC d).mpr ⟨(hz d).mpr (Or.inr rfl), hd.marked, Or.inr hd⟩).1

/-- The converse of a marked relation. -/
lemma exists_converse (B : V) :
    ∃ B' : V, ∀ x y, PairIn e B' y x ↔ PairIn e B x y := by
  obtain ⟨C, _, hsound, hcomp⟩ :=
    collect he B (fun p q => ∃ a b, MPair e p a b ∧ MPair e q b a) (by definability)
  refine ⟨C, fun x y => ⟨fun ⟨q, hq, hqp⟩ => ?_, fun ⟨p, hp, hpp⟩ => ?_⟩⟩
  · obtain ⟨p, hp, a, b, hpab, hqba⟩ := hsound q hq hqp.1
    obtain ⟨rfl, rfl⟩ := hqp.unique hqba
    exact ⟨p, hp, hpab⟩
  · obtain ⟨q, hq⟩ := exists_mpair he hpp.marked_right hpp.marked_left
    obtain ⟨q', hq', _, a, b, hpab, hq'ba⟩ := hcomp p hp ⟨q, hq.1, x, y, hpp, hq⟩
    obtain ⟨rfl, rfl⟩ := hpp.unique hpab
    exact ⟨q', hq', hq'ba⟩

/-- Union of two marked relations together with their composite. -/
lemma exists_comp_union (B₁ B₂ : V) :
    ∃ B₃ : V, ∀ a b, PairIn e B₃ a b ↔
      PairIn e B₁ a b ∨ PairIn e B₂ a b ∨ ∃ c, PairIn e B₁ a c ∧ PairIn e B₂ c b := by
  let Bundle : V → V → Prop := IsBundle e B₂
  have hbundle : ∀ p a c, MPair e p a c → ∃ K, Bundle p K := by
    intro p a c hp
    obtain ⟨K, heK, hsound, hcomp⟩ :=
      collect he B₂ (fun p₂ q => ∃ b, MPair e p₂ c b ∧ MPair e q a b) (by definability)
    refine ⟨K, a, c, hp, heK, fun q hq heq => ?_, fun b ⟨p₂, hp₂, hp₂cb⟩ => ?_⟩
    · obtain ⟨p₂, hp₂, b, hp₂cb, hqab⟩ := hsound q hq heq
      exact ⟨b, ⟨p₂, hp₂, hp₂cb⟩, hqab⟩
    · obtain ⟨q₀, hq₀⟩ := exists_mpair he hp.marked_left hp₂cb.marked_right
      obtain ⟨q, hq, _, b', hp₂cb', hqab'⟩ := hcomp p₂ hp₂ ⟨q₀, hq₀.1, b, hp₂cb, hq₀⟩
      obtain ⟨-, rfl⟩ := hp₂cb.unique hp₂cb'
      exact ⟨q, hq, hqab'⟩
  obtain ⟨F, _, hFsound, hFcomp⟩ := collect he B₁ Bundle (by definability)
  -- a transitive object below which every relevant pair lies
  obtain ⟨P₁, hP₁⟩ := exists_pair B₂ F
  obtain ⟨P₀, hP₀⟩ := exists_pair B₁ P₁
  obtain ⟨T, hP₀T, hT⟩ := exists_transitive_superset he P₀
  have hB₁T : B₁ ∈ T := hT P₀ hP₀T B₁ ((hP₀ B₁).mpr (Or.inl rfl))
  have hP₁T : P₁ ∈ T := hT P₀ hP₀T P₁ ((hP₀ P₁).mpr (Or.inr rfl))
  have hB₂T : B₂ ∈ T := hT P₁ hP₁T B₂ ((hP₁ B₂).mpr (Or.inl rfl))
  have hFT : F ∈ T := hT P₁ hP₁T F ((hP₁ F).mpr (Or.inr rfl))
  let Rel : V → V → Prop := fun a b =>
    PairIn e B₁ a b ∨ PairIn e B₂ a b ∨ ∃ c, PairIn e B₁ a c ∧ PairIn e B₂ c b
  obtain ⟨B₃, _, hB₃⟩ := select he T (fun q => ∃ a b, MPair e q a b ∧ Rel a b) (by definability)
  refine ⟨B₃, fun a b => ⟨fun ⟨q, hq, hqab⟩ => ?_, fun hr => ?_⟩⟩
  · obtain ⟨-, -, a', b', hq', hr⟩ := (hB₃ q).mp ⟨hq, hqab.1⟩
    obtain ⟨rfl, rfl⟩ := hqab.unique hq'
    exact hr
  · have mem3 : ∀ q, q ∈ T → MPair e q a b → PairIn e B₃ a b := fun q hqT hq =>
      ⟨q, ((hB₃ q).mpr ⟨hqT, hq.1, a, b, hq, hr⟩).1, hq⟩
    rcases hr with ⟨p, hp, hpp⟩ | ⟨p, hp, hpp⟩ | ⟨c, ⟨p, hp, hpac⟩, hcb⟩
    · exact mem3 p (hT B₁ hB₁T p hp) hpp
    · exact mem3 p (hT B₂ hB₂T p hp) hpp
    · obtain ⟨K₀, hK₀⟩ := hbundle p a c hpac
      have heK₀ : e ∈ K₀ := by obtain ⟨_, _, _, h, _⟩ := hK₀; exact h
      obtain ⟨K, hKF, heK, a', c', hpac', _, _, hall⟩ := hFcomp p hp ⟨K₀, heK₀, hK₀⟩
      obtain ⟨rfl, rfl⟩ := hpac.unique hpac'
      obtain ⟨q, hqK, hq⟩ := hall b hcb
      exact mem3 q (hT K (hT F hFT K hKF) q hqK) hq

/-- Bisimilarity is symmetric. -/
lemma Eqv.symm {x y : V} (h : Eqv e x y) : Eqv e y x := by
  rcases h with rfl | ⟨B, hB, hxy⟩
  · exact Or.inl rfl
  obtain ⟨B', hB'⟩ := exists_converse he B
  refine Or.inr ⟨B', fun a b hab => ?_, (hB' x y).mpr hxy⟩
  obtain ⟨hf, hb⟩ := hB b a ((hB' b a).mp hab)
  refine ⟨fun a' ha' hea' => ?_, fun b' hb' heb' => ?_⟩
  · obtain ⟨b', hb', heb', h⟩ := hb a' ha' hea'
    exact ⟨b', hb', heb', h.elim (fun h => Or.inl h.symm) fun h => Or.inr ((hB' b' a').mpr h)⟩
  · obtain ⟨a', ha', hea', h⟩ := hf b' hb' heb'
    exact ⟨a', ha', hea', h.elim (fun h => Or.inl h.symm) fun h => Or.inr ((hB' b' a').mpr h)⟩

/-- Bisimilarity is transitive. -/
lemma Eqv.trans {x y z : V} (h₁ : Eqv e x y) (h₂ : Eqv e y z) : Eqv e x z := by
  rcases h₁ with rfl | ⟨B₁, hB₁, hxy⟩
  · exact h₂
  rcases h₂ with rfl | ⟨B₂, hB₂, hyz⟩
  · exact Or.inr ⟨B₁, hB₁, hxy⟩
  obtain ⟨B₃, hB₃⟩ := exists_comp_union he B₁ B₂
  -- a matched step in `B₁` or `B₂` is a matched step in `B₃`
  have up₁ : ∀ {a b}, a = b ∨ PairIn e B₁ a b → a = b ∨ PairIn e B₃ a b := fun h =>
    h.imp id fun h => (hB₃ _ _).mpr (Or.inl h)
  have up₂ : ∀ {a b}, a = b ∨ PairIn e B₂ a b → a = b ∨ PairIn e B₃ a b := fun h =>
    h.imp id fun h => (hB₃ _ _).mpr (Or.inr (Or.inl h))
  have glue : ∀ {a b c}, (a = b ∨ PairIn e B₁ a b) → (b = c ∨ PairIn e B₂ b c) →
      a = c ∨ PairIn e B₃ a c := by
    intro a b c h₁ h₂
    rcases h₁ with rfl | h₁
    · exact up₂ h₂
    rcases h₂ with rfl | h₂
    · exact up₁ (Or.inr h₁)
    · exact Or.inr ((hB₃ a c).mpr (Or.inr (Or.inr ⟨b, h₁, h₂⟩)))
  refine Or.inr ⟨B₃, fun a c hac => ?_, (hB₃ x z).mpr (Or.inr (Or.inr ⟨y, hxy, hyz⟩))⟩
  rcases (hB₃ a c).mp hac with h | h | ⟨b, hab, hbc⟩
  · obtain ⟨hf, hb⟩ := hB₁ a c h
    exact ⟨fun a' ha' he' => (hf a' ha' he').imp fun _ ⟨h1, h2, h3⟩ => ⟨h1, h2, up₁ h3⟩,
      fun c' hc' he' => (hb c' hc' he').imp fun _ ⟨h1, h2, h3⟩ => ⟨h1, h2, up₁ h3⟩⟩
  · obtain ⟨hf, hb⟩ := hB₂ a c h
    exact ⟨fun a' ha' he' => (hf a' ha' he').imp fun _ ⟨h1, h2, h3⟩ => ⟨h1, h2, up₂ h3⟩,
      fun c' hc' he' => (hb c' hc' he').imp fun _ ⟨h1, h2, h3⟩ => ⟨h1, h2, up₂ h3⟩⟩
  · obtain ⟨hf₁, hb₁⟩ := hB₁ a b hab
    obtain ⟨hf₂, hb₂⟩ := hB₂ b c hbc
    refine ⟨fun a' ha' he' => ?_, fun c' hc' he' => ?_⟩
    · obtain ⟨b', hb', heb', s₁⟩ := hf₁ a' ha' he'
      obtain ⟨c', hc', hec', s₂⟩ := hf₂ b' hb' heb'
      exact ⟨c', hc', hec', glue s₁ s₂⟩
    · obtain ⟨b', hb', heb', s₂⟩ := hb₂ c' hc' he'
      obtain ⟨a', ha', hea', s₁⟩ := hb₁ b' hb' heb'
      exact ⟨a', ha', hea', glue s₁ s₂⟩

end ZF209.GateModel
