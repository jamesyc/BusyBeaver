module
public import GateModel.Axioms
public import GateModel.Interp
public import GateModel.WellFounded
@[expose] public section
/-! # The marked quotient satisfies ZF without Foundation -/
namespace ZF209.GateModel
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [GateHull V]
variable {e : V} (he : SetTheory.IsEmpty e)

/-- `v` is a marked successor of `u`. -/
def QSucc (e v u : V) : Prop := e ∈ v ∧ ∀ t, (t ∈ v ∧ e ∈ t) ↔ (t = u ∨ (t ∈ u ∧ e ∈ t))

omit [Nonempty V] [GateHull V] in
instance QSucc.definable : ℒₛₑₜ-relation₃ (QSucc (V := V)) := by
  unfold QSucc; definability

include he

open Classical in
/-- Classes of objects, total on `V`. -/
noncomputable def Q.cls (x : V) : Q he :=
  if h : e ∈ x then Q.mk he x h
  else Q.mk he _ (Classical.choose_spec (exists_marked_empty he)).1

lemma Q.cls_of {x : V} (hx : e ∈ x) : Q.cls he x = Q.mk he x hx := by
  unfold Q.cls; exact dif_pos hx

/-- The marked quotient as an interpretation in `V`. -/
noncomputable def qInterp : Interp V (Q he) where
  dom x := e ∈ x
  π := Q.cls he
  surj Y := by
    induction Y using Q.ind he with
    | h x hx => exact ⟨x, hx, Q.cls_of he hx⟩
  mem := QMem e
  mem_iff x y hx hy := by
    show QMem e x y ↔ Q.cls he x ∈ Q.cls he y
    rw [Q.cls_of he hx, Q.cls_of he hy]
    exact (Q.mk_mem_mk he hx hy).symm
  eq := Eqv e
  eq_iff x y hx hy := by
    show Eqv e x y ↔ Q.cls he x = Q.cls he y
    rw [Q.cls_of he hx, Q.cls_of he hy, Q.mk_eq_mk]
  dom_def := by definability
  mem_def := by definability
  eq_def := by definability

lemma q_pullback_pred {P : Q he → Prop} (hP : ℒₛₑₜ-predicate P) :
    ℒₛₑₜ-predicate (fun w : V => ∃ hw : e ∈ w, P (Q.mk he w hw)) := by
  refine Language.Definable.of_iff ((qInterp he).pullback_pred hP) fun v => ?_
  show (∃ hw : e ∈ v 0, P (Q.mk he (v 0) hw)) ↔ e ∈ v 0 ∧ P (Q.cls he (v 0))
  exact ⟨fun ⟨h, hp⟩ => ⟨h, by rwa [Q.cls_of he h]⟩,
    fun ⟨h, hp⟩ => ⟨h, by rwa [Q.cls_of he h] at hp⟩⟩

lemma q_pullback_rel {F : Q he → Q he → Prop} (hF : ℒₛₑₜ-relation F) :
    ℒₛₑₜ-relation (fun w v : V =>
      ∃ hw : e ∈ w, ∃ hv : e ∈ v, F (Q.mk he w hw) (Q.mk he v hv)) := by
  refine Language.Definable.of_iff ((qInterp he).pullback_rel hF) fun u => ?_
  show (∃ hw : e ∈ u 0, ∃ hv : e ∈ u 1, F (Q.mk he (u 0) hw) (Q.mk he (u 1) hv)) ↔
    e ∈ u 0 ∧ e ∈ u 1 ∧ F (Q.cls he (u 0)) (Q.cls he (u 1))
  exact ⟨fun ⟨h₀, h₁, hp⟩ => ⟨h₀, h₁, by rwa [Q.cls_of he h₀, Q.cls_of he h₁]⟩,
    fun ⟨h₀, h₁, hp⟩ => ⟨h₀, h₁, by rwa [Q.cls_of he h₀, Q.cls_of he h₁] at hp⟩⟩

/-- Transitive classes containing any class. -/
theorem Q.exists_trans (X : Q he) : ∃ T : Q he, X ∈ T ∧ ∀ Y ∈ T, ∀ Z ∈ Y, Z ∈ T := by
  induction X using Q.ind he with
  | h x hx =>
  obtain ⟨T, hxT, hT⟩ := exists_transitive_superset he x
  obtain ⟨C, heC, hC⟩ := select he T (fun _ => True) (by definability)
  refine ⟨Q.mk he C heC,
    (Q.mem_mk_iff he heC).mpr ⟨x, hx, ((hC x).mpr ⟨hxT, hx, trivial⟩).1, rfl⟩,
    fun Y hY Z hZ => ?_⟩
  obtain ⟨y, hy, hyC, rfl⟩ := (Q.mem_mk_iff he heC).mp hY
  obtain ⟨z, hz, hzy, rfl⟩ := (Q.mem_mk_iff he hy).mp hZ
  have hyT := ((hC y).mp ⟨hyC, hy⟩).1
  exact (Q.mem_mk_iff he heC).mpr ⟨z, hz, ((hC z).mpr ⟨hT y hyT z hzy, hz, trivial⟩).1, rfl⟩

lemma exists_qsucc {u : V} (hu : e ∈ u) : ∃ v, QSucc e v u := by
  obtain ⟨T, huT, hT⟩ := exists_transitive_superset he u
  obtain ⟨C, heC, hC⟩ := select he T (fun t => t = u ∨ t ∈ u) (by definability)
  refine ⟨C, heC, fun t => ⟨fun ⟨ht, het⟩ => ?_, fun h => ?_⟩⟩
  · obtain ⟨-, -, h⟩ := (hC t).mp ⟨ht, het⟩
    exact h.imp id fun h => ⟨h, het⟩
  · rcases h with h | ⟨htu, het⟩
    · subst h; exact (hC t).mpr ⟨huT, hu, Or.inl rfl⟩
    · exact (hC t).mpr ⟨hT u huT t htu, het, Or.inr htu⟩

lemma QSucc.mk_mem_iff {v u : V} (h : QSucc e v u) (hu : e ∈ u) (Z : Q he) :
    Z ∈ Q.mk he v h.1 ↔ Z = Q.mk he u hu ∨ Z ∈ Q.mk he u hu := by
  rw [Q.mem_mk_iff, Q.mem_mk_iff]
  constructor
  · rintro ⟨t, ht, htv, rfl⟩
    rcases (h.2 t).mp ⟨htv, ht⟩ with h' | ⟨htu, _⟩
    · subst h'; exact Or.inl rfl
    · exact Or.inr ⟨t, ht, htu, rfl⟩
  · rintro (rfl | ⟨t, ht, htu, rfl⟩)
    · exact ⟨u, hu, ((h.2 u).mpr (Or.inl rfl)).1, rfl⟩
    · exact ⟨t, ht, ((h.2 t).mpr (Or.inr ⟨htu, ht⟩)).1, rfl⟩

/-- An inductive class. -/
theorem Q.exists_inductive : ∃ I : Q he, (∃ E ∈ I, ∀ Z, Z ∉ E) ∧
    ∀ X ∈ I, ∃ S ∈ I, ∀ Z, Z ∈ S ↔ Z = X ∨ Z ∈ X := by
  obtain ⟨E₀, heE₀, hE₀⟩ := exists_marked_empty he
  let R : V → V → Prop := fun u v => (u = e ∧ v = E₀) ∨ (e ∈ u ∧ QSucc e v u)
  obtain ⟨C, hC⟩ := GateHull.hull R (by definability) e E₀
  have hE₀C : E₀ ∈ C := hC.start (Or.inl ⟨rfl, rfl⟩)
  have hsucc : ∀ z ∈ C, e ∈ z → ∃ w ∈ C, QSucc e w z := by
    intro z hz hez
    obtain ⟨v, hv⟩ := exists_qsucc he hez
    obtain ⟨w, hw, h | h⟩ := hC.cover hz (subset_refl z) (v := v) (Or.inr ⟨hez, hv⟩)
    · exact (he e (h.1 ▸ hez)).elim
    · exact ⟨w, hw, h.2⟩
  obtain ⟨I, heI, hI⟩ := select he C (fun _ => True) (by definability)
  refine ⟨Q.mk he I heI, ⟨Q.mk he E₀ heE₀, (Q.mem_mk_iff he heI).mpr
    ⟨E₀, heE₀, ((hI E₀).mpr ⟨hE₀C, heE₀, trivial⟩).1, rfl⟩, fun Z hZ => ?_⟩, fun X hX => ?_⟩
  · obtain ⟨z, hz, hzE, -⟩ := (Q.mem_mk_iff he heE₀).mp hZ
    exact hE₀ z hzE hz
  · obtain ⟨z, hz, hzI, rfl⟩ := (Q.mem_mk_iff he heI).mp hX
    obtain ⟨w, hwC, hw⟩ := hsucc z ((hI z).mp ⟨hzI, hz⟩).1 hz
    exact ⟨Q.mk he w hw.1, (Q.mem_mk_iff he heI).mpr
      ⟨w, hw.1, ((hI w).mpr ⟨hwC, hw.1, trivial⟩).1, rfl⟩, QSucc.mk_mem_iff he hw hz⟩

/-- The marked quotient satisfies ZF without Foundation. -/
instance Q.zfMinus : ZFMinus (Q he) where
  ext _ _ h := Q.ext he h
  empty := Q.exists_empty he
  pair := Q.exists_pair he
  union := Q.exists_union he
  power := Q.exists_power he
  sep P hP x := Q.exists_sep he x P (q_pullback_pred he hP)
  repl F hF hfun x := Q.exists_repl he x F (q_pullback_rel he hF) hfun
  infinity := Q.exists_inductive he
  trans := Q.exists_trans he

end ZF209.GateModel
