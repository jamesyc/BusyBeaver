module
public import GateModel.Quotient
@[expose] public section
/-! # ZF axioms in the marked quotient (first part) -/
namespace ZF209.GateModel
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [GateHull V]
variable {e : V} (he : SetTheory.IsEmpty e)
omit [Nonempty V] [GateHull V] in
instance Eqv.definable : ℒₛₑₜ-relation₃ (Eqv (V := V)) := by
  unfold Eqv; definability

omit [Nonempty V] [GateHull V] in
instance QMem.definable : ℒₛₑₜ-relation₃ (QMem (V := V)) := by
  unfold QMem; definability

/-- A marked bisimulation from one of two families. -/
abbrev GoodW (e F₁ F₂ W : V) : Prop := (W ∈ F₁ ∨ W ∈ F₂) ∧ e ∈ W ∧ Bisim e W

/-- The relation built for extensionality. -/
abbrev ExtRel (e x y F₁ F₂ a b : V) : Prop :=
  (a = x ∧ b = y) ∨ ∃ W, GoodW e F₁ F₂ W ∧ PairIn e W a b

/-- Marked pairs whose components are related by `R`. -/
abbrev PairOf (e : V) (R : V → V → Prop) (q : V) : Prop := ∃ a b, MPair e q a b ∧ R a b

omit [Nonempty V] [GateHull V] in
instance GoodW.definable (e F₁ F₂ : V) : ℒₛₑₜ-predicate (GoodW e F₁ F₂) := by
  unfold GoodW; definability

omit [Nonempty V] [GateHull V] in
instance ExtRel.definable (e x y F₁ F₂ : V) : ℒₛₑₜ-relation (ExtRel e x y F₁ F₂) := by
  unfold ExtRel; definability

omit [Nonempty V] [GateHull V] in
instance PairOf.definable (e : V) (R : V → V → Prop) [hR : ℒₛₑₜ-relation R] :
    ℒₛₑₜ-predicate (PairOf e R) := by
  unfold PairOf; definability

include he

/-- A marked copy of a relation, with the same marked pairs. -/
lemma exists_marked_copy (B : V) : ∃ B' : V, e ∈ B' ∧ ∀ a b, PairIn e B' a b ↔ PairIn e B a b := by
  obtain ⟨C, heC, hC⟩ := select he B (fun _ => True) (by definability)
  refine ⟨C, heC, fun a b => ⟨fun ⟨p, hp, hpp⟩ => ?_, fun ⟨p, hp, hpp⟩ => ?_⟩⟩
  · exact ⟨p, ((hC p).mp ⟨hp, hpp.1⟩).1, hpp⟩
  · exact ⟨p, ((hC p).mpr ⟨hp, hpp.1, trivial⟩).1, hpp⟩

/-- A marked object with no marked members. -/
lemma exists_marked_empty : ∃ s : V, e ∈ s ∧ ∀ t ∈ s, e ∉ t := by
  obtain ⟨s, hs⟩ := exists_singleton e
  exact ⟨s, hs.mem_self, fun t ht het => he e ((hs.eq ht) ▸ het)⟩

/-- Bisimilarity is witnessed by a marked bisimulation, possibly with no pairs. -/
lemma Eqv.witness {x y : V} (h : Eqv e x y) :
    ∃ W : V, e ∈ W ∧ Bisim e W ∧ (x = y ∨ PairIn e W x y) := by
  rcases h with rfl | ⟨B, hB, hxy⟩
  · obtain ⟨s, hes, hs⟩ := exists_marked_empty he
    exact ⟨s, hes, fun a b ⟨p, hp, hpp⟩ => (hs p hp hpp.1).elim, Or.inl rfl⟩
  · obtain ⟨B', heB', hB'⟩ := exists_marked_copy he B
    refine ⟨B', heB', fun a b hab => ?_, Or.inr ((hB' x y).mpr hxy)⟩
    obtain ⟨hf, hb⟩ := hB a b ((hB' a b).mp hab)
    exact ⟨fun a' ha' he' => (hf a' ha' he').imp fun _ ⟨h1, h2, h3⟩ =>
        ⟨h1, h2, h3.imp id fun h => (hB' _ _).mpr h⟩,
      fun b' hb' he' => (hb b' hb' he').imp fun _ ⟨h1, h2, h3⟩ =>
        ⟨h1, h2, h3.imp id fun h => (hB' _ _).mpr h⟩⟩

/-- Extensionality: marked objects with the same members up to bisimilarity are
bisimilar. -/
lemma eqv_of_qmem_iff {x y : V} (hex : e ∈ x) (hey : e ∈ y) (hext : ∀ z, e ∈ z → (QMem e z x ↔ QMem e z y)) :
    Eqv e x y := by
  let P₁ : V → V → Prop := fun x' W => e ∈ W ∧ Bisim e W ∧
    ∃ y' ∈ y, e ∈ y' ∧ (x' = y' ∨ PairIn e W x' y')
  let P₂ : V → V → Prop := fun y' W => e ∈ W ∧ Bisim e W ∧
    ∃ x' ∈ x, e ∈ x' ∧ (x' = y' ∨ PairIn e W x' y')
  obtain ⟨F₁, _, hF₁s, hF₁c⟩ := collect he x P₁ (by definability)
  obtain ⟨F₂, _, hF₂s, hF₂c⟩ := collect he y P₂ (by definability)
  have hx : ∀ x' ∈ x, e ∈ x' → ∃ W, e ∈ W ∧ P₁ x' W := by
    intro x' hx' he'
    obtain ⟨y', hy', hey', hxy'⟩ := (hext x' he').mp ⟨x', hx', he', Or.inl rfl⟩
    obtain ⟨W, heW, hW, h⟩ := hxy'.witness he
    exact ⟨W, heW, heW, hW, y', hy', hey', h⟩
  have hy : ∀ y' ∈ y, e ∈ y' → ∃ W, e ∈ W ∧ P₂ y' W := by
    intro y' hy' he'
    obtain ⟨x', hx', hex', hyx'⟩ := (hext y' he').mpr ⟨y', hy', he', Or.inl rfl⟩
    obtain ⟨W, heW, hW, h⟩ := (hyx'.symm he).witness he
    exact ⟨W, heW, heW, hW, x', hx', hex', h⟩
  obtain ⟨q₀, hq₀⟩ := exists_mpair he hex hey
  obtain ⟨P₁', hP₁'⟩ := exists_pair F₁ F₂
  obtain ⟨P₀, hP₀⟩ := exists_pair q₀ P₁'
  obtain ⟨T, hP₀T, hT⟩ := exists_transitive_superset he P₀
  have hq₀T : q₀ ∈ T := hT P₀ hP₀T q₀ ((hP₀ q₀).mpr (Or.inl rfl))
  have hPT : P₁' ∈ T := hT P₀ hP₀T P₁' ((hP₀ P₁').mpr (Or.inr rfl))
  have hF₁T : F₁ ∈ T := hT P₁' hPT F₁ ((hP₁' F₁).mpr (Or.inl rfl))
  have hF₂T : F₂ ∈ T := hT P₁' hPT F₂ ((hP₁' F₂).mpr (Or.inr rfl))
  let Good : V → Prop := GoodW e F₁ F₂
  let Rel : V → V → Prop := ExtRel e x y F₁ F₂
  obtain ⟨B, _, hB⟩ := select he T (PairOf e Rel) inferInstance
  have inB : ∀ a b, PairIn e B a b ↔ Rel a b := by
    intro a b
    constructor
    · rintro ⟨q, hq, hqab⟩
      obtain ⟨-, -, a', b', hq', hr⟩ := (hB q).mp ⟨hq, hqab.1⟩
      obtain ⟨rfl, rfl⟩ := hqab.unique hq'
      exact hr
    · intro hr
      have mem : ∀ q, q ∈ T → MPair e q a b → PairIn e B a b := fun q hqT hq =>
        ⟨q, ((hB q).mpr ⟨hqT, hq.1, a, b, hq, hr⟩).1, hq⟩
      rcases hr with ⟨rfl, rfl⟩ | ⟨W, ⟨hWF, _, _⟩, p, hp, hpp⟩
      · exact mem q₀ hq₀T hq₀
      · have hWT : W ∈ T := hWF.elim (fun h => hT F₁ hF₁T W h) (fun h => hT F₂ hF₂T W h)
        exact mem p (hT W hWT p hp) hpp
  have up : ∀ {W a b : V}, Good W → (a = b ∨ PairIn e W a b) → a = b ∨ PairIn e B a b :=
    fun hW h => h.imp id fun h => (inB _ _).mpr (Or.inr ⟨_, hW, h⟩)
  refine Or.inr ⟨B, fun a b hab => ?_, (inB x y).mpr (Or.inl ⟨rfl, rfl⟩)⟩
  rcases (inB a b).mp hab with ⟨rfl, rfl⟩ | ⟨W, hW, hWab⟩
  · refine ⟨fun x' hx' he' => ?_, fun y' hy' he' => ?_⟩
    · obtain ⟨W, hWF, heW, _, hW, y', hy', hey', h⟩ := hF₁c x' hx' (hx x' hx' he')
      exact ⟨y', hy', hey', up ⟨Or.inl hWF, heW, hW⟩ h⟩
    · obtain ⟨W, hWF, heW, _, hW, x', hx', hex', h⟩ := hF₂c y' hy' (hy y' hy' he')
      exact ⟨x', hx', hex', up ⟨Or.inr hWF, heW, hW⟩ h⟩
  · obtain ⟨hf, hb⟩ := hW.2.2 a b hWab
    exact ⟨fun a' ha' he' => (hf a' ha' he').imp fun _ ⟨h1, h2, h3⟩ => ⟨h1, h2, up hW h3⟩,
      fun b' hb' he' => (hb b' hb' he').imp fun _ ⟨h1, h2, h3⟩ => ⟨h1, h2, up hW h3⟩⟩

/-! ## The axioms in `Q` -/

theorem Q.ext {X Y : Q he} (h : ∀ Z : Q he, Z ∈ X ↔ Z ∈ Y) : X = Y := by
  induction X using Q.ind he with
  | h x hx =>
  induction Y using Q.ind he with
  | h y hy =>
  refine (Q.mk_eq_mk he hx hy).mpr (eqv_of_qmem_iff he hx hy fun z hz => ?_)
  exact (Q.mk_mem_mk he hz hx).symm.trans ((h (Q.mk he z hz)).trans (Q.mk_mem_mk he hz hy))

theorem Q.exists_empty : ∃ E : Q he, ∀ Z : Q he, Z ∉ E := by
  obtain ⟨s, hes, hs⟩ := exists_marked_empty he
  refine ⟨Q.mk he s hes, fun Z hZ => ?_⟩
  obtain ⟨z, hz, hzs, -⟩ := (Q.mem_mk_iff he hes).mp hZ
  exact hs z hzs hz

theorem Q.exists_pair (A B : Q he) : ∃ P : Q he, ∀ Z, Z ∈ P ↔ Z = A ∨ Z = B := by
  induction A using Q.ind he with
  | h a ha =>
  induction B using Q.ind he with
  | h b hb =>
  obtain ⟨d, hd⟩ := exists_mdoub he ha hb
  refine ⟨Q.mk he d hd.marked, fun Z => ?_⟩
  rw [Q.mem_mk_iff]
  constructor
  · rintro ⟨z, hz, hzd, rfl⟩
    rcases hd.eq hzd hz with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨a, ha, hd.mem_left.1, rfl⟩
    · exact ⟨b, hb, hd.mem_right.1, rfl⟩

theorem Q.exists_union (X : Q he) : ∃ U : Q he, ∀ Z, Z ∈ U ↔ ∃ Y ∈ X, Z ∈ Y := by
  induction X using Q.ind he with
  | h x hx =>
  obtain ⟨T, hxT, hT⟩ := exists_transitive_superset he x
  obtain ⟨U, heU, hU⟩ := select he T (fun w => ∃ y ∈ x, e ∈ y ∧ w ∈ y) (by definability)
  refine ⟨Q.mk he U heU, fun Z => ?_⟩
  rw [Q.mem_mk_iff]
  constructor
  · rintro ⟨w, hw, hwU, rfl⟩
    obtain ⟨-, -, y, hy, hey, hwy⟩ := (hU w).mp ⟨hwU, hw⟩
    exact ⟨Q.mk he y hey, (Q.mem_mk_iff he hx).mpr ⟨y, hey, hy, rfl⟩,
      (Q.mem_mk_iff he hey).mpr ⟨w, hw, hwy, rfl⟩⟩
  · rintro ⟨Y, hYX, hZY⟩
    obtain ⟨y, hey, hy, rfl⟩ := (Q.mem_mk_iff he hx).mp hYX
    obtain ⟨w, hw, hwy, rfl⟩ := (Q.mem_mk_iff he hey).mp hZY
    have hwT : w ∈ T := hT y (hT x hxT y hy) w hwy
    exact ⟨w, hw, ((hU w).mpr ⟨hwT, hw, y, hy, hey, hwy⟩).1, rfl⟩

theorem Q.exists_power (X : Q he) : ∃ P : Q he, ∀ Y, Y ∈ P ↔ ∀ Z ∈ Y, Z ∈ X := by
  induction X using Q.ind he with
  | h x hx =>
  obtain ⟨D, heD, hD⟩ := exists_enumerator he x
  obtain ⟨Xp, hDX, heX, hxX, hXb⟩ := exists_plus he x D hD
  obtain ⟨Pw, hPw⟩ := exists_powerset he Xp
  obtain ⟨P, heP, hP⟩ :=
    select he Pw (fun v => ∀ t ∈ v, e ∈ t → t ∈ x) (by definability)
  refine ⟨Q.mk he P heP, fun Y => ⟨fun hY Z hZ => ?_, fun hY => ?_⟩⟩
  · obtain ⟨v, hev, hvP, rfl⟩ := (Q.mem_mk_iff he heP).mp hY
    obtain ⟨t, het, htv, rfl⟩ := (Q.mem_mk_iff he hev).mp hZ
    exact (Q.mem_mk_iff he hx).mpr ⟨t, het, ((hP v).mp ⟨hvP, hev⟩).2.2 t htv het, rfl⟩
  induction Y using Q.ind he with
  | h y hy =>
  obtain ⟨s, hes, hsb, hsc⟩ := select_with he x D heD hD (fun w => QMem e w y) (by definability)
  have hsX : s ⊆ Xp := by
    intro v hv
    rcases hsb v hv with h | h | ⟨hvx, _⟩
    · rw [h]; exact hDX
    · rw [h]; exact heX
    · exact hxX v hvx
  have hφs : ∀ t ∈ s, e ∈ t → t ∈ x := by
    intro t ht het
    rcases hsb t ht with h | h | ⟨htx, _⟩
    · exact (heD (h ▸ het)).elim
    · exact (he e (h ▸ het)).elim
    · exact htx
  have hsP : s ∈ P := ((hP s).mpr ⟨hPw s hsX, hes, hφs⟩).1
  have hys : Q.mk he y hy = Q.mk he s hes := by
    apply Q.ext he
    intro Z
    constructor
    · intro hZ
      obtain ⟨w, hew, hwx, rfl⟩ := (Q.mem_mk_iff he hx).mp (hY Z hZ)
      have hq : QMem e w y := (Q.mk_mem_mk he hew hy).mp hZ
      exact (Q.mem_mk_iff he hes).mpr ⟨w, hew, hsc w hwx hew hq, rfl⟩
    · intro hZ
      obtain ⟨w, hew, hws, rfl⟩ := (Q.mem_mk_iff he hes).mp hZ
      rcases hsb w hws with h | h | ⟨_, _, hq⟩
      · exact (heD (h ▸ hew)).elim
      · exact (he e (h ▸ hew)).elim
      · exact (Q.mk_mem_mk he hew hy).mpr hq
  rw [hys]
  exact (Q.mem_mk_iff he heP).mpr ⟨s, hes, hsP, rfl⟩

/-- Separation, for predicates whose pullback to marked objects is definable. -/
theorem Q.exists_sep (X : Q he) (P : Q he → Prop)
    (hP : ℒₛₑₜ-predicate (fun w : V => ∃ hw : e ∈ w, P (Q.mk he w hw))) :
    ∃ S : Q he, ∀ Z, Z ∈ S ↔ Z ∈ X ∧ P Z := by
  induction X using Q.ind he with
  | h x hx =>
  obtain ⟨S, heS, hS⟩ := select he x (fun w => ∃ hw : e ∈ w, P (Q.mk he w hw)) hP
  refine ⟨Q.mk he S heS, fun Z => ⟨fun hZ => ?_, fun ⟨hZ, hPZ⟩ => ?_⟩⟩
  · obtain ⟨w, hew, hwS, rfl⟩ := (Q.mem_mk_iff he heS).mp hZ
    obtain ⟨hwx, -, _, hPw⟩ := (hS w).mp ⟨hwS, hew⟩
    exact ⟨(Q.mem_mk_iff he hx).mpr ⟨w, hew, hwx, rfl⟩, hPw⟩
  · obtain ⟨w, hew, hwx, rfl⟩ := (Q.mem_mk_iff he hx).mp hZ
    exact (Q.mem_mk_iff he heS).mpr ⟨w, hew, ((hS w).mpr ⟨hwx, hew, hew, hPZ⟩).1, rfl⟩

/-- Replacement for functional relations, in the partial form of the Challenge,
for relations whose pullback to marked objects is definable. -/
theorem Q.exists_repl (X : Q he) (F : Q he → Q he → Prop)
    (hF : ℒₛₑₜ-relation (fun w v : V =>
      ∃ hw : e ∈ w, ∃ hv : e ∈ v, F (Q.mk he w hw) (Q.mk he v hv)))
    (hfun : ∀ A B C, F A B → F A C → B = C) :
    ∃ R : Q he, ∀ Z, Z ∈ R ↔ ∃ A ∈ X, F A Z := by
  induction X using Q.ind he with
  | h x hx =>
  obtain ⟨C, heC, hCs, hCc⟩ := collect he x _ hF
  refine ⟨Q.mk he C heC, fun Z => ⟨fun hZ => ?_, fun ⟨A, hAX, hAZ⟩ => ?_⟩⟩
  · obtain ⟨v, hev, hvC, rfl⟩ := (Q.mem_mk_iff he heC).mp hZ
    obtain ⟨w, hwx, hew, _, hF'⟩ := hCs v hvC hev
    exact ⟨Q.mk he w hew, (Q.mem_mk_iff he hx).mpr ⟨w, hew, hwx, rfl⟩, hF'⟩
  · obtain ⟨w, hew, hwx, rfl⟩ := (Q.mem_mk_iff he hx).mp hAX
    induction Z using Q.ind he with
    | h z hz =>
    obtain ⟨v, hvC, hev, _, _, hF'⟩ := hCc w hwx ⟨z, hz, hew, hz, hAZ⟩
    rw [hfun _ _ _ hAZ hF']
    exact (Q.mem_mk_iff he heC).mpr ⟨v, hev, hvC, rfl⟩

end ZF209.GateModel
