module
public import ZF192Support.SetTheory.GateModel.Interp
public import Foundation.FirstOrder.SetTheory.ZF.Basic
@[expose] public section
/-! # The well-founded part of a model of ZF without Foundation

`ZFMinus` states, semantically, the ZF axioms other than Foundation, with
Separation and Replacement for definable predicates, plus the existence of a
transitive set containing any given set. The elements lying in a transitive,
well-founded set then form a model of Foundation's `𝗭𝗙`. -/
namespace ZF192Support.GateModel
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

/-- ZF without Foundation, together with transitive supersets. -/
class ZFMinus (M : Type*) [SetStructure M] : Prop where
  ext : ∀ x y : M, (∀ z, z ∈ x ↔ z ∈ y) → x = y
  empty : ∃ e : M, ∀ z, z ∉ e
  pair : ∀ a b : M, ∃ p : M, ∀ z, z ∈ p ↔ z = a ∨ z = b
  union : ∀ x : M, ∃ u : M, ∀ z, z ∈ u ↔ ∃ y ∈ x, z ∈ y
  power : ∀ x : M, ∃ p : M, ∀ y, y ∈ p ↔ ∀ z ∈ y, z ∈ x
  sep : ∀ P : M → Prop, (ℒₛₑₜ-predicate P) → ∀ x : M, ∃ s : M, ∀ z, z ∈ s ↔ z ∈ x ∧ P z
  repl : ∀ F : M → M → Prop, (ℒₛₑₜ-relation F) → (∀ a b c, F a b → F a c → b = c) →
    ∀ x : M, ∃ r : M, ∀ z, z ∈ r ↔ ∃ a ∈ x, F a z
  infinity : ∃ I : M, (∃ e ∈ I, ∀ z, z ∉ e) ∧
    ∀ x ∈ I, ∃ s ∈ I, ∀ z, z ∈ s ↔ z = x ∨ z ∈ x
  trans : ∀ x : M, ∃ T : M, x ∈ T ∧ ∀ y ∈ T, ∀ z ∈ y, z ∈ T

variable {M : Type*} [SetStructure M]

/-- `T` is transitive. -/
def IsTransSet (T : M) : Prop := ∀ y ∈ T, ∀ z ∈ y, z ∈ T

/-- Every nonempty subset of `T` has a membership-minimal element. -/
def IsWFdSet (T : M) : Prop :=
  ∀ S : M, (∀ z ∈ S, z ∈ T) → (∃ z, z ∈ S) → ∃ m ∈ S, ∀ z ∈ S, z ∉ m

/-- `x` lies in a transitive, well-founded set. -/
def IsWF (x : M) : Prop := ∃ T : M, x ∈ T ∧ IsTransSet T ∧ IsWFdSet T

instance IsTransSet.definable : ℒₛₑₜ-predicate (IsTransSet (M := M)) := by
  unfold IsTransSet; definability

instance IsWFdSet.definable : ℒₛₑₜ-predicate (IsWFdSet (M := M)) := by
  unfold IsWFdSet; definability

instance IsWF.definable : ℒₛₑₜ-predicate (IsWF (M := M)) := by
  unfold IsWF; definability

lemma IsWF.mem {x y : M} (hy : IsWF y) (hx : x ∈ y) : IsWF x := by
  obtain ⟨T, hyT, hT, hW⟩ := hy
  exact ⟨T, hT y hyT x hx, hT, hW⟩

variable [ZFMinus M]

/-- A set all of whose members are well-founded is well-founded. -/
lemma IsWF.of_forall_mem {x : M} (h : ∀ y ∈ x, IsWF y) : IsWF x := by
  obtain ⟨T₀, hxT₀, hT₀⟩ := ZFMinus.trans x
  obtain ⟨W, hW⟩ := ZFMinus.sep IsWF inferInstance T₀
  have hWtrans : IsTransSet W := by
    intro y hy z hz
    obtain ⟨hyT, hyW⟩ := (hW y).mp hy
    exact (hW z).mpr ⟨hT₀ y hyT z hz, hyW.mem hz⟩
  have hWwf : IsWFdSet W := by
    rintro S hS ⟨z, hz⟩
    obtain ⟨-, T, hzT, hT, hTw⟩ := (hW z).mp (hS z hz)
    obtain ⟨S', hS'⟩ := ZFMinus.sep (fun s => s ∈ T) (by definability) S
    by_cases hne : ∃ s, s ∈ S'
    · obtain ⟨m, hm, hmin⟩ := hTw S' (fun s hs => ((hS' s).mp hs).2) hne
      obtain ⟨hmS, hmT⟩ := (hS' m).mp hm
      exact ⟨m, hmS, fun w hw hwm => hmin w ((hS' w).mpr ⟨hw, hT m hmT w hwm⟩) hwm⟩
    · exact ⟨z, hz, fun w hw hwz => hne ⟨w, (hS' w).mpr ⟨hw, hT z hzT w hwz⟩⟩⟩
  obtain ⟨sx, hsx⟩ := ZFMinus.pair x x
  obtain ⟨pr, hpr⟩ := ZFMinus.pair W sx
  obtain ⟨T, hT⟩ := ZFMinus.union pr
  have hTm : ∀ z, z ∈ T ↔ z ∈ W ∨ z = x := by
    intro z
    rw [hT]
    constructor
    · rintro ⟨y, hy, hzy⟩
      rcases (hpr y).mp hy with rfl | rfl
      · exact Or.inl hzy
      · exact Or.inr (((hsx z).mp hzy).elim id id)
    · rintro (hz | rfl)
      · exact ⟨W, (hpr W).mpr (Or.inl rfl), hz⟩
      · exact ⟨sx, (hpr sx).mpr (Or.inr rfl), (hsx z).mpr (Or.inl rfl)⟩
  have hxW : ∀ y ∈ x, y ∈ W := fun y hy => (hW y).mpr ⟨hT₀ x hxT₀ y hy, h y hy⟩
  refine ⟨T, (hTm x).mpr (Or.inr rfl), ?_, ?_⟩
  · intro y hy z hz
    rcases (hTm y).mp hy with hy | rfl
    · exact (hTm z).mpr (Or.inl (hWtrans y hy z hz))
    · exact (hTm z).mpr (Or.inl (hxW z hz))
  · intro S hS hne
    obtain ⟨S', hS'⟩ := ZFMinus.sep (fun s => s ∈ W) (by definability) S
    by_cases hne' : ∃ s, s ∈ S'
    · obtain ⟨m, hm, hmin⟩ := hWwf S' (fun s hs => ((hS' s).mp hs).2) hne'
      obtain ⟨hmS, hmW⟩ := (hS' m).mp hm
      exact ⟨m, hmS, fun w hw hwm => hmin w ((hS' w).mpr ⟨hw, hWtrans m hmW w hwm⟩) hwm⟩
    · obtain ⟨z, hz⟩ := hne
      have hzx : z = x := by
        rcases (hTm z).mp (hS z hz) with hzW | hzx
        · exact (hne' ⟨z, (hS' z).mpr ⟨hz, hzW⟩⟩).elim
        · exact hzx
      subst hzx
      exact ⟨z, hz, fun w hw hwz => hne' ⟨w, (hS' w).mpr ⟨hw, hxW w hwz⟩⟩⟩

variable (M) in
/-- The well-founded part. -/
def WFPart := {x : M // IsWF x}

instance : SetStructure (WFPart M) := ⟨fun Y X => X.1 ∈ Y.1⟩

lemma WFPart.mem_iff {X Y : WFPart M} : X ∈ Y ↔ X.1 ∈ Y.1 := Iff.rfl

lemma exists_wf_empty : ∃ e : M, IsWF e ∧ ∀ z, z ∉ e := by
  obtain ⟨e, he⟩ := ZFMinus.empty (M := M)
  exact ⟨e, IsWF.of_forall_mem fun y hy => (he y hy).elim, he⟩

instance : Nonempty (WFPart M) :=
  let ⟨e, he, _⟩ := exists_wf_empty (M := M); ⟨⟨e, he⟩⟩

open Classical in
/-- The inclusion of the well-founded part, read as an interpretation. -/
noncomputable def wfInterp : Interp M (WFPart M) where
  dom := IsWF
  π x := if h : IsWF x then ⟨x, h⟩ else Classical.arbitrary _
  surj Y := ⟨Y.1, Y.2, by simp [Y.2]; rfl⟩
  mem x y := x ∈ y
  mem_iff x y hx hy := by simp [hx, hy]; exact Iff.rfl
  eq x y := x = y
  eq_iff x y hx hy := by
    simp [hx, hy]
    exact ⟨fun h => by subst h; rfl, fun h => congrArg Subtype.val h⟩
  dom_def := inferInstance
  mem_def := by definability
  eq_def := by definability

lemma wfInterp_π {x : M} (hx : IsWF x) : (wfInterp (M := M)).π x = ⟨x, hx⟩ := by
  simp only [wfInterp]
  exact dif_pos hx

/-- Definable predicates on the well-founded part pull back to definable predicates. -/
lemma wf_pullback_pred {P : WFPart M → Prop} (hP : ℒₛₑₜ-predicate P) :
    ℒₛₑₜ-predicate (fun x : M => ∃ h : IsWF x, P ⟨x, h⟩) :=
  Language.Definable.of_iff ((wfInterp (M := M)).pullback_pred hP) fun v =>
    ⟨fun ⟨h, hp⟩ => ⟨h, by rw [wfInterp_π h]; exact hp⟩,
     fun ⟨h, hp⟩ => ⟨h, by rw [wfInterp_π h] at hp; exact hp⟩⟩

lemma wf_pullback_rel {R : WFPart M → WFPart M → Prop} (hR : ℒₛₑₜ-relation R) :
    ℒₛₑₜ-relation (fun x y : M => ∃ (hx : IsWF x) (hy : IsWF y), R ⟨x, hx⟩ ⟨y, hy⟩) :=
  Language.Definable.of_iff ((wfInterp (M := M)).pullback_rel hR) fun v =>
    ⟨fun ⟨hx, hy, hr⟩ => ⟨hx, hy, by rw [wfInterp_π hx, wfInterp_π hy]; exact hr⟩,
     fun ⟨hx, hy, hr⟩ => ⟨hx, hy, by rw [wfInterp_π hx, wfInterp_π hy] at hr; exact hr⟩⟩

/-! ## The axioms in the well-founded part -/

namespace WFPart

lemma ext {X Y : WFPart M} (h : ∀ Z : WFPart M, Z ∈ X ↔ Z ∈ Y) : X = Y :=
  Subtype.ext <| ZFMinus.ext X.1 Y.1 fun z =>
    ⟨fun hz => (h ⟨z, X.2.mem hz⟩).mp hz, fun hz => (h ⟨z, Y.2.mem hz⟩).mpr hz⟩

lemma exists_empty : ∃ E : WFPart M, ∀ Z : WFPart M, Z ∉ E :=
  let ⟨e, he, hz⟩ := exists_wf_empty (M := M); ⟨⟨e, he⟩, fun Z => hz Z.1⟩

lemma exists_pair (A B : WFPart M) : ∃ P : WFPart M, ∀ Z, Z ∈ P ↔ Z = A ∨ Z = B := by
  obtain ⟨p, hp⟩ := ZFMinus.pair A.1 B.1
  have hwf : IsWF p := IsWF.of_forall_mem fun y hy => by
    rcases (hp y).mp hy with rfl | rfl
    · exact A.2
    · exact B.2
  refine ⟨⟨p, hwf⟩, fun Z => ⟨fun hZ => ((hp Z.1).mp hZ).imp Subtype.ext Subtype.ext,
    fun h => (hp Z.1).mpr (h.imp (congrArg Subtype.val) (congrArg Subtype.val))⟩⟩

lemma exists_union (X : WFPart M) : ∃ U : WFPart M, ∀ Z, Z ∈ U ↔ ∃ Y ∈ X, Z ∈ Y := by
  obtain ⟨u, hu⟩ := ZFMinus.union X.1
  have hwf : IsWF u := IsWF.of_forall_mem fun z hz => by
    obtain ⟨y, hy, hzy⟩ := (hu z).mp hz
    exact (X.2.mem hy).mem hzy
  refine ⟨⟨u, hwf⟩, fun Z => ⟨fun hZ => ?_, fun ⟨Y, hY, hZY⟩ => (hu Z.1).mpr ⟨Y.1, hY, hZY⟩⟩⟩
  obtain ⟨y, hy, hzy⟩ := (hu Z.1).mp hZ
  exact ⟨⟨y, X.2.mem hy⟩, hy, hzy⟩

lemma exists_power (X : WFPart M) : ∃ P : WFPart M, ∀ Y, Y ∈ P ↔ ∀ Z ∈ Y, Z ∈ X := by
  obtain ⟨p, hp⟩ := ZFMinus.power X.1
  have hsub : ∀ y ∈ p, IsWF y := fun y hy =>
    IsWF.of_forall_mem fun z hz => X.2.mem ((hp y).mp hy z hz)
  refine ⟨⟨p, IsWF.of_forall_mem hsub⟩, fun Y => ⟨fun hY Z hZ => (hp Y.1).mp hY Z.1 hZ,
    fun hY => (hp Y.1).mpr fun z hz => hY ⟨z, Y.2.mem hz⟩ hz⟩⟩

lemma foundation (X : WFPart M) (hX : ∃ Z, Z ∈ X) : ∃ Y ∈ X, ∀ Z ∈ X, Z ∉ Y := by
  obtain ⟨T, hXT, hT, hTw⟩ := X.2
  obtain ⟨Z, hZ⟩ := hX
  obtain ⟨m, hm, hmin⟩ := hTw X.1 (fun z hz => hT X.1 hXT z hz) ⟨Z.1, hZ⟩
  exact ⟨⟨m, X.2.mem hm⟩, hm, fun W hW => hmin W.1 hW⟩

lemma exists_sep (X : WFPart M) (P : WFPart M → Prop) (hP : ℒₛₑₜ-predicate P) :
    ∃ S : WFPart M, ∀ Z, Z ∈ S ↔ Z ∈ X ∧ P Z := by
  obtain ⟨s, hs⟩ := ZFMinus.sep _ (wf_pullback_pred hP) X.1
  have hwf : IsWF s := IsWF.of_forall_mem fun z hz => X.2.mem ((hs z).mp hz).1
  refine ⟨⟨s, hwf⟩, fun Z => ⟨fun hZ => ?_, fun ⟨hZ, hPZ⟩ => (hs Z.1).mpr ⟨hZ, Z.2, hPZ⟩⟩⟩
  obtain ⟨hzx, _, hPz⟩ := (hs Z.1).mp hZ
  exact ⟨hzx, hPz⟩

lemma exists_repl (X : WFPart M) (F : WFPart M → WFPart M → Prop) (hF : ℒₛₑₜ-relation F)
    (hfun : ∀ A B C, F A B → F A C → B = C) :
    ∃ R : WFPart M, ∀ Z, Z ∈ R ↔ ∃ A ∈ X, F A Z := by
  obtain ⟨r, hr⟩ := ZFMinus.repl _ (wf_pullback_rel hF) (fun a b c ⟨ha, hb, h₁⟩ ⟨ha', hc, h₂⟩ =>
    congrArg Subtype.val (hfun _ _ _ h₁ h₂)) X.1
  have hwf : IsWF r := IsWF.of_forall_mem fun z hz => by
    obtain ⟨_, _, _, hz', _⟩ := (hr z).mp hz
    exact hz'
  refine ⟨⟨r, hwf⟩, fun Z => ⟨fun hZ => ?_, fun ⟨A, hA, hAZ⟩ => (hr Z.1).mpr ⟨A.1, hA, A.2, Z.2, hAZ⟩⟩⟩
  obtain ⟨a, ha, hwa, _, hF'⟩ := (hr Z.1).mp hZ
  exact ⟨⟨a, hwa⟩, ha, hF'⟩

lemma exists_inductive : ∃ I : WFPart M, (∀ E : WFPart M, (∀ Z, Z ∉ E) → E ∈ I) ∧
    ∀ X ∈ I, ∀ X' : WFPart M, (∀ Z, Z ∈ X' ↔ Z = X ∨ Z ∈ X) → X' ∈ I := by
  obtain ⟨I₀, ⟨e₀, he₀I, he₀⟩, hI₀⟩ := ZFMinus.infinity (M := M)
  obtain ⟨i, hi⟩ := ZFMinus.sep IsWF inferInstance I₀
  have hwf : IsWF i := IsWF.of_forall_mem fun z hz => ((hi z).mp hz).2
  refine ⟨⟨i, hwf⟩, fun E hE => ?_, fun X hX X' hX' => ?_⟩
  · have : E.1 = e₀ := ZFMinus.ext _ _ fun z =>
      ⟨fun hz => (hE ⟨z, E.2.mem hz⟩ hz).elim, fun hz => (he₀ z hz).elim⟩
    exact (hi E.1).mpr ⟨this ▸ he₀I, E.2⟩
  · obtain ⟨hXI₀, -⟩ := (hi X.1).mp hX
    obtain ⟨s, hsI₀, hs⟩ := hI₀ X.1 hXI₀
    have : X'.1 = s := ZFMinus.ext _ _ fun z => by
      constructor
      · intro hz
        rcases (hX' ⟨z, X'.2.mem hz⟩).mp hz with h | h
        · exact (hs z).mpr (Or.inl (congrArg Subtype.val h))
        · exact (hs z).mpr (Or.inr h)
      · intro hz
        rcases (hs z).mp hz with h | h
        · subst h; exact (hX' X).mpr (Or.inl rfl)
        · exact (hX' ⟨z, X.2.mem h⟩).mpr (Or.inr h)
    exact (hi X'.1).mpr ⟨this ▸ hsI₀, X'.2⟩

end WFPart

end ZF192Support.GateModel
