module
public import ZF192Support.SetTheory.GateModel.CodeBridge
public import ZF192Support.Independence.Interpretation.Relativization
@[expose] public section
/-! # The marked interpretation of ZF

The interpretation uses the membership-indiscernibility quotient, the marked
bisimilarity quotient at an empty object, and its well-founded part. -/
namespace ZF192Support.Independence
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory ZF192Support.GateModel

/-! ## Formulas for the marked quotient (read in any set structure) -/

def msingF : Semisentence ℒₛₑₜ 3 := “e s a. e ∈ s ∧ ∀ t, ((t ∈ s ∧ e ∈ t) ↔ t = a)”
def mdoubF : Semisentence ℒₛₑₜ 4 :=
  “e s a b. e ∈ s ∧ ∀ t, ((t ∈ s ∧ e ∈ t) ↔ (t = a ∨ t = b))”
def mpairF : Semisentence ℒₛₑₜ 4 :=
  “e p a b. e ∈ p ∧ (∀ t, t ∈ p → e ∈ t → (!msingF e t a ∨ !mdoubF e t a b)) ∧
    (∃ t, t ∈ p ∧ !msingF e t a) ∧ ∃ t, t ∈ p ∧ !mdoubF e t a b”
def pairInF : Semisentence ℒₛₑₜ 4 := “e B a b. ∃ p, p ∈ B ∧ !mpairF e p a b”
def backForthF : Semisentence ℒₛₑₜ 4 :=
  “e B x y. (∀ x', x' ∈ x → e ∈ x' → ∃ y', y' ∈ y ∧ e ∈ y' ∧ (x' = y' ∨ !pairInF e B x' y')) ∧
    ∀ y', y' ∈ y → e ∈ y' → ∃ x', x' ∈ x ∧ e ∈ x' ∧ (x' = y' ∨ !pairInF e B x' y')”
def bisimF : Semisentence ℒₛₑₜ 2 :=
  “e B. ∀ x y, !pairInF e B x y → !backForthF e B x y”
def eqvF : Semisentence ℒₛₑₜ 3 := “e x y. x = y ∨ ∃ B, !bisimF e B ∧ !pairInF e B x y”
def qmemF : Semisentence ℒₛₑₜ 3 := “e x y. ∃ z, z ∈ y ∧ e ∈ z ∧ !eqvF e x z”

section Defined
variable {V : Type*} [SetStructure V]

instance MSing.defined : ℒₛₑₜ-relation₃[V] MSing via msingF :=
  ⟨fun v => by simp [msingF, MSing]⟩
instance MDoub.defined : ℒₛₑₜ-relation₄[V] MDoub via mdoubF :=
  ⟨fun v => by simp [mdoubF, MDoub]⟩
instance MPair.defined : ℒₛₑₜ-relation₄[V] MPair via mpairF :=
  ⟨fun v => by simp [mpairF, MPair]⟩
instance PairIn.defined : ℒₛₑₜ-relation₄[V] PairIn via pairInF :=
  ⟨fun v => by simp [pairInF, PairIn]⟩
instance BackForth.defined : ℒₛₑₜ-relation₄[V] BackForth via backForthF :=
  ⟨fun v => by simp [backForthF, BackForth]⟩
instance Bisim.defined : ℒₛₑₜ-relation[V] Bisim via bisimF :=
  ⟨fun v => by simp [bisimF, Bisim]⟩
instance Eqv.defined : ℒₛₑₜ-relation₃[V] Eqv via eqvF :=
  ⟨fun v => by simp [eqvF, Eqv]⟩
instance QMem.defined : ℒₛₑₜ-relation₃[V] QMem via qmemF :=
  ⟨fun v => by simp [qmemF, QMem]⟩

end Defined

/-! ## Formulas for the well-founded part and for indiscernibility -/

def isTransF : Semisentence ℒₛₑₜ 1 := “T. ∀ y, y ∈ T → ∀ z, z ∈ y → z ∈ T”
def isWFdF : Semisentence ℒₛₑₜ 1 :=
  “T. ∀ S, (∀ z, z ∈ S → z ∈ T) → (∃ z, z ∈ S) → ∃ m, m ∈ S ∧ ∀ z, z ∈ S → z ∉ m”
def isWFF : Semisentence ℒₛₑₜ 1 := “x. ∃ T, x ∈ T ∧ !isTransF T ∧ !isWFdF T”
def indiscF : Semisentence ℒₛₑₜ 2 := “x y. ∀ z, (z ∈ x ↔ z ∈ y) ∧ (x ∈ z ↔ y ∈ z)”
def emptyF : Semisentence ℒₛₑₜ 1 := “e. ∀ y, y ∉ e”

section Defined2
variable {V : Type*} [SetStructure V]

instance IsTransSet.defined : ℒₛₑₜ-predicate[V] IsTransSet via isTransF :=
  ⟨fun v => by simp [isTransF, IsTransSet]⟩
instance IsWFdSet.defined : ℒₛₑₜ-predicate[V] IsWFdSet via isWFdF :=
  ⟨fun v => by simp [isWFdF, IsWFdSet]⟩
instance IsWF.defined : ℒₛₑₜ-predicate[V] IsWF via isWFF :=
  ⟨fun v => by simp [isWFF, IsWF]⟩

lemma eval_indiscF (x y : V) : V ⊧/![x, y] indiscF ↔ Indisc (fun a b : V => a ∈ b) x y := by
  simp [indiscF, Indisc]

end Defined2

/-! ## The three interpretations -/

def dNQ : RelData0 := ⟨“x. ⊤”, “x y. x ∈ y”, indiscF⟩
def dQ : RelData1 := ⟨“x e. e ∈ x”, “x y e. !qmemF e x y”, “x y e. !eqvF e x y”⟩
def dWF : RelData0 := ⟨isWFF, “x y. x ∈ y”, “x y. x = y”⟩

section Meaning
variable {W : Type*} [SetStructure W] [Nonempty W]

lemma sem_dNQ : Sem0 dNQ (cls (fun x y : W => x ∈ y)) where
  surj y := let ⟨x, hx⟩ := cls_surj _ y; ⟨x, by simp [dNQ], hx⟩
  mem x y _ _ := by simp [dNQ]; rfl
  eq x y _ _ := by
    show W ⊧/![x, y] indiscF ↔ _
    rw [eval_indiscF, cls_eq]

variable [GateHull (NQ (fun x y : W => x ∈ y))]

lemma sem_dQ {e : NQ (fun x y : W => x ∈ y)} (he : SetTheory.IsEmpty e) :
    Sem1 dQ e (Q.cls he) := by
  have hdom : ∀ z, (NQ (fun x y : W => x ∈ y)) ⊧/![z, e] dQ.dom ↔ e ∈ z := fun z => by simp [dQ]
  have hmem : ∀ x y, (NQ (fun x y : W => x ∈ y)) ⊧/![x, y, e] dQ.mem ↔ QMem e x y :=
    fun x y => by simp [dQ]
  have heq : ∀ x y, (NQ (fun x y : W => x ∈ y)) ⊧/![x, y, e] dQ.eq ↔ Eqv e x y :=
    fun x y => by simp [dQ]
  refine ⟨fun y => ?_, fun x y hx hy => ?_, fun x y hx hy => ?_⟩
  · obtain ⟨x, hx, hxy⟩ := (qInterp he).surj y
    exact ⟨x, (hdom x).mpr hx, hxy⟩
  · rw [hmem]; exact (qInterp he).mem_iff x y ((hdom x).mp hx) ((hdom y).mp hy)
  · rw [heq]; exact (qInterp he).eq_iff x y ((hdom x).mp hx) ((hdom y).mp hy)

lemma sem_dWF {e : NQ (fun x y : W => x ∈ y)} (he : SetTheory.IsEmpty e) :
    Sem0 dWF (wfInterp (M := Q he)).π := by
  have hdom : ∀ z : Q he, (Q he) ⊧/![z] dWF.dom ↔ IsWF z := fun z => by simp [dWF]
  have hmem : ∀ x y : Q he, (Q he) ⊧/![x, y] dWF.mem ↔ x ∈ y := fun x y => by simp [dWF]
  have heq : ∀ x y : Q he, (Q he) ⊧/![x, y] dWF.eq ↔ x = y := fun x y => by simp [dWF]
  refine ⟨fun y => ?_, fun x y hx hy => ?_, fun x y hx hy => ?_⟩
  · obtain ⟨x, hx, hxy⟩ := (wfInterp (M := Q he)).surj y
    exact ⟨x, (hdom x).mpr hx, hxy⟩
  · rw [hmem]; exact (wfInterp (M := Q he)).mem_iff x y ((hdom x).mp hx) ((hdom y).mp hy)
  · rw [heq]; exact (wfInterp (M := Q he)).eq_iff x y ((hdom x).mp hx) ((hdom y).mp hy)

end Meaning

/-! ## Transport of pointed hulls -/

variable {W : Type} [SetStructure W] [Nonempty W]
local notation "N" => NQ (fun x y : W => x ∈ y)
local notation "q" => cls (fun x y : W => x ∈ y)

/-- Definability pulls back through the existing interpretation of the quotient. -/
private theorem quotient_pullback {R : N → N → Prop} (hR : ℒₛₑₜ-relation R) :
    ℒₛₑₜ-relation (fun a b : W => R (q a) (q b)) := by
  classical
  obtain ⟨φ, hφ⟩ := hR.definable
  let rep : N → W := fun p => (cls_surj _ p).choose
  have hrep : q ∘ rep = id := funext fun p => (cls_surj _ p).choose_spec
  refine ⟨⟨rel0 dNQ (Rew.rewriteMap rep ▹ φ), ?_⟩⟩
  intro v
  have sem := eval_rel0 (sem_dNQ (W := W)) (Rew.rewriteMap rep ▹ φ) v id
    (fun i => by simp [dNQ]) (fun x => by simp [dNQ])
  rw [Semiformula.eval_rewriteMap, Function.comp_id] at sem
  change _ ↔ φ.Eval (q ∘ v) (q ∘ rep) at sem
  rw [hrep] at sem
  exact sem.trans (hφ _)

/-- Pointed hulls descend through membership indiscernibility. -/
theorem gateHull_of_ambient (h : GateHull W) : GateHull N := by
  refine ⟨?_⟩
  intro R hR U V
  obtain ⟨u, rfl⟩ := cls_surj _ U
  obtain ⟨v, rfl⟩ := cls_surj _ V
  obtain ⟨C, hstart, hC⟩ := h.hull _ (quotient_pullback hR) u v
  refine ⟨q C, hstart, ?_⟩
  intro Z hz
  obtain ⟨z, rfl⟩ := cls_surj _ Z
  obtain ⟨⟨p, hp⟩, hcov⟩ := hC z hz
  refine ⟨⟨q p, hp⟩, ?_⟩
  intro U hU hv
  obtain ⟨u, rfl⟩ := cls_surj _ U
  obtain ⟨V, hUV⟩ := hv
  obtain ⟨v, rfl⟩ := cls_surj _ V
  obtain ⟨w, hw, hUw⟩ := hcov u (fun x hu => hU (q x) hu) ⟨v, hUV⟩
  exact ⟨q w, hw, hUw⟩


end ZF192Support.Independence
