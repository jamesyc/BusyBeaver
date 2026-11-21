module
public import I0451.Logic.TruthFamily
public import I0451.Logic.NaturalBounds

/-! Every generated relation ignores all sufficiently high natural
variable labels. This is an internal bound in the set model's omega.
It supplies fresh labels for implication and quantification. -/
@[expose] public section
namespace I0451.Logic.SetAssignments

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open I0451.AssignmentCode
open I0451.Logic.ZFModel (common_nat_bound avoid_nat_label)

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

local notation "E" => (fun (x y : V) => x ∈ y)

def SameExcept (d i g h : V) : Prop :=
  ∀ k ∈ d, k ≠ i → ∀ x, At E g k x ↔ At E h k x

def IndependentAt (d U R i : V) : Prop :=
  ∀ g ∈ U, ∀ h ∈ U, SameExcept d i g h → (g ∈ R ↔ h ∈ R)

def HasClockBound (d U R : V) : Prop :=
  ∃ n ∈ (ω : V), ∀ i ∈ (ω : V), i ∉ n → IndependentAt d U R i

def sameExceptDef : SetTheorySemisentence 4 :=
  “d i g h. ∀ k ∈ d, k ≠ i → ∀ x, !atDef g k x ↔ !atDef h k x”

theorem eval_sameExceptDef (d i g h : V) :
    sameExceptDef.Evalb ![d,i,g,h] ↔ SameExcept d i g h := by
  have evalAt (g k x : V) :
      atDef.Eval (g :> k :> fun _ : Fin 1 => x) Empty.elim ↔ At E g k x := by
    simpa only [Matrix.vec_single_eq_const] using eval_atDef g k x
  simp [sameExceptDef, SameExcept, evalAt, Matrix.comp_vecCons', Function.comp_def]

def independentAtDef : SetTheorySemisentence 4 :=
  “d U R i. ∀ g ∈ U, ∀ h ∈ U, !sameExceptDef d i g h → (g ∈ R ↔ h ∈ R)”

theorem eval_independentAtDef (d U R i : V) :
    independentAtDef.Evalb ![d,U,R,i] ↔ IndependentAt d U R i := by
  have eval (d i g h : V) :
      sameExceptDef.Eval (d :> i :> g :> fun _ : Fin 1 => h) Empty.elim ↔ SameExcept d i g h := by
    simpa only [Matrix.vec_single_eq_const] using eval_sameExceptDef d i g h
  simp [independentAtDef, IndependentAt, eval, Matrix.comp_vecCons', Function.comp_def]

def clockBoundDef : SetTheorySemisentence 3 :=
  “R d U. ∃ w, !isω w ∧ ∃ n ∈ w, ∀ i ∈ w, i ∉ n → !independentAtDef d U R i”

theorem eval_clockBoundDef (R d U : V) :
    clockBoundDef.Evalb ![R,d,U] ↔ HasClockBound d U R := by
  have eval (d U R i : V) :
      independentAtDef.Eval (d :> U :> R :> fun _ : Fin 1 => i) Empty.elim ↔ IndependentAt d U R i := by
    simpa only [Matrix.vec_single_eq_const] using eval_independentAtDef d U R i
  simp [clockBoundDef, HasClockBound, eval, Matrix.comp_vecCons', Function.comp_def]

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem SameExcept.symm {d i g h : V} (hEq : SameExcept d i g h) : SameExcept d i h g :=
  fun k hk different x => (hEq k hk different x).symm

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
theorem decoded_eq {d i g h : V} {f k : Domain E d → Domain E d}
    (gCode : Encodes E d g f) (hCode : Encodes E d h k) (same : SameExcept d i g h)
    (x : Domain E d) (different : x.val ≠ i) : f x = k x :=
  Subtype.ext (((hCode.at_iff x _).mp ((same x.val x.property different _).mp
    ((gCode.at_iff x _).mpr rfl))).symm)

omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] in
private theorem sameExcept_of_decoded {d i g h : V} {f k : Domain E d → Domain E d}
    (gCode : Encodes E d g f) (hCode : Encodes E d h k)
    (same : ∀ x : Domain E d, x.val ≠ i → f x = k x) : SameExcept d i g h := by
  intro x hx diff y
  let index : Domain E d := ⟨x, hx⟩
  exact (gCode.at_iff index y).trans ((by rw [same index diff] :
    (f index).val = y ↔ (k index).val = y).trans (hCode.at_iff index y).symm)

theorem atom_independent {d U i j k : V} (di : i ∈ d) (dj : j ∈ d) (ki : i ≠ k) (kj : j ≠ k) :
    IndependentAt d U (atomicSet U i j) k := by
  intro g gU h hU agree
  rw [mem_atomicSet, mem_atomicSet, and_iff_right gU, and_iff_right hU, AtomTrace, AtomTrace]
  simp only [agree i di ki, agree j dj kj]

theorem step_independent {d i R S k : V} (hi : i ∈ d)
    (left : IndependentAt d (assignments d) R k) (right : IndependentAt d (assignments d) S k) :
    IndependentAt d (assignments d) (stepSet (assignments d) i R S) k := by
  classical
  let U := assignments d
  let index : Domain E d := ⟨i, hi⟩
  let ops := ZFModel.setOperations (V := V)
  have decode (a : V) (member : a ∈ U) : ∃ f, Encodes E d a f :=
    (is_map_iff_encodes ops).mp ((mem_universe d a).mp member)
  have move (g h : V) (gU : g ∈ U) (hU : h ∈ U) (together : SameExcept d k g h) :
      StepTrace g U i R S → StepTrace h U i R S := by
    rintro ⟨u, uU, condition, changeI⟩
    obtain ⟨f, gCode⟩ := decode g gU
    obtain ⟨p, uCode⟩ := decode u uU
    obtain ⟨q, hCode⟩ := decode h hU
    obtain ⟨w, wCode, newI⟩ := hCode.replace ops index (p index)
    have wU : w ∈ U := (mem_universe d _).mpr ((is_map_iff_encodes ops).mpr ⟨_, wCode⟩)
    have sameCode : SameExcept d k u w := by
      apply sameExcept_of_decoded uCode wCode
      intro x different
      by_cases changed : x = index
      · subst x
        simp [Identity.replace]
      · rw [show Identity.replace q index (p index) x = q x by simp [Identity.replace, changed]]
        exact (changeI.preserves ops gCode uCode changed).trans
          (decoded_eq gCode hCode together x different)
    refine ⟨w, wU, fun premise => (right u uU w wU sameCode).mp
      (condition ((left u uU w wU sameCode).mpr premise)), newI⟩
  intro g gU h hU agree
  rw [mem_stepSet, mem_stepSet, and_iff_right gU, and_iff_right hU]
  exact ⟨move g h gU hU agree, move h g hU gU agree.symm⟩

theorem bounded_atom {d i j : V} (hi : i ∈ d) (hj : j ∈ d) :
    HasClockBound d (assignments d) (atomicSet (assignments d) i j) := by
  obtain ⟨a, ha, avoidsI⟩ := avoid_nat_label i
  obtain ⟨b, hb, avoidsJ⟩ := avoid_nat_label j
  obtain ⟨n, hn, first, second⟩ := common_nat_bound a b ha hb
  exact ⟨n, hn, fun k hk later => atom_independent hi hj
    (avoidsI k hk fun member => later (first k member))
    (avoidsJ k hk fun member => later (second k member))⟩

theorem bounded_step {d i R S : V} (hi : i ∈ d)
    (left : HasClockBound d (assignments d) R) (right : HasClockBound d (assignments d) S) :
    HasClockBound d (assignments d) (stepSet (assignments d) i R S) := by
  obtain ⟨n, hn, leftRule⟩ := left
  obtain ⟨m, hm, rightRule⟩ := right
  obtain ⟨s, hs, first, second⟩ := common_nat_bound n m hn hm
  exact ⟨s, hs, fun k hk later => step_independent hi
    (leftRule k hk fun member => later (first k member))
    (rightRule k hk fun member => later (second k member))⟩

theorem generated_hasClockBound (d R : V) (member : R ∈ generated d (assignments d)) :
    HasClockBound d (assignments d) R := by
  let U := assignments d
  let supported := sep (℘ U) (HasClockBound d U) (by
    have defn := predicateWith clockBoundDef ![d,U]
    exact defn.of_iff fun R => (eval_clockBoundDef R d U).symm)
  have mem (R : V) : R ∈ supported ↔ R ⊆ U ∧ HasClockBound d U R := by
    rw [show supported = _ from rfl, mem_sep_iff, mem_power_iff]
  have closed : ClosedFamily d U supported := by
    constructor
    · exact fun R h => ((mem R).mp h).1
    · intro i j hi hj
      exact (mem _).mpr ⟨fun g h => ((mem_atomicSet U i j g).mp h).1, bounded_atom hi hj⟩
    · intro i R S hi rIn sIn
      exact (mem _).mpr ⟨fun g h => ((mem_stepSet U i R S g).mp h).1,
        bounded_step hi ((mem R).mp rIn).2 ((mem S).mp sIn).2⟩
  exact ((mem R).mp (((mem_generated R d U).mp member).2 _ closed)).2

end I0451.Logic.SetAssignments
