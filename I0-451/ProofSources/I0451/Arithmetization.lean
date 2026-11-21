module
public import Foundation.FirstOrder.Arithmetic.HFS.PRF
public import Foundation.FirstOrder.Arithmetic.Exponential.Exp
public import I0451.Machine

@[expose] public section
namespace I0451.Arithmetization

section Syntax

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

def rowDef (table : Nat) : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “d q r. ∃ b, !remDef b r 2 ∧ ∃ p,
    !expDef p (11 * (2 * q + b)) ∧ ∃ a,
      !divDef a ↑(table) p ∧ !remDef d a 2048”

def tickDef (table : Nat) : 𝚺ᴬ₁.Semisentence 2 :=
  .mkSigma “after before.
    ∃ q, ∃ l, ∃ r, !pair₃Def before q l r ∧ ∃ d, !(rowDef table) d q r ∧
    ((d = 0 ∧ after = before) ∨
    ∃ c, d = c + 1 ∧ ∃ k, !divDef k c 4 ∧ ∃ w, !remDef w c 2 ∧
    ∃ h, !divDef h c 2 ∧ ∃ dr, !remDef dr h 2 ∧
    ∃ rt, !divDef rt r 2 ∧
    ((dr = 1 ∧ !pair₃Def after k (2 * l + w) rt) ∨
      (dr = 0 ∧ ∃ lt, !divDef lt l 2 ∧ ∃ v, !remDef v l 2 ∧
        !pair₃Def after k lt (4 * rt + 2 * w + v))))”

def machineBlueprint (table : Nat) : PR.Blueprint 0 where
  zero := .mkSigma “x. x = 0”
  succ := .mkSigma “y x t. !(tickDef table) y x”

def haltsDef (table : Nat) : 𝚺ᴬ₁.Semisentence 0 :=
  .mkSigma “∃ t, ∃ x, !((machineBlueprint table).resultDef) x t ∧
    ∃ q, ∃ l, ∃ r, !pair₃Def x q l r ∧ !(rowDef table) 0 q r”

section Models

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def modelDiv (a b : V) : V := a / b
noncomputable def modelSub (a b : V) : V := a - b
noncomputable def modelRem (a b : V) : V := a % b

noncomputable def modelDigit (table : Nat) (q r : V) : V :=
  modelRem (modelDiv (ORingStructure.numeral table : V) (Exp.exp (11 * (2 * q + modelRem r 2)))) 2048

theorem rowDef_eval (table : Nat) (d q r : V) :
    (rowDef table).val.Evalb ![d, q, r] ↔ d = modelDigit table q r := by
  simp [rowDef, modelDigit, modelDiv, modelRem, rem_defined.iff, exp_defined_deltaZero.iff, div_defined.iff, numeral_eq_natCast]

noncomputable def modelTick (table : Nat) (state : V) : V := by
  classical
  exact
    let q := π₁ state
    let l := π₁ (π₂ state)
    let r := π₂ (π₂ state)
    let d := modelDigit table q r
    if d = 0 then state
    else
      let c := modelSub d 1
      let next := modelDiv c 4
      let w := modelRem c 2
      if modelRem (modelDiv c 2) 2 = 1 then ⟪next, 2*l+w, modelDiv r 2⟫
      else ⟪next, modelDiv l 2, 4*modelDiv r 2+2*w+modelRem l 2⟫

theorem tickDef_unpack (table : Nat) (after before : V) :
    (tickDef table).val.Evalb ![after, before] ↔
      ∃ q l r, before = ⟪q, l, r⟫ ∧
        ((modelDigit table q r = 0 ∧ after = before) ∨
        ∃ c, modelDigit table q r = c + 1 ∧
          (((c / 2) % 2 = 1 ∧ after = ⟪c / 4, 2*l+c%2, r/2⟫) ∨
          ((c / 2) % 2 = 0 ∧ after = ⟪c / 4, l/2, 4*(r/2)+2*(c%2)+l%2⟫))) := by
  simp [tickDef, rowDef_eval, pair₃_defined.iff, div_defined.iff, rem_defined.iff, add_assoc]

private theorem triple_eta (x : V) : x = ⟪π₁ x, π₁ (π₂ x), π₂ (π₂ x)⟫ := by
  simp

theorem tickDef_eval (table : Nat) (after before : V) :
    (tickDef table).val.Evalb ![after, before] ↔ after = modelTick table before := by
  classical
  rw [tickDef_unpack]
  constructor
  · rintro ⟨q, l, r, rfl, ⟨zero, eq⟩ | ⟨code, digit, high | low⟩⟩
    · simpa [modelTick, zero] using eq
    · obtain ⟨direction, eq⟩ := high
      simpa [modelTick, modelDiv, modelRem, modelSub, digit, direction] using eq
    · obtain ⟨direction, eq⟩ := low
      simpa [modelTick, modelDiv, modelRem, modelSub, digit, direction] using eq
  · rintro rfl
    let q := π₁ before
    let l := π₁ (π₂ before)
    let r := π₂ (π₂ before)
    refine ⟨q, l, r, triple_eta before, ?_⟩
    let digit := modelDigit table q r
    by_cases zero : digit = 0
    · exact Or.inl ⟨zero, by
        dsimp [digit, q, r] at zero
        simp [modelTick, zero]⟩
    · let c := digit - 1
      have le : (1 : V) ≤ digit := by
        exact le_of_not_gt (fun h => zero (lt_one_iff_eq_zero.mp h))
      have code : digit = c + 1 := (tsub_add_cancel_of_le le).symm
      refine Or.inr ⟨c, code, ?_⟩
      rcases mod_two (c / 2) with dir | dir
      · refine Or.inr ⟨dir, ?_⟩
        dsimp [digit, q, r] at zero
        dsimp [c, digit, q, r] at dir
        simp [modelTick, modelDiv, modelRem, modelSub, q, l, r, c, digit, zero, dir]
      · refine Or.inl ⟨dir, ?_⟩
        dsimp [digit, q, r] at zero
        dsimp [c, digit, q, r] at dir
        simp [modelTick, modelDiv, modelRem, modelSub, q, l, r, c, digit, zero, dir]

noncomputable def machineConstruction (table : Nat) :
    PR.Construction V (machineBlueprint table) where
  zero := fun _ => 0
  succ := fun _ _ x => modelTick table x
  zero_defined := .mk fun v => by simp [machineBlueprint]
  succ_defined := .mk fun v => by
    simpa [machineBlueprint] using tickDef_eval table (v 0) (v 1)

noncomputable def atTime (table : Nat) (t : V) : V :=
  (machineConstruction table).result ![] t

@[simp] theorem atTime_zero (table : Nat) : atTime table (0 : V) = 0 := by
  simp [atTime, machineConstruction]

@[simp] theorem atTime_succ (table : Nat) (t : V) :
    atTime table (t + 1) = modelTick table (atTime table t) := by
  simp [atTime, machineConstruction]

theorem haltsDef_eval (table : Nat) :
    (haltsDef table).val.Evalb (![] : Fin 0 → V) ↔
      ∃ t : V, modelDigit table (π₁ (atTime table t)) (π₂ (π₂ (atTime table t))) = 0 := by
  simp [haltsDef, rowDef_eval, pair₃_defined.iff, (machineConstruction (V := V) table).result_defined_iff]
  constructor
  · rintro ⟨t, q, l, r, packed, stop⟩
    have params : (fun _ : Fin 0 => t) = (![] : Fin 0 → V) := by
      funext i
      exact i.elim0
    rw [params] at packed
    refine ⟨t, ?_⟩
    unfold atTime
    rw [packed]
    simpa using stop.symm
  · rintro ⟨t, stop⟩
    have params : (fun _ : Fin 0 => t) = (![] : Fin 0 → V) := by
      funext i
      exact i.elim0
    have unpacked : (machineConstruction table).result (fun _ : Fin 0 => t) t =
        ⟪π₁ (atTime table t), π₁ (π₂ (atTime table t)), π₂ (π₂ (atTime table t))⟫ := by
      rw [params]
      exact triple_eta _
    exact ⟨t, _, _, _, unpacked, stop.symm⟩

end Models

end Syntax

/-- Leave a terminal configuration unchanged so the arithmetic clock is total. -/
def totalStep (table : Table) (c : Config) : Config := (step table c).getD c

def totalRun (table : Table) : Nat → Config → Config
  | 0, c => c
  | n + 1, c => totalRun table n (totalStep table c)

theorem totalRun_last (table : Table) (n : Nat) (c : Config) :
    totalRun table (n + 1) c = totalStep table (totalRun table n c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => exact ih (totalStep table c)

noncomputable def encodeConfig (c : Config) : Nat := FFL.FirstOrder.Arithmetic.pair c.state (FFL.FirstOrder.Arithmetic.pair c.left c.right)

private theorem bit_as_remainder (n : Nat) : (I0451.bit n).toNat = n.mod 2 := by
  unfold I0451.bit
  have b : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases b with h | h
  · have standard : n.mod 2 = 0 := h
    rw [h, standard]
    rfl
  · have standard : n.mod 2 = 1 := h
    rw [h, standard]
    rfl

private theorem modelOfNat_nat (n : Nat) [n.AtLeastTwo] :
    @OfNat.ofNat Nat n (@instOfNatAtLeastTwo Nat n
      (FFL.FirstOrder.Arithmetic.natCast Nat) _) = n :=
  FFL.FirstOrder.Arithmetic.natCast_nat n

@[simp] theorem modelDiv_nat (a b : Nat) : modelDiv a b = Nat.div a b := by
  symm
  apply FFL.FirstOrder.Arithmetic.div_graph.mpr
  constructor
  · intro pos
    refine ⟨FFL.FirstOrder.Arithmetic.le_def.mpr (Nat.eq_or_lt_of_le (Nat.mul_div_le a b)), ?_⟩
    have strict := (Nat.div_lt_iff_lt_mul (x := a) pos).mp (Nat.lt_succ_self (a.div b))
    simpa [Nat.mul_comm] using strict
  · rintro rfl
    exact Nat.div_zero a

@[simp] theorem modelSub_nat (a b : Nat) : modelSub a b = Nat.sub a b := by
  symm
  apply FFL.FirstOrder.Arithmetic.sub_eq_iff.mpr
  constructor
  · intro bound
    have le : b ≤ a := (FFL.FirstOrder.Arithmetic.le_def.mp bound).elim (fun h => h ▸ Nat.le_refl _) Nat.le_of_lt
    exact (by simpa [Nat.add_comm] using (Nat.sub_add_cancel le).symm)
  · intro lt
    exact Nat.sub_eq_zero_of_le (Nat.le_of_lt lt)

@[simp] theorem modelRem_nat (a b : Nat) : modelRem a b = Nat.mod a b := by
  change modelSub a (b * modelDiv a b) = Nat.mod a b
  rw [modelSub_nat, modelDiv_nat]
  have eq : a % b = a - a / b * b := Nat.mod_eq_sub_div_mul
  change a.mod b = Nat.sub a (a.div b * b) at eq
  rw [Nat.mul_comm b]
  exact eq.symm

theorem modelDigit_nat (table q r : Nat) :
    modelDigit table q r = I0451.row table q (I0451.bit r) := by
  simp only [modelDigit, modelDiv_nat, modelRem_nat, FFL.FirstOrder.Arithmetic.numeral_eq_natCast_app,
    FFL.FirstOrder.Arithmetic.natCast_nat, modelOfNat_nat, FFL.FirstOrder.Arithmetic.exp_nat_eq_two_pow,
    I0451.row, I0451.digit, bit_as_remainder]
  have power : Nat.pow 2 (11 * (2 * q + r.mod 2)) = Nat.pow 2048 (2 * q + r.mod 2) :=
    (pow_mul (2 : Nat) 11 (2 * q + r.mod 2))
  change (table.div (Nat.pow 2 (11 * (2 * q + r.mod 2)))).mod 2048 =
    (table.div (Nat.pow 2048 (2 * q + r.mod 2))).mod 2048
  rw [power]

theorem modelTick_nat (table : Table) (c : Config) :
    modelTick table (encodeConfig c) = encodeConfig (totalStep table c) := by
  obtain ⟨q, l, r⟩ := c
  cases digit : I0451.row table q (I0451.bit r) with
  | zero =>
    simp [modelTick, encodeConfig, modelDigit_nat, digit, totalStep, step]
  | succ code =>
    by_cases dir : (code.div 2).mod 2 = 1
    · have branch : I0451.bit (code / 2) = true := by
        unfold I0451.bit
        exact beq_iff_eq.mpr dir
      simp [modelTick, encodeConfig, modelDigit_nat, digit, totalStep, step, move,
        branch, push, bit_as_remainder, modelOfNat_nat, Nat.add_comm]
      rw [ite_eq_left dir]
      rfl
    · have branch : I0451.bit (code / 2) = false :=
        beq_false_of_ne dir
      simp [modelTick, encodeConfig, modelDigit_nat, digit, totalStep, step, move,
        branch, push, bit_as_remainder, modelOfNat_nat]
      rw [ite_eq_right dir]
      congr 2
      change 4 * r.div 2 + 2 * code.mod 2 + l.mod 2 = l.mod 2 + 2 * (code.mod 2 + 2 * r.div 2)
      omega

theorem atTime_nat (table n : Nat) : atTime table n = encodeConfig (totalRun table n (blank 0)) := by
  induction n with
  | zero => simp [encodeConfig, totalRun, blank, FFL.FirstOrder.Arithmetic.pair]
  | succ n ih => rw [atTime_succ, ih, modelTick_nat, totalRun_last]

private theorem step_none_iff_row (table : Table) (c : Config) :
    step table c = none ↔ I0451.row table c.state (I0451.bit c.right) = 0 := by
  cases h : I0451.row table c.state (I0451.bit c.right) <;> simp [step, h]

theorem halts_iff_totalRun (table : Table) (start : Config) :
    Halts table start ↔ ∃ n, step table (totalRun table n start) = none := by
  constructor
  · rintro ⟨n, last, reach, stop⟩
    have same : totalRun table n start = last := by
      induction n generalizing start with
      | zero =>
        simp only [run, Option.some.injEq] at reach
        exact reach
      | succ n ih =>
        cases h : step table start with
        | none => simp [run, h] at reach
        | some next =>
          simp only [totalRun, totalStep, h, Option.getD_some]
          exact ih next (by simpa [run, h] using reach)
    exact ⟨n, by rw [same]; exact stop⟩
  · rintro ⟨n, stop⟩
    induction n generalizing start with
    | zero => exact ⟨0, start, rfl, stop⟩
    | succ n ih =>
      cases h : step table start with
      | none => exact ⟨0, start, rfl, h⟩
      | some next =>
        obtain ⟨m, last, reach, terminal⟩ := ih (start := next)
          (by simpa [totalRun, totalStep, h] using stop)
        exact ⟨m + 1, last, by simp [run, h, reach], terminal⟩

/-- The arithmetic sentence says exactly that the supplied tape machine
halts from the blank tape in the standard natural numbers. -/
theorem haltsDef_nat (table : Nat) :
    (haltsDef table).val.Evalb (![] : Fin 0 → Nat) ↔ Halts table (blank 0) := by
  rw [haltsDef_eval, halts_iff_totalRun]
  simp only [atTime_nat, modelDigit_nat, encodeConfig, FFL.FirstOrder.Arithmetic.pi₁_pair, FFL.FirstOrder.Arithmetic.pi₂_pair, step_none_iff_row]

end I0451.Arithmetization
