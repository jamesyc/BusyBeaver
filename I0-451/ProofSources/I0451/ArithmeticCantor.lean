module
public import I0451.ArithmeticTrace
public import M6.Source.Cantor

/-! The diagonal pairing used by the literal scheduler, with total
projections in every model of IΣ₁. The symbol codes use this pairing
independently of Foundation's internal tuple representation. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

def cantorDef : 𝚺ᴬ₀.Semisentence 3 :=
  .mkSigma “z a b. 2 * z = (a + b) * ((a + b) + 1) + 2 * b”

def cantorLeftDef : 𝚺ᴬ₁.Semisentence 2 :=
  .mkSigma “left code. ∃ right, !cantorDef code left right”

def cantorRightDef : 𝚺ᴬ₁.Semisentence 2 :=
  .mkSigma “right code. ∃ left, !cantorDef code left right”

section Models

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem product_even (n : V) : ∃ k : V, 2 * k = n * (n + 1) := by
  induction n using ISigma1.sigma1_succ_induction with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨k, eq⟩ := ih
    refine ⟨k + (n + 1), ?_⟩
    rw [mul_add, eq]
    simp only [← one_add_one_eq_two, mul_add, add_mul, mul_one, one_mul]
    ac_rfl
  | hP => definability

theorem cantor_existsUnique (a b : V) :
    ∃! z : V, 2 * z = (a + b) * ((a + b) + 1) + 2 * b := by
  obtain ⟨k, eq⟩ := product_even (a + b)
  have code : 2 * (k + b) = (a + b) * ((a + b) + 1) + 2 * b := by rw [mul_add, eq]
  exact ⟨k + b, code, fun z spec => mul_left_cancel₀ (by simp : (2 : V) ≠ 0) (spec.trans code.symm)⟩

noncomputable def cantor (a b : V) : V := Classical.choose! (cantor_existsUnique a b)

theorem cantor_eq (a b : V) :
    2 * cantor a b = (a + b) * ((a + b) + 1) + 2 * b :=
  Classical.choose!_spec (cantor_existsUnique a b)

theorem eq_cantor_iff (z a b : V) :
    z = cantor a b ↔ 2 * z = (a + b) * ((a + b) + 1) + 2 * b :=
  Classical.choose!_eq_iff_right (cantor_existsUnique a b)

instance cantor_defined : 𝚺ᴬ₀-Function₂[V] (cantor : V → V → V) via cantorDef :=
  .mk fun v => by simp [cantorDef, eq_cantor_iff]

@[definability] instance cantor_definable : 𝚺ᴬ₀-Function₂[V] (cantor : V → V → V) :=
  cantor_defined.to_definable

@[simp] theorem cantor_zero : cantor (0 : V) 0 = 0 := by
  symm
  exact (eq_cantor_iff _ _ _).mpr (by simp)

theorem cantor_next (a b : V) : cantor a (b + 1) = cantor (a + 1) b + 1 := by
  symm
  apply (eq_cantor_iff _ _ _).mpr
  rw [mul_add, cantor_eq]
  simp only [mul_add, add_mul, mul_one, one_mul]
  ac_rfl

theorem cantor_wrap (b : V) : cantor (b + 1) 0 = cantor 0 b + 1 := by
  symm
  apply (eq_cantor_iff _ _ _).mpr
  rw [mul_add, cantor_eq]
  simp only [zero_add, add_zero, mul_zero, mul_one, one_mul,
    ← one_add_one_eq_two, mul_add, add_mul]
  ac_rfl

theorem cantor_factor (a b : V) : cantor a b = cantor (a + b) 0 + b := by
  symm
  apply (eq_cantor_iff _ a b).mpr
  rw [mul_add, cantor_eq]
  simp only [add_zero, mul_zero]

theorem cantor_descend {a b n : V} (sum : a + b = n + 1) :
    cantor a b = b + 1 + cantor 0 n := by
  rw [cantor_factor, sum, cantor_wrap]
  ac_rfl

theorem cantor_surjective (n : V) : ∃ a b, cantor a b = n := by
  induction n using ISigma1.sigma1_succ_induction with
  | zero => exact ⟨0, 0, cantor_zero⟩
  | succ n ih =>
    obtain ⟨a, b, eq⟩ := ih
    by_cases zero : a = 0
    · subst a
      exact ⟨b + 1, 0, by rw [cantor_wrap, eq]⟩
    · obtain ⟨k, rfl⟩ := eq_succ_of_pos (pos_iff_ne_zero.mpr zero)
      exact ⟨k, b + 1, by rw [cantor_next, eq]⟩
  | hP => definability

private theorem triangular_next (s : V) : (s + 1) * (s + 1 + 1) = s * (s + 1) + 2 * s + 2 := by
  simp only [← one_add_one_eq_two, mul_add, add_mul, mul_one, one_mul]
  ac_rfl

theorem cantor_diagonal_lt (a b c d : V) (h : a + b < c + d) : cantor a b < cantor c d := by
  have hb : b ≤ a + b := by simp
  have hs : a + b + 1 ≤ c + d := succ_le_iff_lt.mpr h
  have hp : (a + b + 1) * (a + b + 1 + 1) ≤ (c + d) * (c + d + 1) :=
    mul_le_mul hs (_root_.add_le_add hs (_root_.le_refl 1)) (by simp) (by simp)
  have before : 2 * cantor a b < 2 * cantor c d := calc
    2 * cantor a b = (a + b) * (a + b + 1) + 2 * b := cantor_eq a b
    _ ≤ (a + b) * (a + b + 1) + 2 * (a + b) :=
      _root_.add_le_add (_root_.le_refl _) (mul_le_mul_of_nonneg_left hb (by simp))
    _ < (a + b) * (a + b + 1) + 2 * (a + b) + 2 := by simp
    _ = (a + b + 1) * (a + b + 1 + 1) := (triangular_next _).symm
    _ ≤ (c + d) * (c + d + 1) := hp
    _ ≤ (c + d) * (c + d + 1) + 2 * d := by simp
    _ = 2 * cantor c d := (cantor_eq c d).symm
  by_contra wrong
  exact (_root_.not_lt_of_ge (mul_le_mul_of_nonneg_left (_root_.not_lt.mp wrong) (by simp))) before

theorem cantor_injective {a b c d : V} (eq : cantor a b = cantor c d) : a = c ∧ b = d := by
  have diagonal : a + b = c + d := by
    rcases lt_trichotomy (a + b) (c + d) with less | same | greater
    · exact False.elim (_root_.ne_of_lt (cantor_diagonal_lt _ _ _ _ less) eq)
    · exact same
    · exact False.elim (_root_.ne_of_lt (cantor_diagonal_lt _ _ _ _ greater) eq.symm)
  have areEqual := congrArg (fun n : V => 2 * n) eq
  rw [cantor_eq, cantor_eq, diagonal] at areEqual
  have right : b = d := mul_left_cancel₀ (by simp : (2 : V) ≠ 0) (add_left_cancel areEqual)
  subst d
  exact ⟨add_right_cancel diagonal, rfl⟩

theorem cantorPairWitness (n : V) : ∃ p : V × V, cantor p.1 p.2 = n := by
  obtain ⟨a, b, eq⟩ := cantor_surjective n
  exact ⟨(a, b), eq⟩

noncomputable def cantorDecode (n : V) : V × V :=
  Classical.choose (cantorPairWitness n)

theorem cantor_encode_decode (n : V) : cantor (cantorDecode n).1 (cantorDecode n).2 = n :=
  Classical.choose_spec (cantorPairWitness n)

theorem cantor_decode_iff (n a b : V) : cantorDecode n = (a, b) ↔ cantor a b = n := by
  constructor
  · intro eq
    have ran := cantor_encode_decode n
    rwa [eq] at ran
  · intro eq
    apply Prod.ext <;> first
    | exact (cantor_injective ((cantor_encode_decode n).trans eq.symm)).1
    | exact (cantor_injective ((cantor_encode_decode n).trans eq.symm)).2

noncomputable def cantorLeft (n : V) : V := (cantorDecode n).1
noncomputable def cantorRight (n : V) : V := (cantorDecode n).2

theorem cantorLeft_eval (a n : V) :
    cantorLeftDef.val.Evalb ![a,n] ↔ a = cantorLeft n := by
  rw [show cantorLeftDef.val.Evalb ![a,n] ↔ ∃ b, n = cantor a b from by
    simp [cantorLeftDef]]
  constructor
  · rintro ⟨b, proof⟩
    exact (congrArg Prod.fst ((cantor_decode_iff n a b).mpr proof.symm)).symm
  · intro proof
    exact ⟨cantorRight n, by rw [proof]; exact (cantor_encode_decode n).symm⟩

theorem cantorRight_eval (b n : V) :
    cantorRightDef.val.Evalb ![b,n] ↔ b = cantorRight n := by
  rw [show cantorRightDef.val.Evalb ![b,n] ↔ ∃ a, n = cantor a b from by
    simp [cantorRightDef]]
  constructor
  · rintro ⟨a, proof⟩
    exact (congrArg Prod.snd ((cantor_decode_iff n a b).mpr proof.symm)).symm
  · intro proof
    exact ⟨cantorLeft n, by rw [proof]; exact (cantor_encode_decode n).symm⟩

theorem cantorLeft_defined :
    𝚺ᴬ₁-Function₁[V] (cantorLeft : V → V) via cantorLeftDef := .mk fun v => by
  rw [Matrix.fun_eq_vec_two v]
  exact cantorLeft_eval _ _

theorem cantorRight_defined :
    𝚺ᴬ₁-Function₁[V] (cantorRight : V → V) via cantorRightDef := .mk fun v => by
  rw [Matrix.fun_eq_vec_two v]
  exact cantorRight_eval _ _

@[definability] instance cantorLeft_definable : 𝚺ᴬ₁-Function₁[V] (cantorLeft : V → V) :=
  cantorLeft_defined.to_definable

@[definability] instance cantorRight_definable : 𝚺ᴬ₁-Function₁[V] (cantorRight : V → V) :=
  cantorRight_defined.to_definable

@[simp] theorem cantorLeft_pair (a b : V) : cantorLeft (cantor a b) = a :=
  congrArg Prod.fst ((cantor_decode_iff (cantor a b) a b).mpr rfl)

@[simp] theorem cantorRight_pair (a b : V) : cantorRight (cantor a b) = b :=
  congrArg Prod.snd ((cantor_decode_iff (cantor a b) a b).mpr rfl)

theorem cantor_nat_pair (a b : Nat) : cantor a b = M6.Source.Cantor.pair a b := by
  symm
  apply (eq_cantor_iff (V := Nat) _ a b).mpr
  change 2 * M6.Source.Cantor.pair a b = (a + b) * (a + b + 1) + 2 * b
  simp only [M6.Source.Cantor.pair, Nat.mul_add, M6.Source.Cantor.twice_triangle]

theorem cantorDecode_nat (n : Nat) : cantorDecode n = M6.Source.Cantor.decode n := by
  let p := M6.Source.Cantor.decode n
  have code : cantor p.1 p.2 = n := by
    rw [cantor_nat_pair]
    exact M6.Source.Cantor.pair_decode n
  exact (cantor_decode_iff n p.1 p.2).mpr code

theorem cantor_cast (a b : Nat) :
    ((M6.Source.Cantor.pair a b : Nat) : V) = cantor (a : V) (b : V) := by
  apply (eq_cantor_iff _ _ _).mpr
  have h := cantor_eq a b
  rw [cantor_nat_pair] at h
  exact_mod_cast h

theorem cantorLeft_cast (n : Nat) :
    cantorLeft (n : V) = ((M6.Source.Cantor.decode n).1 : V) := by
  rw [← cantorLeft_pair ((M6.Source.Cantor.decode n).1 : V)
    ((M6.Source.Cantor.decode n).2 : V), ← cantor_cast, M6.Source.Cantor.pair_decode]

theorem cantorRight_cast (n : Nat) :
    cantorRight (n : V) = ((M6.Source.Cantor.decode n).2 : V) := by
  rw [← cantorRight_pair ((M6.Source.Cantor.decode n).1 : V)
    ((M6.Source.Cantor.decode n).2 : V), ← cantor_cast, M6.Source.Cantor.pair_decode]

end Models

end I0451.Arithmetization
