module
public import ConcreteArithmeticModelStructure
public import ConcreteOmegaOrderArithmetic
public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic
@[expose] public section
namespace ZF207.OmegaInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]
local notation "A" => arithmeticTranslation.Model V
attribute [local irreducible] add mul
private theorem model_eq {x y : A} (h : x.val = y.val) : x = y := DirectTranslation.Model.ext h
private theorem omega_zero_le' (a : V) (ha : a ∈ (ω : V)) : (0 : V) = a ∨ 0 ∈ a := by
 rcases omega_lt_trichotomy 0 a zero_mem_ω ha with h | h | h
 · exact Or.inr h
 · exact Or.inl h
 · exact False.elim (omega_zero_le a ha h)
private theorem one_eq_succ_zero : (1 : V) = succ (0 : V) := by simp [one_def, zero_def, succ]

instance omega_models_peanoMinus : A↓[ℒₒᵣ] ⊧* Arithmetic.PeanoMinus := models_theory_iff.mpr <| by
 intro p hp
 cases hp with
 | equal p hp =>
   have h : A↓[ℒₒᵣ] ⊧* (𝗘𝗤 ℒₒᵣ : ArithmeticTheory) := inferInstance
   exact models_theory_iff.mp h p hp
 | addZero =>
   simp only [models_iff]
   intro x
   apply model_eq
   simp
 | addAssoc =>
   simp only [models_iff]
   intro x y z
   apply model_eq
   simpa using add_assoc x.val y.val z.val (model_mem_omega y) (model_mem_omega z)
 | addComm =>
   simp only [models_iff]
   intro x y
   apply model_eq
   simpa using add_comm x.val y.val (model_mem_omega x) (model_mem_omega y)
 | addEqOfLt =>
   simp [models_iff, Semiformula.eval_bexsLTSucc]
   intro x y hxy
   obtain ⟨d,hd,he⟩ := omega_add_difference x.val y.val (model_mem_omega x) (model_mem_omega y) (lt_iff_mem x y |>.mp hxy)
   let z : A := ⟨succ d, by simpa [DirectTranslation.Dom, arithmeticTranslation, Semiformula.Operator.val] using ω_succ_closed hd⟩
   refine ⟨z, ?_, ?_⟩
   · rw [one_eq_succ_zero, add_succ _ _ zero_mem_ω, add_zero]
     change succ d ∈ succ y.val
     apply mem_succ_iff.mpr
     rcases omega_zero_le' x.val (model_mem_omega x) with h | h
     · left
       rw [he, ← h, zero_add _ (ω_succ_closed hd)]
     · right
       have H := add_lt_add_right 0 x.val (succ d) zero_mem_ω (model_mem_omega x) (ω_succ_closed hd) h
       simpa [zero_add _ (ω_succ_closed hd), ← he] using H
   · apply model_eq
     simpa [z] using he.symm
 | zeroLe =>
   simp [models_iff]
   intro x
   rcases omega_zero_le' x.val (model_mem_omega x) with h | h
   · exact Or.inl (model_eq (by simpa using h))
   · exact Or.inr ((lt_iff_mem _ _).mpr (by simpa using h))
 | zeroLtOne =>
   simpa [models_iff] using (show (0 : A) < 1 from (lt_iff_mem _ _).mpr (by simpa using (omega_zero_lt_one (V := V))))
 | oneLeOfZeroLt =>
   simp [models_iff]
   intro x hx
   have hz : (0 : V) ∈ x.val := hx
   letI : IsOrdinal (0 : V) := IsOrdinal.nat zero_mem_ω
   letI : IsOrdinal x.val := IsOrdinal.nat (model_mem_omega x)
   have H := IsOrdinal.subset_iff.mp (Ordinal.subset_succ_iff.mpr hz)
   rcases H with h | h
   · exact Or.inl (model_eq (by simpa [one_eq_succ_zero] using h))
   · exact Or.inr ((lt_iff_mem _ _).mpr (by simpa [one_eq_succ_zero] using h))
 | addLtAdd =>
   simp [models_iff]
   intro x y z h
   exact add_lt_add_right x.val y.val z.val (model_mem_omega x) (model_mem_omega y) (model_mem_omega z) h
 | mulZero =>
   simp only [models_iff]
   intro x
   apply model_eq
   simp [← zero_def]
 | mulOne =>
   simp only [models_iff]
   intro x
   apply model_eq
   simpa [one_eq_succ_zero] using mul_one x.val (model_mem_omega x)
 | mulAssoc =>
   simp only [models_iff]
   intro x y z
   apply model_eq
   simpa using mul_assoc x.val y.val z.val (model_mem_omega x) (model_mem_omega y) (model_mem_omega z)
 | mulComm =>
   simp only [models_iff]
   intro x y
   apply model_eq
   simpa using mul_comm x.val y.val (model_mem_omega x) (model_mem_omega y)
 | mulLtMul =>
   simp [models_iff]
   intro x y z h hz
   have hzne : z.val ≠ 0 := by
     intro he
     have H := hz
     simp [he, omega_lt_irrefl] at H
   exact mul_lt_mul_right x.val y.val z.val (model_mem_omega x) (model_mem_omega y) (model_mem_omega z) h hzne
 | distr =>
   simp only [models_iff]
   intro x y z
   apply model_eq
   simpa using mul_add x.val y.val z.val (model_mem_omega x) (model_mem_omega y) (model_mem_omega z)
 | ltIrrefl =>
   simp [models_iff, lt_iff_mem, omega_lt_irrefl]
 | ltTrans =>
   simp [models_iff]
   intro x y z h1 h2
   exact (lt_iff_mem _ _).mpr (omega_lt_trans _ _ _ (model_mem_omega z) ((lt_iff_mem _ _).mp h1) ((lt_iff_mem _ _).mp h2))
 | ltTri =>
   simp [models_iff]
   intro x y
   rcases omega_lt_trichotomy x.val y.val (model_mem_omega x) (model_mem_omega y) with h | h | h
   · exact Or.inl ((lt_iff_mem _ _).mpr h)
   · exact Or.inr (Or.inl (model_eq h))
   · exact Or.inr (Or.inr ((lt_iff_mem _ _).mpr h))
end ZF207.OmegaInterpretation
