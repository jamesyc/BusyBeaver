module
public import Foundation.FirstOrder.SetTheory.Recursion.Seq
public import Foundation.FirstOrder.SetTheory.ZF.ZF

/-! Choose a natural label outside an internally finite tuple
without a choice principle. -/
@[expose] public section
namespace I0451.Logic.ZFModel

open FFL FFL.FirstOrder FFL.FirstOrder.SetTheory

variable {V : Type} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]

theorem common_nat_bound (a b : V) (ha : a ∈ (ω : V)) (hb : b ∈ (ω : V)) :
    ∃ n ∈ (ω : V), a ⊆ n ∧ b ⊆ n := by
  let x : Ordinal V := (IsOrdinal.of_mem ha).toOrdinal
  let y : Ordinal V := (IsOrdinal.of_mem hb).toOrdinal
  rcases le_total x y with first | second
  · exact ⟨b, hb, first, subset_refl _⟩
  · exact ⟨a, ha, subset_refl _, second⟩

theorem avoid_nat_label (x : V) :
    ∃ n ∈ (ω : V), ∀ i ∈ (ω : V), i ∉ n → x ≠ i := by
  by_cases natural : x ∈ (ω : V)
  · refine ⟨succ x, ω_succ_closed natural, fun i _ gone eq => ?_⟩
    exact gone (eq ▸ mem_succ_self x)
  · exact ⟨0, zero_mem_ω, fun i hi _ same => natural (same.symm ▸ hi)⟩

theorem ofNat_mem_of_lt {m n : Nat} (before : m < n) : (m : V) ∈ (n : V) := by
  induction n generalizing m with
  | zero => omega
  | succ n ih =>
    rw [num_succ_def]
    rcases Nat.lt_succ_iff_lt_or_eq.mp before with smaller | rfl
    · exact mem_succ_iff.mpr (.inr (ih smaller))
    · exact mem_succ_self _

theorem ofNat_injective : Function.Injective (SetTheory.ofNat : Nat → V) := by
  intro m n equal
  rcases lt_trichotomy m n with smaller | same | larger
  · have mem := ofNat_mem_of_lt (V := V) smaller
    rw [← show (m : V) = (n : V) from equal] at mem
    exact (mem_irrefl _ mem).elim
  · exact same
  · have mem := ofNat_mem_of_lt (V := V) larger
    rw [show (m : V) = (n : V) from equal] at mem
    exact (mem_irrefl _ mem).elim

@[simp] theorem ofNat_eq_iff {m n : Nat} : (m : V) = (n : V) ↔ m = n :=
  (ofNat_injective (V := V)).eq_iff

theorem mem_ofNat_iff {n : Nat} {i : V} :
    i ∈ (n : V) ↔ ∃ k : Fin n, (k.val : V) = i := by
  constructor
  · induction n with
    | zero => simp [zero_def]
    | succ n ih =>
      rw [num_succ_def]
      intro member
      rcases mem_succ_iff.mp member with rfl | earlier
      · exact ⟨Fin.last n, rfl⟩
      · obtain ⟨j, same⟩ := ih earlier
        exact ⟨j.castSucc, same⟩
  · rintro ⟨k, rfl⟩
    exact ofNat_mem_of_lt k.isLt

def RangeNaturalBound (s bound : V) : Prop :=
  ∀ x ∈ range s, x ∈ (ω : V) → x ∈ bound

theorem sequence_bound {s : V} (sequence : Seq s) (short : lh s ∈ (ω : V)) :
    ∃ n ∈ (ω : V), RangeNaturalBound s n := by
  have each : ∀ length ∈ (ω : V), ∀ t : V, Seq t → lh t = length → ∃ n ∈ (ω : V), RangeNaturalBound t n := by
    apply naturalNumber_induction
      (fun length => ∀ t : V, Seq t → lh t = length → ∃ n ∈ (ω : V), RangeNaturalBound t n)
    · unfold RangeNaturalBound
      definability
    · intro t seq len
      have empty : t = ∅ := seq.isempty_of_lh_eq_zero (by simpa [zero_def] using len)
      exact ⟨0, zero_mem_ω, by simp [RangeNaturalBound, empty]⟩
    · intro k hk earlier t seq len
      let : IsOrdinal k := IsOrdinal.of_mem hk
      have before : k ⊆ lh t := by
        rw [len]
        exact fun x hx => mem_succ_iff.mpr (.inr hx)
      have last : k ∈ lh t := by rw [len]; exact mem_succ_self _
      obtain ⟨a, boundedA, boundA⟩ := earlier (t ↾ k) (seq.restrict before) (seq.lh_restrict before)
      obtain ⟨b, boundedB, avoidsLast⟩ := avoid_nat_label (seq.nth last)
      obtain ⟨n, hn, useA, useB⟩ := common_nat_bound a b boundedA boundedB
      refine ⟨n, hn, fun x inRange natural => ?_⟩
      obtain ⟨i, stores⟩ := mem_range_iff.mp inRange
      have inside := seq.lt_lh_of_mem stores
      rw [len] at inside
      rcases mem_succ_iff.mp inside with rfl | inPrefix
      · apply useB
        by_contra outside
        exact avoidsLast x natural outside (seq.nth_uniq last stores).symm
      · have inPart : ⟨i,x⟩ₖ ∈ t ↾ k := kpair_mem_restrict_iff.mpr ⟨stores, inPrefix⟩
        exact useA x (boundA x (mem_range_iff.mpr ⟨i, inPart⟩) natural)
  exact each (lh s) short s sequence rfl

theorem fresh_natural_for_sequence {s : V} (sequence : Seq s) (short : lh s ∈ (ω : V)) :
    ∃ n ∈ (ω : V), n ∉ range s := by
  obtain ⟨n, hn, bounds⟩ := sequence_bound sequence short
  exact ⟨n, hn, fun seen => mem_irrefl n (bounds n seen hn)⟩

end I0451.Logic.ZFModel
