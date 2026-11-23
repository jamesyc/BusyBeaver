module
public import I3_334Support.Search.Arithmetic.WordEmission
public import I3_334Support.Arithmetic.FiniteTraces
@[expose] public section

namespace PalomarI3380.ArithmeticMachine.SourceWords

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PalomarI3380.Arithmetic (Chain)

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The scanner consumes a token only while it is waiting for a node.
A token fills one waiting slot and introduces its arity many new slots. -/
def consumptionStep (x y : M) : Prop :=
  0 < π₂ x ∧ ∃ token rest, π₁ x = token ∷ rest ∧ y = ⟪rest,π₂ x-1+π₁ token⟫

def Consumes (tokens before after : M) : Prop :=
  Chain consumptionStep (len tokens) ⟪tokens,before⟫ ⟪0,after⟫

theorem consumes_definable : 𝚺ᴬ₁-Relation₃ (Consumes (M := M)) := by
  have step : 𝚺ᴬ₁-Relation (consumptionStep (M := M)) := by unfold consumptionStep; definability
  unfold Consumes Chain
  definability

theorem Consumes.empty (count : M) : Consumes 0 count count := by
  simpa only [Consumes,len_nil] using Chain.refl consumptionStep (⟪0,count⟫ : M)

theorem Consumes.one (token count : M) (positive : 0 < count) :
    Consumes (?[token]) count (count-1+π₁ token) := by
  simpa only [Consumes,len_adjoin,len_nil,zero_add] using
    (Chain.single (edge := consumptionStep) (a := ⟪?[token],count⟫) (b := ⟪0,count-1+π₁ token⟫)
      (by exact ⟨by simpa using positive,token,0,by simp,by simp⟩))

theorem Consumes.append {a b first middle last : M}
    (priorTokens : Consumes a first middle) (suffix : Consumes b middle last) :
    Consumes (appendVector a b) first last := by
  let extend := fun z : M => ⟪appendVector (π₁ z) b,π₂ z⟫
  have fn : 𝚺ᴬ₁-Function₁ extend := by unfold extend; definability
  have valid : ∀ x y : M, consumptionStep x y → consumptionStep (extend x) (extend y) := by
    intro x y edge
    obtain ⟨live,token,tail,seen,forward⟩ := edge
    simp only [consumptionStep,extend,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair]
    exact ⟨live,token,appendVector tail b,by rw [seen,appendVector_cons],by rw [forward]; simp⟩
  have prior := Chain.map priorTokens extend fn valid
  simp only [extend,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair,appendVector_nil] at prior
  unfold Consumes
  rw [appendVector_length]
  exact prior.trans suffix

/-- A single tree at the head of a stream consumes one pending slot.
This property is useful under a surrounding stack of pending siblings. -/
def ConsumesTree (tokens : M) : Prop :=
  ∀ count : M, 0 < count → Consumes tokens count (count-1)

theorem ConsumesTree.leaf (tag : M) : ConsumesTree (M := M) (?[ (⟪0,tag⟫ : M) ]) := by
  intro count active
  simpa only [Arithmetic.pi₁_pair,add_zero] using Consumes.one (⟪0,tag⟫ : M) count active

theorem Consumes.forest {v : M} {n : Nat} (width : len v = (n : M))
    (trees : ∀ i < len v, ConsumesTree v.[i]) (count : M) :
    Consumes (flattenTokens v) (count+(n : M)) count := by
  induction n generalizing v with
  | zero =>
    have empty : v=0 := len_zero_iff_eq_nil.mp (by simpa using width)
    simpa only [empty,flattenTokens_zero,Nat.cast_zero,add_zero] using Consumes.empty count
  | succ n ih =>
    have positive : 0 < len v := by rw [width,Nat.cast_succ]; simp
    rcases nil_or_adjoin v with rfl | ⟨x,tail,rfl⟩
    · simp at positive
    · have sz : len tail = (n : M) := by
        have plus : len tail+1 = (n : M)+1 := by simpa only [len_adjoin,Nat.cast_succ] using width
        exact add_right_cancel plus
      have valid : ∀ i < len tail, ConsumesTree tail.[i] := by
        intro i before
        have step : i+1 < len (x ∷ tail) := by simpa only [len_adjoin,add_lt_add_iff_right] using before
        simpa only [nth_adjoin_succ] using trees (i+1) step
      have rest := ih sz valid
      have first := trees 0 positive (count+((n+1 : Nat) : M)) (by rw [Nat.cast_succ,← add_assoc]; simp)
      simp only [nth_adjoin_zero,Nat.cast_succ,← add_assoc,Arithmetic.add_sub_self] at first
      simpa only [flattenTokens_cons,Nat.cast_succ,add_assoc] using first.append rest

end PalomarI3380.ArithmeticMachine.SourceWords
