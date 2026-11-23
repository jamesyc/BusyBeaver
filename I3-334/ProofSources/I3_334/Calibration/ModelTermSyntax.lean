module
public import I3_334.Calibration.ModelWords
@[expose] public section

namespace PalomarI3334.SearchProgram

open PalomarI3380
open PalomarI3380.Arithmetic (Chain)
open ArithmeticMachine.SourceWords (appendVector)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem GuardedConsumes.empty (offset count : M) : GuardedConsumes offset 0 count count := by
  simpa only [GuardedConsumes,len_nil] using Chain.refl (guardedStep offset) (⟪0,count⟫ : M)

theorem GuardedConsumes.one (offset token count : M) (positive : 0 < count) (safe : offset ≤ π₂ token) :
    GuardedConsumes offset (?[token]) count (count-1+π₁ token) := by
  simpa only [GuardedConsumes,len_adjoin,len_nil,zero_add] using
    (Chain.single (edge := guardedStep offset) (a := ⟪?[token],count⟫) (b := ⟪0,count-1+π₁ token⟫)
      (by exact ⟨token,0,by simpa using positive,by simp,safe,by simp⟩))

theorem GuardedConsumes.append {offset a b before middle after : M}
    (left : GuardedConsumes offset a before middle) (right : GuardedConsumes offset b middle after) :
    GuardedConsumes offset (appendVector a b) before after := by
  let extend := fun z : M => ⟪appendVector (π₁ z) b,π₂ z⟫
  have fn : 𝚺ᴬ₁-Function₁ extend := by unfold extend; definability
  have valid : ∀ x y : M, guardedStep offset x y → guardedStep offset (extend x) (extend y) := by
    intro x y edge
    obtain ⟨token,rest,live,seen,safe,forward⟩ := edge
    simp only [guardedStep,extend,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair]
    exact ⟨token,appendVector rest b,live,by rw [seen,ArithmeticMachine.SourceWords.appendVector_cons],
      safe,by rw [forward]; simp⟩
  have prefixRun := Chain.map left extend fn valid
  simp only [extend,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair,ArithmeticMachine.SourceWords.appendVector_nil] at prefixRun
  unfold GuardedConsumes
  rw [ArithmeticMachine.SourceWords.appendVector_length]
  exact prefixRun.trans right

theorem GuardedConsumes.lower {offset lower tokens before after : M}
    (run : GuardedConsumes offset tokens before after) (le : lower ≤ offset) :
    GuardedConsumes lower tokens before after := by
  have identity : 𝚺ᴬ₁-Function₁ (fun x : M => x) := by definability
  exact Chain.map run (fun x => x) identity (by
    intro x y step
    obtain ⟨token,rest,live,seen,safe,forward⟩ := step
    exact ⟨token,rest,live,seen,le.trans safe,forward⟩)

theorem GuardedConsumes.extend_count {offset tokens before after : M}
    (run : GuardedConsumes offset tokens before after) (extra : M) :
    GuardedConsumes offset tokens (before+extra) (after+extra) := by
  let addCount := fun z : M => ⟪π₁ z,π₂ z+extra⟫
  have computable : 𝚺ᴬ₁-Function₁ addCount := by unfold addCount; definability
  have edge : ∀ x y : M, guardedStep offset x y → guardedStep offset (addCount x) (addCount y) := by
    intro x y h
    obtain ⟨token,rest,live,shape,allowed,rfl⟩ := h
    have pos : 0 < π₂ x+extra := lt_of_lt_of_le live (le_add_of_nonneg_right (Arithmetic.zero_le _))
    have debit : (π₂ x+extra)-1 = (π₂ x-1)+extra := by
      have part := tsub_add_cancel_of_le (pos_iff_one_le.mp live)
      calc
        _ = (((π₂ x-1)+extra)+1)-1 := by rw [add_right_comm,part]
        _ = _ := Arithmetic.add_sub_self
    simp only [guardedStep,addCount,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair]
    exact ⟨token,rest,pos,shape,allowed,by rw [debit]; simp only [add_assoc,add_comm,add_left_comm]⟩
  simpa only [GuardedConsumes,addCount,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair] using
    Chain.map run addCount computable edge

/-- An internal word fills exactly one pending slot, and every token
meets its tag lower bound. This is a Σ₁ property of the word. -/
def ClosedVector (offset tokens : M) : Prop := GuardedConsumes offset tokens 1 0

theorem closedVector_definable : 𝚺ᴬ₁-Relation (ClosedVector (M := M)) := by
  have relation := guardedConsumes_definable (M := M)
  unfold ClosedVector
  definability

theorem ClosedVector.consume {offset tokens count : M}
    (closed : ClosedVector offset tokens) (positive : 0 < count) :
    GuardedConsumes offset tokens count (count-1) := by
  have code := closed.extend_count (count-1)
  rw [Arithmetic.add_tsub_self_of_le (pos_iff_one_le.mp positive),zero_add] at code
  exact code

noncomputable def joinVectors : List M → M
  | [] => 0
  | t::ts => appendVector t (joinVectors ts)

theorem consume_forest (offset : M) (ts : List M) (good : ∀ t ∈ ts, ClosedVector offset t) (count : M) :
    GuardedConsumes offset (joinVectors ts) ((ts.length : M)+count) count := by
  induction ts with
  | nil => simpa [joinVectors] using GuardedConsumes.empty offset count
  | cons token ts ih =>
    have rest := ih (fun t member => good t (List.mem_cons_of_mem _ member))
    have start : (((token::ts).length : M)+count) = ((ts.length : M)+count)+1 := by
      simp only [List.length_cons,Nat.cast_succ]
      rw [add_right_comm]
    have first : GuardedConsumes offset token (((token::ts).length : M)+count) ((ts.length : M)+count) := by
      rw [start]
      have live : 0 < ((ts.length : M)+count)+1 :=
        lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)
      have proof := (good token List.mem_cons_self).consume live
      simpa only [Arithmetic.add_sub_self] using proof
    exact first.append rest

noncomputable def modelApplication (tag : M) (args : List M) : M :=
  (⟪(args.length : M),tag⟫ : M) ∷ joinVectors args

theorem closed_application (offset tag : M) (args : List M) (allowed : offset ≤ tag)
    (wellFormed : ∀ a ∈ args, ClosedVector offset a) :
    ClosedVector offset (modelApplication tag args) := by
  have head := GuardedConsumes.one offset (⟪(args.length : M),tag⟫ : M) (1 : M) (by simp)
    (by simpa using allowed)
  have argsUse := consume_forest offset args wellFormed (0 : M)
  simp only [add_zero] at argsUse
  simp only [Arithmetic.sub_self,zero_add,Arithmetic.pi₁_pair] at head
  have combined := head.append argsUse
  simpa [ClosedVector,modelApplication,ArithmeticMachine.SourceWords.appendVector_cons,
    ArithmeticMachine.SourceWords.appendVector_nil] using combined

end PalomarI3334.SearchProgram
