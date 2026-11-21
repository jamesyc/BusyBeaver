module
public import Foundation.FirstOrder.Arithmetic.HFS.Vec
@[expose] public section

namespace PalomarI3380.Arithmetic

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Collect the values of an arithmetic graph in a vector of internal
length. This works for every length in the arithmetic model. -/
theorem tabulateVector (value : M → M) (definition : 𝚺ᴬ₁-Function₁ value) (size : M) :
    ∃ v : M, len v = size ∧ ∀ i < size, v.[i] = value i := by
  induction size using ISigma1.sigma1_succ_induction with
  | zero =>
    exact ⟨0,len_nil,fun i below => (not_lt_of_ge (Arithmetic.zero_le i) below).elim⟩
  | succ n ih =>
    obtain ⟨v,length,entries⟩ := ih
    refine ⟨concat v (value n),by rw [len_concat,length],fun i below => ?_⟩
    rcases lt_or_eq_of_le (lt_succ_iff_le.mp below) with previous | same
    · rw [concat_nth_lt _ _ (by simpa only [length] using previous),entries i previous]
    · exact same ▸ concat_nth_len' v (value n) length
  | hP => definability

/-- The two endpoints and every step of a model-finite trace. All
indices, including the number of steps, belong to the arithmetic model. -/
def Chain (edge : M → M → Prop) (steps first last : M) : Prop :=
  ∃ trace : M, len trace = steps+1 ∧ trace.[0] = first ∧ trace.[steps] = last ∧
    ∀ i < steps, edge trace.[i] trace.[i+1]

def chainDef (edge : 𝚺ᴬ₁.Semisentence 2) : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “steps first last. ∃ trace,
    !lenDef (steps+1) trace ∧ !nthDef first trace 0 ∧ !nthDef last trace steps ∧
    ∀ i < steps, ∃ a b, !nthDef a trace i ∧ !nthDef b trace (i+1) ∧ !edge a b”

theorem chainDef_eval {edge : M → M → Prop} {formula : 𝚺ᴬ₁.Semisentence 2}
    (meaning : ∀ x y : M, formula.val.Evalb ![x,y] ↔ edge x y) (steps first last : M) :
    (chainDef formula).val.Evalb ![steps,first,last] ↔ Chain edge steps first last := by
  simp [chainDef,Chain,len_defined.iff,nth_defined.iff,meaning,eq_comm]

variable {edge target : M → M → Prop} {n k a b c : M}

theorem Chain.refl (edge : M → M → Prop) (a : M) : Chain edge 0 a a :=
  ⟨?[a],by simp,by simp,by simp,fun i h => (not_lt_of_ge (Arithmetic.zero_le i) h).elim⟩

theorem Chain.single (step : edge a b) : Chain edge 1 a b := by
  refine ⟨?[a,b],by simp [one_add_one_eq_two],by simp,by simp,?_⟩
  intro i hi
  have zero : i = 0 := lt_one_iff_eq_zero.mp hi
  simpa only [zero,zero_add,nth_adjoin_zero,nth_adjoin_one] using step

theorem Chain.trans (first : Chain edge n a b) (second : Chain edge k b c) :
    Chain edge (n+k) a c := by
  obtain ⟨l,_,beginL,endL,stepsL⟩ := first
  obtain ⟨r,_,beginR,endR,stepsR⟩ := second
  let value := fun i : M => if i ≤ n then l.[i] else r.[i-n]
  let branches := fun v : Fin 2 → M =>
    (v 1 ≤ n ∧ v 0 = l.[v 1]) ∨ (n < v 1 ∧ v 0 = r.[v 1-n])
  have graph : 𝚺ᴬ₁.Definable branches := by unfold branches; definability
  have definition : 𝚺ᴬ₁-Function₁ value := graph.of_iff (fun v => by
    by_cases h : v 1 ≤ n
    · simp [branches,value,h,not_lt_of_ge h]
    · simp [branches,value,h,lt_of_not_ge h])
  obtain ⟨trace,size,entries⟩ := tabulateVector value definition (n+k+1)
  have get (i : M) (bound : i ≤ n+k) : trace.[i] = value i :=
    entries i (lt_succ_iff_le.mpr bound)
  have joined (i : M) (lower : n ≤ i) : value i = r.[i-n] := by
    rcases lt_or_eq_of_le lower with after | eq
    · simp [value,not_le_of_gt after]
    · subst i
      simp [value,endL,beginR]
  refine ⟨trace,size,?_,?_,?_⟩
  · rw [get _ (Arithmetic.zero_le _)]
    simp [value,beginL]
  · rw [get _ le_rfl,joined _ (le_add_of_nonneg_right (Arithmetic.zero_le k)),add_tsub_cancel_left,endR]
  · intro i below
    rw [get _ (le_of_lt below),get _ (succ_le_iff_lt.mpr below)]
    by_cases left : i < n
    · simpa [value,le_of_lt left,succ_le_iff_lt.mpr left] using stepsL i left
    · have lower : n ≤ i := le_of_not_gt left
      have lowerNext := lower.trans (le_of_lt (lt_add_one i))
      have remaining : i-n < k := (Arithmetic.tsub_lt_iff_left lower).mpr (by simpa [add_comm] using below)
      have next : i+1-n = i-n+1 := by
        rw [add_comm i 1,add_tsub_assoc_of_le lower]
        exact add_comm _ _
      rw [joined i lower,joined _ lowerNext,next]
      exact stepsR _ remaining

theorem Chain.map (run : Chain edge n a b) (value : M → M) (definition : 𝚺ᴬ₁-Function₁ value)
    (preserves : ∀ first last, edge first last → target (value first) (value last)) :
    Chain target n (value a) (value b) := by
  obtain ⟨trace,_,beginAt,endAt,steps⟩ := run
  obtain ⟨mapped,size,entries⟩ := tabulateVector (fun i => value trace.[i]) (by definability) (n+1)
  refine ⟨mapped,size,?_,?_,?_⟩
  · rw [entries _ (lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)),beginAt]
  · rw [entries _ (lt_add_one _),endAt]
  · intro i before
    rw [entries _ (lt_trans before (lt_add_one _)),entries _ ((by simpa only [add_comm] using add_lt_add_right before 1))]
    exact preserves _ _ (steps i before)

theorem Chain.reverse (run : Chain edge n a b)
    (opposite : ∀ first last, edge first last → target last first) :
    Chain target n b a := by
  obtain ⟨trace,_,beginAt,endAt,steps⟩ := run
  obtain ⟨rev,size,entries⟩ := tabulateVector (fun i => trace.[n-i]) (by definability) (n+1)
  refine ⟨rev,size,?_,?_,?_⟩
  · rw [entries _ (lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)),tsub_zero,endAt]
  · rw [entries _ (lt_add_one _),Arithmetic.sub_self,beginAt]
  · intro i before
    have next : i+1 ≤ n := succ_le_iff_lt.mpr before
    let j := n-(i+1)
    have flattened : j+(i+1) = n := tsub_add_cancel_of_le next
    have predecessor : j+1 = n-i := by
      calc
        j+1 = (j+1+i)-i := (Arithmetic.add_sub_self ..).symm
        _ = n-i := congrArg (· - i) (by rw [← flattened]; ac_rfl)
    have small : j < n := by
      apply lt_of_lt_of_le (lt_add_one j)
      rw [predecessor]
      exact Arithmetic.sub_le_self ..
    rw [entries _ (lt_trans before (lt_add_one _)),entries _ ((by simpa only [add_comm] using add_lt_add_right before 1)),
      ← predecessor]
    exact opposite _ _ (steps j small)

/-- Assemble a run from a definable sequence of states, after checking
one arbitrary step against the supplied transition relation. -/
theorem Chain.ofFunction (edge : M → M → Prop) (path : M → M)
    (definition : 𝚺ᴬ₁-Function₁ path) (steps : M)
    (transition : ∀ i < steps, edge (path i) (path (i+1))) :
    Chain edge steps (path 0) (path steps) := by
  obtain ⟨trace,size,entries⟩ := tabulateVector path definition (steps+1)
  refine ⟨trace,size,entries _ (lt_of_le_of_lt (Arithmetic.zero_le _) (lt_add_one _)),
    entries _ (lt_add_one _),?_⟩
  intro i before
  have next : i+1 < steps+1 := by simpa only [add_comm] using add_lt_add_right before 1
  rw [entries _ (lt_trans before (lt_add_one _)),entries _ next]
  exact transition i before

/-- Transport a definable invariant along a trace, including the
nonstandard lengths admitted by the arithmetic model. -/
theorem Chain.last_holds (run : Chain edge n a b) (P : M → Prop)
    (definition : 𝚺ᴬ₁-Predicate P) (initial : P a)
    (step : ∀ x y, P x → edge x y → P y) : P b := by
  obtain ⟨trace,_,beginAt,endAt,edges⟩ := run
  have carries (i : M) : i ≤ n → P trace.[i] := by
    induction i using ISigma1.sigma1_succ_induction with
    | zero => intro _; rwa [beginAt]
    | succ k ih =>
      intro bound
      have earlier := succ_le_iff_lt.mp bound
      exact step _ _ (ih (le_of_lt earlier)) (edges k earlier)
    | hP => definability
  exact endAt ▸ carries n le_rfl

end PalomarI3380.Arithmetic
