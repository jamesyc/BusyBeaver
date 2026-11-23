module
public import I3_334Support.SetTheory.Recursion.RecursionBounds
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext.ClassUpdate

open Logic
variable {A V : Type} {M : Algebra A} {N : SetContext M V} (U : ClassUpdate N)

def Candidate (key bounds i previous value : V) : Prop :=
  ∃ height stage, Internal.At N.mem bounds i height ∧ N.Rank height stage ∧
    N.mem value stage ∧ U.choices key i previous value

theorem candidate_def {n k h i p y : Nat}
    (hk : k < n) (hh : h < n) (hi : i < n) (hp : p < n) (hy : y < n) :
    N.square.Definable n (fun s => U.Candidate (s k) (s h) (s i) (s p) (s y)) := by
  have height := Definable.graphValue (N := N) (n := n+2) (i := h+2) (j := i+2) (k := 1)
    (by omega) (by omega) (by omega)
  have stage := Definable.rank (N := N) (n := n+2) (i := 1) (j := 0) (by omega) (by omega)
  have member := Definable.mem (N := N) (n := n+2) (i := y+2) (j := 0) (by omega) (by omega)
  have checked := U.definable (n := n+2) (i := k+2) (j := i+2) (k := p+2) (l := y+2)
    (by omega) (by omega) (by omega) (by omega)
  exact Definable.ex (Definable.ex (height.and (stage.and (member.and checked))))

def ChooseStep (parameters i previous value : V) : Prop :=
  ∃ key bounds order, N.Triple key bounds order parameters ∧
    ((U.Candidate key bounds i previous value ∧
      ∀ y, U.Candidate key bounds i previous y → value = y ∨ Internal.At N.mem order value y) ∨
      ((¬∃ y, U.Candidate key bounds i previous y) ∧ Internal.Empty N.mem value))

theorem chooseStep_def : Definable.Relation4 N U.ChooseStep := by
  intro n p i f y hp hi hf hy
  have settings := N.triple_def (n := n+3) (a := 2) (b := 1) (c := 0) (p := p+3)
    (by omega) (by omega) (by omega) (by omega)
  have chosen := U.candidate_def (n := n+3) (k := 2) (h := 1) (i := i+3) (p := f+3) (y := y+3)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have other := U.candidate_def (n := n+4) (k := 3) (h := 2) (i := i+4) (p := f+4) (y := 0)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have equality := Definable.eq (S := N.square) (n := n+4) (i := y+4) (j := 0) (by omega) (by omega)
  have ordered := Definable.graphValue (N := N) (n := n+4) (i := 1) (j := y+4) (k := 0)
    (by omega) (by omega) (by omega)
  have empty := Definable.empty (N := N) (n := n+3) (i := y+3) (by omega)
  have selection := chosen.and (Definable.all (other.implies (equality.or ordered)))
  have fallback := (Definable.ex other).not.and empty
  exact Definable.ex (Definable.ex (Definable.ex (settings.and (selection.or fallback))))

/-- A set of bounds permits one wellorder to select all recursion
outputs, using only the membership model's actual Choice axiom. -/
structure Selector where
  bounds : V
  order : V
  ambient : V
  wellOrder : N.WellOrderOn (Internal.At N.mem order) ambient
  within : ∀ i b s, Internal.At N.mem bounds i b → N.Rank b s → N.Subset s ambient

variable {U : ClassUpdate N}

theorem Selector.candidate_inside (S : Selector (N := N)) {i f value : V}
    (h : U.Candidate U.key S.bounds i f value) : N.mem value S.ambient := by
  obtain ⟨height,stage,valueAt,rank,member,_⟩ := h
  exact S.within i height stage valueAt rank value member

theorem chooseStep_exists (S : Selector (N := N)) (i f : V) :
    ∃ value, U.ChooseStep (N.triple U.key S.bounds S.order) i f value := by
  classical
  by_cases response : ∃ value, U.Candidate U.key S.bounds i f value
  · have defn := U.candidate_def (n := 6) (k := 2) (h := 3) (i := 4) (p := 5) (y := 0)
      (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨set,spec⟩ := N.separate [U.key,S.bounds,i,f] defn S.ambient S.ambient
    have within : N.Subset set S.ambient := fun x hx => ((spec x).mp hx).1
    obtain ⟨x, yes⟩ := response
    have has : N.NonemptySet set := ⟨x,(spec x).mpr ⟨S.candidate_inside yes,yes⟩⟩
    obtain ⟨y, hy, least⟩ := S.wellOrder.least set within has
    exact ⟨y,U.key,S.bounds,S.order,N.triple_intro _ _ _,Or.inl
      ⟨((spec y).mp hy).2,fun z hz => least z ((spec z).mpr ⟨S.candidate_inside hz,hz⟩)⟩⟩
  · exact ⟨N.empty,U.key,S.bounds,S.order,N.triple_intro _ _ _,Or.inr ⟨response,N.empty_mem⟩⟩

theorem chooseStep_unique (S : Selector (N := N)) (i f x y : V)
    (hx : U.ChooseStep (N.triple U.key S.bounds S.order) i f x)
    (hy : U.ChooseStep (N.triple U.key S.bounds S.order) i f y) : x = y := by
  obtain ⟨k,b,r,key,action⟩ := hx
  obtain ⟨k',b',r',key',action'⟩ := hy
  obtain ⟨eqK,eqB,eqR⟩ := N.triple_inj key (N.triple_intro U.key S.bounds S.order)
  subst k
  subst b
  subst r
  obtain ⟨eqK,eqB,eqR⟩ := N.triple_inj key' (N.triple_intro U.key S.bounds S.order)
  subst k'
  subst b'
  subst r'
  rcases action with ⟨left,minA⟩ | ⟨none,empty⟩ <;>
    rcases action' with ⟨right,minB⟩ | ⟨none',empty'⟩
  · rcases minA y right with same | xy
    · exact same
    · rcases minB x left with same | yx
      · exact same.symm
      · exact (WellOrderOn.asymm N S.wellOrder (S.candidate_inside left) (S.candidate_inside right) xy yx).elim
  · exact (none' ⟨x,left⟩).elim
  · exact (none ⟨y,right⟩).elim
  · exact ((N.empty_unique x).mp empty).trans ((N.empty_unique y).mp empty').symm

theorem chooseStep_correct (S : Selector (N := N)) {i f y : V}
    (step : U.ChooseStep (N.triple U.key S.bounds S.order) i f y)
    (has : ∃ z, U.Candidate U.key S.bounds i f z) :
    U.Candidate U.key S.bounds i f y := by
  obtain ⟨k,b,r,key,action⟩ := step
  obtain ⟨eqK,eqB,eqR⟩ := N.triple_inj key (N.triple_intro U.key S.bounds S.order)
  subst k
  subst b
  subst r
  exact action.elim And.left (fun h => (h.1 has).elim)

noncomputable def choosingRecursor (S : Selector (N := N)) : SetRecursion N :=
  ⟨U.domain,U.domain,N.triple U.key S.bounds S.order,fun _ => N.mem,Definable.membership_relation,
    U.ordered.ordered,U.ChooseStep,U.chooseStep_def,chooseStep_exists (U := U) S,chooseStep_unique (U := U) S⟩

end PalomarI3380.SquareRepresentation.SetContext.ClassUpdate
