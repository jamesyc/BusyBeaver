module
public import I3_380.Arithmetic.Iteration
public import I3_380.Search.Cantor
@[expose] public section

/-! The arithmetic induction follows the Cantor-code lemmas in
PA196/ArithmeticSupport/Scheduler. Foundation pairs are used only for
the state of the recursion. The value being decoded uses the source ABI. -/
namespace PalomarI3380.ArithmeticMachine.SourceCantor

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

noncomputable def triangleBlueprint : PR.Blueprint 0 where
  zero := .mkSigma “z. z = 0”
  succ := .mkSigma “u z i. u = z + i + 1”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def triangleConstruction : PR.Construction V triangleBlueprint where
  zero := fun _ => 0
  succ := fun _ i z => z+i+1
  zero_defined := .mk fun v => by simp [triangleBlueprint]
  succ_defined := .mk fun v => by simp [triangleBlueprint]

noncomputable def triangleValue (n : V) : V := triangleConstruction.result ![] n
noncomputable def triangleGraph : 𝚺ᴬ₁.Semisentence 2 := triangleBlueprint.resultDef

@[simp] theorem triangle_zero : triangleValue (0 : V) = 0 := by
  simp [triangleValue,triangleConstruction]
@[simp] theorem triangle_succ (n : V) : triangleValue (n+1) = triangleValue n+n+1 := by
  simp [triangleValue,triangleConstruction]

theorem triangle_graph (z n : V) :
    triangleGraph.val.Evalb ![z,n] ↔ z=triangleValue n := by
  have he : (fun _ : Fin 0 => n) = (![] : Fin 0 → V) := by
    funext i
    exact Fin.elim0 i
  simpa [triangleGraph,triangleValue,he] using
    (triangleConstruction (V := V)).result_defined_iff ![z,n]

theorem triangle_total_unique (n : V) : ∃! z, triangleGraph.val.Evalb ![z,n] := by
  refine ⟨triangleValue n,(triangle_graph _ _).mpr rfl,?_⟩
  intro z hz
  exact (triangle_graph _ _).mp hz

theorem triangle_standard (n : Nat) : triangleValue n = PalomarI3380.Cantor.triangle n := by
  induction n with
  | zero => simp [PalomarI3380.Cantor.triangle]
  | succ n ih => simp only [triangle_succ,PalomarI3380.Cantor.triangle,ih,Nat.add_assoc]

noncomputable def pairValue (a b : V) : V := triangleValue (a+b)+b
noncomputable def pairGraph : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “z a b. ∃ t, !triangleGraph t (a+b) ∧ z = t+b”

theorem pair_graph (z a b : V) : pairGraph.val.Evalb ![z,a,b] ↔ z=pairValue a b := by
  simp [pairGraph,triangle_graph,pairValue]

theorem pair_total_unique (a b : V) : ∃! z, pairGraph.val.Evalb ![z,a,b] := by
  refine ⟨pairValue a b,(pair_graph _ _ _).mpr rfl,?_⟩
  intro z hz
  exact (pair_graph _ _ _).mp hz

theorem pair_standard (a b : Nat) : pairValue a b = PalomarI3380.Cantor.pair a b := by
  simp only [pairValue,triangle_standard,← PalomarI3380.Cantor.diagonalStart_eq,
    PalomarI3380.Cantor.diagonalStart,PalomarI3380.Cantor.pair]

noncomputable def decodeBlueprint : PR.Blueprint 0 where
  zero := .mkSigma “z. !pairDef z 0 0”
  succ := .mkSigma “u z i. ∃ a b, !pi₁Def a z ∧ !pi₂Def b z ∧
    ((a = 0 ∧ !pairDef u (b+1) 0) ∨
     (a ≠ 0 ∧ ∃ p, !subDef p a 1 ∧ !pairDef u p (b+1)))”

noncomputable def advanceState (z : V) : V := by
  classical
  exact if π₁ z = 0 then ⟪π₂ z+1,0⟫ else ⟪π₁ z-1,π₂ z+1⟫

noncomputable def decodeConstruction : PR.Construction V decodeBlueprint where
  zero := fun _ => ⟪0,0⟫
  succ := fun _ _ z => advanceState z
  zero_defined := .mk fun v => by simp [decodeBlueprint]
  succ_defined := .mk fun v => by
    by_cases h : π₁ (v 1) = 0 <;> simp [decodeBlueprint,advanceState,h]

noncomputable def decodeState (n : V) : V := decodeConstruction.result ![] n
noncomputable def decodeStateGraph : 𝚺ᴬ₁.Semisentence 2 := decodeBlueprint.resultDef

@[simp] theorem decodeState_zero : decodeState (0 : V) = ⟪0,0⟫ := by
  simp [decodeState,decodeConstruction]
@[simp] theorem decodeState_succ (n : V) : decodeState (n+1) = advanceState (decodeState n) := by
  simp [decodeState,decodeConstruction]

theorem decodeState_graph (z n : V) : decodeStateGraph.val.Evalb ![z,n] ↔ z=decodeState n := by
  have he : (fun _ : Fin 0 => n) = (![] : Fin 0 → V) := by
    funext i
    exact Fin.elim0 i
  simpa [decodeStateGraph,decodeState,he] using
    (decodeConstruction (V := V)).result_defined_iff ![z,n]

noncomputable def decodeLeft (n : V) : V := π₁ (decodeState n)
noncomputable def decodeRight (n : V) : V := π₂ (decodeState n)
noncomputable def decodeGraph : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “a b n. ∃ z, !decodeStateGraph z n ∧ !pi₁Def a z ∧ !pi₂Def b z”

theorem decode_graph (a b n : V) :
    decodeGraph.val.Evalb ![a,b,n] ↔ a=decodeLeft n ∧ b=decodeRight n := by
  simp [decodeGraph,decodeState_graph,decodeLeft,decodeRight]

instance triangleValue_defined : 𝚺ᴬ₁-Function₁[V] triangleValue via triangleGraph := .mk fun v => by
  have hv : v = ![v 0,v 1] := by
    funext ⟨i,hi⟩
    have he : i=0 ∨ i=1 := by omega
    rcases he with rfl | rfl <;> rfl
  rw [hv]
  exact triangle_graph _ _
instance triangleValue_definable : 𝚺ᴬ₁-Function₁[V] triangleValue := triangleValue_defined.to_definable
instance pairValue_definable : 𝚺ᴬ₁-Function₂[V] pairValue := by
  unfold pairValue
  definability
instance decodeState_defined : 𝚺ᴬ₁-Function₁[V] decodeState via decodeStateGraph := .mk fun v => by
  have hv : v = ![v 0,v 1] := by
    funext ⟨i,hi⟩
    have he : i=0 ∨ i=1 := by omega
    rcases he with rfl | rfl <;> rfl
  rw [hv]
  exact decodeState_graph _ _
instance decodeState_definable : 𝚺ᴬ₁-Function₁[V] decodeState := decodeState_defined.to_definable
instance decodeLeft_definable : 𝚺ᴬ₁-Function₁[V] decodeLeft := by
  unfold decodeLeft
  definability
instance decodeRight_definable : 𝚺ᴬ₁-Function₁[V] decodeRight := by
  unfold decodeRight
  definability

theorem pairValue_advance (a b : V) :
    pairValue (π₁ (advanceState ⟪a,b⟫)) (π₂ (advanceState ⟪a,b⟫)) = pairValue a b+1 := by
  rcases zero_or_succ a with rfl | ⟨a,rfl⟩
  · simp [advanceState,pairValue,triangle_succ,add_assoc]
  · simp [advanceState,pairValue,add_assoc,add_comm,add_left_comm]

theorem pairValue_advanceState (z : V) :
    pairValue (π₁ (advanceState z)) (π₂ (advanceState z)) = pairValue (π₁ z) (π₂ z)+1 := by
  simpa only [pair_unpair] using pairValue_advance (π₁ z) (π₂ z)

/-- Uniform inverse direction for every element of every IΣ1 model, not only
standard numerals. Its induction predicate uses the explicit graph instances. -/
theorem pairValue_decode (n : V) : pairValue (decodeLeft n) (decodeRight n) = n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp [decodeLeft,decodeRight,pairValue]
  case succ n ih =>
    change pairValue (π₁ (decodeState (n+1))) (π₂ (decodeState (n+1))) = n+1
    rw [decodeState_succ,pairValue_advanceState]
    exact congrArg (fun x : V => x+1) ih

theorem triangle_strict_below (b : V) : ∀ a<b, triangleValue a < triangleValue b := by
  induction b using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro a ha; simp at ha
  case succ b ih =>
    intro a ha
    have hab : a≤b := (le_iff_lt_succ).mpr ha
    have hstep : triangleValue b < triangleValue (b+1) := by
      rw [triangle_succ]
      exact lt_of_le_of_lt (show triangleValue b ≤ triangleValue b+b by simp) (lt_add_one _)
    by_cases he : a=b
    · simpa only [he] using hstep
    · exact lt_trans (ih a (lt_of_le_of_ne hab he)) hstep

theorem triangle_mono {a b : V} (h : a≤b) : triangleValue a≤triangleValue b := by
  by_cases he : a=b
  · simp [he]
  · exact le_of_lt (triangle_strict_below b a (lt_of_le_of_ne h he))

theorem triangle_ge (n : V) : n ≤ triangleValue n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    rw [triangle_succ]
    calc
      n+1 ≤ triangleValue n+1 := by simpa only [add_comm] using add_le_add_right ih 1
      _ ≤ triangleValue n+n+1 := by simpa only [add_comm] using add_le_add_right (show triangleValue n ≤ triangleValue n+n by simp) 1

theorem pairValue_lower (a b : V) : triangleValue (a+b) ≤ pairValue a b := by
  simp [pairValue]
theorem pairValue_upper (a b : V) : pairValue a b < triangleValue (a+b+1) := by
  rw [triangle_succ]
  have hb : b<a+b+1 := lt_of_le_of_lt (show b≤a+b by simp) (lt_add_one _)
  simpa only [pairValue,add_assoc,add_comm,add_left_comm] using add_lt_add_left hb (triangleValue (a+b))

/-- Injectivity holds uniformly in nonstandard models as well. -/
theorem pairValue_injective {a b c d : V} (h : pairValue a b = pairValue c d) : a=c ∧ b=d := by
  have hs : a+b=c+d := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have hm := triangle_mono ((succ_le_iff_lt).mpr hlt)
      have hh := lt_of_lt_of_le (pairValue_upper a b) (le_trans hm (pairValue_lower c d))
      exact (ne_of_lt hh) h
    · have hm := triangle_mono ((succ_le_iff_lt).mpr hgt)
      have hh := lt_of_lt_of_le (pairValue_upper c d) (le_trans hm (pairValue_lower a b))
      exact (ne_of_lt hh) h.symm
  have hb : b=d := by
    apply add_left_cancel (a := triangleValue (a+b))
    simpa only [pairValue,hs] using h
  have ha : a=c := by
    exact add_right_cancel (show a+b=c+b from by simpa only [hb] using hs)
  exact ⟨ha,hb⟩

theorem decode_pairValue (a b : V) :
    decodeLeft (pairValue a b)=a ∧ decodeRight (pairValue a b)=b :=
  pairValue_injective (pairValue_decode (pairValue a b))

theorem pairValue_bounds (a b : V) : a≤pairValue a b ∧ b≤pairValue a b := by
  have hh := le_trans (triangle_ge (a+b)) (pairValue_lower a b)
  exact ⟨le_trans (by simp) hh,le_trans (by simp) hh⟩

theorem decodeValue_bounds (n : V) : decodeLeft n≤n ∧ decodeRight n≤n := by
  have hh := pairValue_bounds (decodeLeft n) (decodeRight n)
  rw [pairValue_decode] at hh
  exact hh

end PalomarI3380.ArithmeticMachine.SourceCantor
