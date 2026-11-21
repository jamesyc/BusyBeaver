module
public import I3_380.Arithmetic.ClockGraph
public import I3_380.Arithmetic.InternalMoves
@[expose] public section

namespace PalomarI3380.Logic.Expanded.OmegaDomain

open SquareRepresentation ArithmeticMachine
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

variable {V : Type} {E G : V → V → Prop}
variable {L : ClassAxioms E G} {inhabited : Nonempty V} (D : OmegaDomain L inhabited)

local notation "K" => (L.context inhabited)
local notation "W" => D.Points
local instance : (W)↓[ℒₒᵣ] ⊧* 𝗣𝗔 := D.models_peano

noncomputable def clockGraph : ClassRelation E G :=
  ⟨fun i z => ∃ hi : E i D.omega, (D.clockAt ⟨i,hi⟩).setCode = z,
    ⟨clockGraphFormula D.omega,clockGraphFormula_scope D.omega,D.clockGraphFormula_eval⟩⟩

theorem member_of_time_domain (n : W) (i : V) (hi : E i ((K).succ n.val)) : E i D.omega := by
  rcases ((K).mem_succ _ _).mp hi with lt | same
  · exact ((K).omega_ordinal D.specification).transitive n.val n.property i lt
  · exact same.symm ▸ n.property

theorem clock_graph_exists (n : W) :
    ∃ f, Internal.FunctionOn E f ((K).succ n.val) ∧
      ∀ i z, Internal.At E f i z ↔ E i ((K).succ n.val) ∧ D.clockGraph.holds i z := by
  have desc := Definable.atom (S := (K).square) (n := 2) D.clockGraph
    (i := 0) (j := 1) (by decide) (by decide)
  apply (K).functionOf [] desc
  · rintro i a b ⟨hi,eq⟩ ⟨_,other⟩
    exact eq.symm.trans other
  · intro i hi
    have inside := D.member_of_time_domain n i hi
    exact ⟨(D.clockAt ⟨i,inside⟩).setCode,inside,rfl⟩

theorem successor_in_domain {n : W} {i : V} (hi : E i D.omega) :
    E ((K).succ i) ((K).succ n.val) ↔ E i n.val := by
  let idx : W := ⟨i,hi⟩
  constructor
  · intro inside
    rcases ((K).mem_succ _ _).mp inside with lower | eq
    · exact D.lt_trans (D.lt_succ_self idx) (show D.successor idx < n from lower)
    · exact eq ▸ ((K).mem_succ i i).mpr (Or.inr rfl)
  · intro earlier
    have bound : D.successor idx ≤ n := by
      rw [← D.plus_one]
      exact succ_le_iff_lt.mpr earlier
    rcases eq_or_lt_of_le bound with eq | less
    · exact ((K).mem_succ _ _).mpr (Or.inr (congrArg Subtype.val eq))
    · exact ((K).mem_succ _ _).mpr (Or.inl less)

theorem clock_successor_matches {i : W} {c : Configuration D}
    (step : Internal.LiteralStep E (D.clockAt i).raw c.raw) :
    D.clockAt (D.successor i) = c :=
  (D.clockAt_succ i).trans ((D.literalStep_eval _ _).mp step).2

abbrev HistorySteps (f n : V) : Prop :=
  ∀ i, E i n → ∃ next s t before after, Internal.Succ E i next ∧
    Internal.At E f i before ∧ Internal.At E f next after ∧
    Internal.ConfigurationCode E s before ∧ Internal.ConfigurationCode E t after ∧ Internal.LiteralStep E s t

private theorem valid_history_label {n : W} {f first : V}
    (fn : Internal.FunctionOn E f ((K).succ n.val))
    (atZero : Internal.At E f (0 : W).val first)
    (blank : Internal.ConfigurationCode E ⟨(0 : W).val,(0 : W).val,(0 : W).val⟩ first)
    (steps : HistorySteps (E := E) f n.val) :
    ∀ i, E i D.omega → E i ((K).succ n.val) → ∀ z, Internal.At E f i z → D.clockGraph.holds i z := by
  have allowed := Definable.mem (N := (K)) (n := 3) (i := 0) (j := 1) (by decide) (by decide)
  have value := Definable.graphValue (N := (K)) (n := 4) (i := 3) (j := 1) (k := 0)
    (by decide) (by decide) (by decide)
  have clock := Definable.atom (S := (K).square) (n := 4) D.clockGraph (i := 1) (j := 0)
    (by decide) (by decide)
  have assertion := allowed.implies (Definable.all (value.implies clock))
  apply (K).omega_induction D.specification [f] assertion ((K).succ n.val)
  · intro _ z hit
    let c : Configuration D := ⟨0,0,0⟩
    have same := (K).at_unique fn hit atZero
    refine ⟨(0 : W).property,?_⟩
    change (D.clockAt (0 : W)).setCode = z
    rw [D.clockAt_zero]
    exact ((c.encodes_set _).mp blank).symm.trans same.symm
  · intro i hi induction_ inside z hit
    have earlier := (D.successor_in_domain (n := n) hi).mp inside
    obtain ⟨j,s,t,before,after,succ,origin,target,codeS,codeT,link⟩ := steps i earlier
    have indexEq := ((K).internal_succ i j).mp succ
    subst j
    obtain ⟨source,sourceShape⟩ := D.typed_configuration codeS
    obtain ⟨dest,destShape⟩ := D.typed_configuration codeT
    rw [← sourceShape] at codeS link
    rw [← destShape] at codeT link
    have prev : D.clockGraph.holds i before :=
      induction_ (((K).mem_succ _ _).mpr (Or.inl earlier)) before origin
    obtain ⟨ini,sourceCode⟩ := prev
    have configEq := D.typed_code_unique (sourceCode.trans ((source.encodes_set _).mp codeS))
    rw [← configEq] at link
    have updated := D.clock_successor_matches link
    have eq := (K).at_unique fn hit target
    exact ⟨(K).omega_succ D.specification hi,by
      change (D.clockAt (D.successor ⟨i,ini⟩)).setCode = z
      rw [updated]
      exact ((dest.encodes_set _).mp codeT).symm.trans eq.symm⟩

theorem clock_halts_of_internal (h : Internal.Halts E) :
    ∃ i : W, ¬(D.clockAt i).state < (380 : W) := by
  obtain ⟨n,domain,f,z,first,finish,hn,succ,fn,empty,blank,initial,last,ending,steps⟩ := h
  let idx : W := ⟨n,((K).natObject_iff D.specification _).mp hn⟩
  have domainEq := ((K).internal_succ n domain).mp succ
  have zero := ((K).empty_unique z).mp empty
  subst domain z
  obtain ⟨c,hc,halt⟩ := ending
  obtain ⟨endState,raw⟩ := D.typed_configuration hc
  rw [← raw] at hc halt
  have label := valid_history_label D (n := idx) fn initial blank steps
    n idx.property (((K).mem_succ _ _).mpr (Or.inr rfl)) finish last
  obtain ⟨_,same⟩ := label
  have state := D.typed_code_unique (same.trans ((endState.encodes_set _).mp hc))
  exact ⟨idx,by rw [state,Subtype.ext (D.numeral_value.mp halt)]; exact D.lt_irrefl _⟩

end PalomarI3380.Logic.Expanded.OmegaDomain
