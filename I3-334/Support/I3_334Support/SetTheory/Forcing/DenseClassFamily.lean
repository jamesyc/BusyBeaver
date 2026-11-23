module
public import I3_334Support.SetTheory.Recursion.DependentClassRecursion
public import I3_334Support.SetTheory.Forcing.OrderForcingFormulas
@[expose] public section

namespace PalomarI3380.SquareRepresentation.SetContext

open Logic
variable {A V : Type} {M : Algebra A} (N : SetContext M V)

theorem ordinal_enumeration (set : V) :
    ∃ domain graph, N.Ordinal domain ∧ Internal.FunctionOn N.mem graph domain ∧ N.IsRange graph set := by
  obtain ⟨r,order⟩ := N.wellOrdering set
  obtain ⟨domain, f, code⟩ := N.orderType_exists set r (Definable.graph_relation (N := N)) order
  have injective (x y z : V) (left : Internal.At N.mem f x z) (right : Internal.At N.mem f y z) : x = y := by
    have hi := (code.ordinal.of_mem N ((code.onto z).mpr ⟨x,left⟩)).not_mem_self N
    rcases order.compare x y (SetRecursion.at_domain code.functionOn left)
      (SetRecursion.at_domain code.functionOn right) with lt | eq | gt
    · exact (hi ((code.order x y z z left right).mp lt)).elim
    · exact eq
    · exact (hi ((code.order y x z z right left).mp gt)).elim
  have defn := Definable.graphValue (N := N) (n := 3) (i := 2) (j := 1) (k := 0)
    (by decide) (by decide) (by decide)
  obtain ⟨g,gOn,gSpec⟩ := N.functionOf [f] defn (fun x y z => injective y z x) domain
    (fun v hv => (code.onto v).mp hv)
  refine ⟨domain,g,code.ordinal,gOn,fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨v, hv, _⟩ := code.functionOn.1 x hx
    exact ⟨v,(gSpec v x).mpr ⟨(code.onto v).mpr ⟨x,hv⟩,hv⟩⟩
  · rintro ⟨v,hv⟩
    exact SetRecursion.at_domain code.functionOn ((gSpec v x).mp hv).2

variable {R : V → V → V → Prop}

def Request (R : V → V → V → Prop) (key base enumeration index previous next : V) : Prop :=
  N.Refines next base ∧ (∃ x, Internal.At N.mem enumeration index x ∧ R key x next) ∧
    ∀ j q, Internal.At N.mem previous j q → N.Refines next q

theorem request_def (defn : Definable.Relation3 N R)
    {n key base enum i p q : Nat} (hk : key < n) (hb : base < n) (he : enum < n)
    (hi : i < n) (hp : p < n) (hq : q < n) :
    N.square.Definable n (fun env => N.Request R (env key) (env base) (env enum) (env i) (env p) (env q)) := by
  have fromBase := N.refines_def hq hb
  have lookup := Definable.graphValue (N := N) (n := n+1) (i := enum+1) (j := i+1) (k := 0)
    (by omega) (by omega) (by omega)
  have decision := defn (n := n+1) (i := key+1) (j := 0) (k := q+1)
    (by omega) (by omega) (by omega)
  have seen := Definable.graphValue (N := N) (n := n+2) (i := p+2) (j := 1) (k := 0)
    (by omega) (by omega) (by omega)
  have keeps := N.refines_def (n := n+2) (p := q+2) (q := 0) (by omega) (by omega)
  exact fromBase.and ((Definable.ex (lookup.and decision)).and (Definable.all (Definable.all (seen.implies keeps))))

def MeetStep (R : V → V → V → Prop) (params i former later : V) : Prop :=
  ∃ key base enumeration, N.Triple key base enumeration params ∧
    (N.Request R key base enumeration i former later ∨
      (¬∃ q, N.Request R key base enumeration i former q) ∧ later = base)

theorem meetStep_def (defn : Definable.Relation3 N R) :
    Definable.Relation4 N (N.MeetStep R) := by
  intro n p i f l hp hi hf hl
  have name := N.triple_def (n := n+3) (a := 2) (b := 1) (c := 0) (p := p+3)
    (by omega) (by omega) (by omega) (by omega)
  have step := N.request_def defn (n := n+3) (key := 2) (base := 1) (enum := 0)
    (i := i+3) (p := f+3) (q := l+3) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have some := N.request_def defn (n := n+4) (key := 3) (base := 2) (enum := 1)
    (i := i+4) (p := f+4) (q := 0) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have stay := Definable.eq (S := N.square) (n := n+3) (i := l+3) (j := 1) (by omega) (by omega)
  exact Definable.ex (Definable.ex (Definable.ex (name.and (step.or ((Definable.ex some).not.and stay)))))

theorem meetStep_total (key base enumeration i former : V) :
    ∃ later, N.MeetStep R (N.triple key base enumeration) i former later := by
  classical
  by_cases possible : ∃ q, N.Request R key base enumeration i former q
  · obtain ⟨q,h⟩ := possible
    exact ⟨q,key,base,enumeration,N.triple_intro _ _ _,Or.inl h⟩
  · exact ⟨base,key,base,enumeration,N.triple_intro _ _ _,Or.inr ⟨possible,rfl⟩⟩

theorem meetStep_valid {key base enumeration i former later : V}
    (h : N.MeetStep R (N.triple key base enumeration) i former later)
    (possible : ∃ q, N.Request R key base enumeration i former q) :
    N.Request R key base enumeration i former later := by
  obtain ⟨k,b,e,tuple,step⟩ := h
  obtain ⟨eqK,eqB,eqE⟩ := N.triple_inj tuple (N.triple_intro key base enumeration)
  subst k
  subst b
  subst e
  exact step.elim id (fun none => (none.1 possible).elim)

end PalomarI3380.SquareRepresentation.SetContext
