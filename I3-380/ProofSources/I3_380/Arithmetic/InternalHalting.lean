module
public import I3_380.Arithmetic.InternalHistory
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

def terminalAt : ArithmeticSemisentence 1 :=
  “i. ∃ q l r, !clockCoordinates i q l r ∧ ¬q < 380”

theorem terminalAt_eval (i : W) :
    terminalAt.Evalb ![i] ↔ ¬(D.clockAt i).state < (380 : W) := by
  have readings : terminalAt.Evalb ![i] ↔
      ∃ q l r : W, clock 380 packedLiteral i 0 = ArithmeticMachine.encode q l r ∧ ¬q < (380 : W) := by
    simp [terminalAt,clockCoordinates_eval,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',
      Empty.eq_elim,Matrix.empty_eq,Matrix.constant_eq_singleton,numeral_eq_natCast,
      -not_lt,-exists_and_left,-exists_and_right]
  rw [readings]
  constructor
  · rintro ⟨q,l,r,eq,terminal⟩
    simpa [clockAt,Configuration.decode,eq,ArithmeticMachine.encode] using terminal
  · intro terminal
    let c := D.clockAt i
    exact ⟨c.state,c.left,c.right,(Configuration.encode_decode _).symm,terminal⟩

private theorem unary_arithmetic_class (p : ArithmeticSemisentence 1) (holds : W → Prop)
    (interpret : ∀ i : W, p.Evalb ![i] ↔ holds i) :
    Binary E G (fun x (_ : V) => ∃ h : E x D.omega, holds ⟨x,h⟩) := by
  let form : Formula V := .and (.mem (.variable 0) (.named D.omega))
    (translateFormula p (.named D.omega) (fun _ => .variable 0) Empty.elim)
  have scope : Bound form 2 :=
    ⟨⟨Nat.zero_lt_succ _,trivial⟩,translateFormula_scope _ trivial
      (fun _ => Nat.zero_lt_succ _) (fun x => x.elim)⟩
  refine ⟨form,scope,fun env => ?_⟩
  have interpretation (hi : E (env 0) D.omega) :
      eval E G (translateFormula p (.named D.omega) (fun _ => .variable 0) Empty.elim) env ↔
        holds ⟨env 0,hi⟩ :=
    (translateFormula_eval D _ _ _ _ _ (![(⟨env 0,hi⟩ : W)]) Empty.elim rfl
      (fun i => by have eq : i = 0 := Subsingleton.elim _ _; subst i; rfl) (fun x => x.elim)).trans
        (interpret _)
  exact ⟨fun ⟨hi,h⟩ => ⟨hi,(interpretation hi).mp h⟩,fun ⟨hi,h⟩ => ⟨hi,(interpretation hi).mpr h⟩⟩

theorem terminal_class :
    Binary E G (fun x (_ : V) => ∃ h : E x D.omega, ¬(D.clockAt ⟨x,h⟩).state < (380 : W)) :=
  D.unary_arithmetic_class terminalAt
    (fun i => ¬(D.clockAt i).state < (380 : W)) D.terminalAt_eval

theorem first_clock_halt {witness : W} (hwitness : ¬(D.clockAt witness).state < (380 : W)) :
    ∃ first : W, ¬(D.clockAt first).state < (380 : W) ∧
      ∀ i : W, i < first → (D.clockAt i).state < (380 : W) := by
  let halted := fun x (_ : V) => ∃ h : E x D.omega, ¬(D.clockAt ⟨x,h⟩).state < (380 : W)
  obtain ⟨cut,spec⟩ := L.separation halted D.terminal_class D.omega D.omega
  have sub : (K).Subset cut D.omega := fun x hx => ((spec x).mp hx).1
  have someTerminal : (K).NonemptySet cut :=
    ⟨witness.val,(spec _).mpr ⟨witness.property,witness.property,hwitness⟩⟩
  obtain ⟨first,inside,least⟩ := ((K).omega_ordinal D.specification).ordered.least cut sub someTerminal
  obtain ⟨_,typed,stop⟩ := (spec first).mp inside
  refine ⟨⟨first,typed⟩,stop,fun i before => Classical.byContradiction fun nonworking => ?_⟩
  have inCut := (spec i.val).mpr ⟨i.property,i.property,nonworking⟩
  rcases least i.val inCut with eq | after
  · have same : (⟨first,typed⟩ : W) = i := Subtype.ext eq
    exact D.lt_irrefl i (same ▸ before)
  · exact D.lt_irrefl i (D.lt_trans before after)

theorem first_clock_state {first : W} (stop : ¬(D.clockAt first).state < (380 : W))
    (earlier : ∀ i : W, i < first → (D.clockAt i).state < (380 : W)) :
    (D.clockAt first).state = (380 : W) := by
  rcases D.nat_predecessor first with rfl | ⟨i,rfl⟩
  · exact (stop (by rw [D.clockAt_zero]; exact (D.lt_numeral_iff _ _).mpr ⟨0,by decide,rfl⟩)).elim
  have working := earlier i (D.lt_succ_self i)
  obtain ⟨q,hq,eq⟩ := (D.lt_numeral_iff _ _).mp working
  obtain ⟨read,bit⟩ := D.bit_read (D.clockAt i).right
  let qi : Fin 380 := ⟨q,hq⟩
  have next := (D.clockAt_succ i).trans (D.tick_move (D.clockAt i) qi read eq bit)
  have state : (D.clockAt (D.successor i)).state = (sourceTarget qi read : W) := by
    rw [next]
    unfold moveResult
    split <;> rfl
  rcases Nat.eq_or_lt_of_le (sourceRow_target qi read) with equal | lower
  · rw [state,show sourceTarget qi read = 380 from equal,Nat.cast_ofNat]
  · exact (stop ((D.lt_numeral_iff _ _).mpr ⟨_,lower,state⟩)).elim

theorem internal_halts_of_clock {time : W} (h : ¬(D.clockAt time).state < (380 : W)) :
    Internal.Halts E := by
  obtain ⟨n,terminal,earlier⟩ := D.first_clock_halt h
  have state := D.first_clock_state terminal earlier
  obtain ⟨f,funOn,lookup⟩ := D.clock_graph_exists n
  let initial := D.clockAt 0
  let last := D.clockAt n
  have atIndex (i : W) (hi : E i.val ((K).succ n.val)) :
      Internal.At E f i.val (D.clockAt i).setCode := (lookup _ _).mpr ⟨hi,i.property,rfl⟩
  have zeroIn : E (0 : W).val ((K).succ n.val) :=
    ((K).mem_succ _ _).mpr ((D.zero_le n).imp_right (congrArg Subtype.val))
  have blank : Internal.ConfigurationCode E ⟨(0 : W).val,(0 : W).val,(0 : W).val⟩ initial.setCode := by
    have initialCode := (initial.encodes_set _).mpr rfl
    simpa only [initial,D.clockAt_zero,Configuration.raw] using initialCode
  refine ⟨n.val,(K).succ n.val,f,(0 : W).val,initial.setCode,last.setCode,D.nat_object n,(K).mem_succ _,
    funOn,(K).empty_mem,blank,atIndex 0 zeroIn,atIndex n (((K).mem_succ _ _).mpr (Or.inr rfl)),
    ⟨last.raw,(last.encodes_set _).mpr rfl,D.numeral_value.mpr (congrArg Subtype.val state)⟩,?_⟩
  intro i hi
  have startIn : E i ((K).succ n.val) := ((K).mem_succ _ _).mpr (Or.inl hi)
  have typed := D.member_of_time_domain n i startIn
  let source : W := ⟨i,typed⟩
  let target := D.successor source
  have targetIn : E target.val ((K).succ n.val) := (D.successor_in_domain typed).mpr hi
  let start := D.clockAt source
  let finish := D.clockAt target
  exact ⟨target.val,start.raw,finish.raw,start.setCode,finish.setCode,(K).mem_succ _,
    atIndex source startIn,atIndex target targetIn,(start.encodes_set _).mpr rfl,(finish.encodes_set _).mpr rfl,
    (D.literalStep_eval _ _).mpr ⟨earlier source hi,(D.clockAt_succ source).symm⟩⟩

theorem internal_halts_iff_arithmetic :
    Internal.Halts E ↔ (haltsDef 380 packedLiteral).val.Evalb (![] : Fin 0 → W) := by
  rw [haltsDef_eval]
  exact ⟨D.clock_halts_of_internal,fun ⟨time,h⟩ => D.internal_halts_of_clock (time := time) h⟩

end PalomarI3380.Logic.Expanded.OmegaDomain
