module
public import I3_334.Machine.ArithmeticRows
public import I3_334.Proof.HaltingFormula
public import I3_334Support.Arithmetic.DefinableClasses
public import I3_334Support.Arithmetic.OmegaSigma
public import I3_334Support.Arithmetic.SigmaTranslation
public import I3_334Support.Arithmetic.StandardRun
public import I3_334Support.Logic.SigmaSoundness
@[expose] public section

namespace PalomarI3380.ArithmeticMachine

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

/-- Decode the clock result at one internal arithmetic index. -/
def clockCoordinates334 : ArithmeticSemisentence 4 :=
  “i q l r. ∃ code, !((clockBlueprint 334 PalomarI3334.packedLiteral).resultDef) code i 0 ∧ !pair₃Def code q l r”

theorem clockCoordinates_eval334 {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (i q l r : M) :
    clockCoordinates334.Evalb ![i,q,l,r] ↔ clock 334 PalomarI3334.packedLiteral i (0 : M) = encode q l r := by
  simp [clockCoordinates334,clock_eval,pair₃_defined.iff,encode,Semiformula.eval_rew,Function.comp_def,
    Matrix.comp_vecCons',Empty.eq_elim,Matrix.empty_eq,Matrix.constant_eq_singleton]

end PalomarI3380.ArithmeticMachine

namespace PalomarI3380.Logic.Expanded.OmegaDomain

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SquareRepresentation ArithmeticMachine

variable {V : Type} {E G : V → V → Prop}
variable {L : ClassAxioms E G} {inhabited : Nonempty V} (D : OmegaDomain L inhabited)

local notation "K" => (L.context inhabited)
local notation "W" => D.Points
local instance : (W)↓[ℒₒᵣ] ⊧* 𝗣𝗔 := D.models_peano

noncomputable def clockAt334 (i : W) : Configuration D :=
  Configuration.decode (clock 334 PalomarI3334.packedLiteral i 0)

theorem clockAt_zero334 : D.clockAt334 0 = ⟨0,0,0⟩ := by
  have code : (⟨0,0,0⟩ : Configuration D).code = 0 := by
    simp [Configuration.code,ArithmeticMachine.encode,Arithmetic.pair]
  rw [clockAt334,clock_zero]
  exact (congrArg (Configuration.decode (D := D)) code.symm).trans (Configuration.decode_encode _)

theorem clockAt_succ334 (i : W) :
    D.clockAt334 (D.successor i) = Configuration.decode (tick 334 PalomarI3334.packedLiteral (D.clockAt334 i).code) := by
  rw [← D.plus_one,clockAt334,clock_succ]
  rw [clockAt334,Configuration.encode_decode]

/-- A graph of literal configurations in the membership language. The
coordinates are read from the arithmetic clock and packed as actual set pairs. -/
def clockGraphFormula334 (omega : V) : Formula V :=
  .and (.mem (.variable 0) (.named omega))
    (.ex (.ex (.ex
      (.and (.mem (.variable 2) (.named omega))
        (.and (.mem (.variable 1) (.named omega))
          (.and (.mem (.variable 0) (.named omega))
            (.and (configurationAt (.variable 2) (.variable 1) (.variable 0) (.variable 4))
              (translateFormula clockCoordinates334 (.named omega)
                ![.variable 3,.variable 2,.variable 1,.variable 0] Empty.elim))))))))

theorem clockGraphFormula_scope334 (omega : V) : Bound (clockGraphFormula334 omega) 2 := by
  have q : (Argument.variable (V := V) 2).bound 5 := by change 2 < 5; decide
  have l : (Argument.variable (V := V) 1).bound 5 := by change 1 < 5; decide
  have r : (Argument.variable (V := V) 0).bound 5 := by change 0 < 5; decide
  have z : (Argument.variable (V := V) 4).bound 5 := by change 4 < 5; decide
  refine ⟨⟨Nat.zero_lt_succ _,trivial⟩,⟨⟨q,trivial⟩,⟨⟨l,trivial⟩,⟨⟨r,trivial⟩,
    configurationAt_scope q l r z,?_⟩⟩⟩⟩
  apply translateFormula_scope (region := .named omega) _ trivial _ (fun x => x.elim)
  intro j
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> simp [Argument.bound]

theorem clockGraphFormula_eval334 (env : Nat → V) :
    eval E G (clockGraphFormula334 D.omega) env ↔
      ∃ h : E (env 0) D.omega, (D.clockAt334 ⟨env 0,h⟩).setCode = env 1 := by
  have arithmetic (q l r : V) (hq : E q D.omega) (hl : E l D.omega) (hr : E r D.omega)
      (hi : E (env 0) D.omega) :
      let values : Fin 4 → W := ![⟨env 0,hi⟩,⟨q,hq⟩,⟨l,hl⟩,⟨r,hr⟩]
      eval E G (translateFormula clockCoordinates334 (.named D.omega)
        ![.variable 3,.variable 2,.variable 1,.variable 0] Empty.elim)
        (pushValue (pushValue (pushValue env q) l) r) ↔
        clock (M := W) 334 PalomarI3334.packedLiteral ⟨env 0,hi⟩ 0 = ArithmeticMachine.encode (M := W)
          (⟨q,hq⟩ : W) (⟨l,hl⟩ : W) (⟨r,hr⟩ : W) := by
    intro values
    have correct (i : Fin 4) :
        (![(Argument.variable 3 : Argument V),.variable 2,.variable 1,.variable 0] i).value
          (pushValue (pushValue (pushValue env q) l) r) = (values i).val := by
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl <;> rfl
    exact (translateFormula_eval D _ _ _ _ _ values Empty.elim rfl correct (fun x => x.elim)).trans
      (clockCoordinates_eval334 ..)
  constructor
  · rintro ⟨hi,q,l,r,hq,hl,hr,ordered,computation⟩
    have coded := (configurationAt_eval _ _ _ _ _).mp ordered
    let c : Configuration D := ⟨⟨q,hq⟩,⟨l,hl⟩,⟨r,hr⟩⟩
    have exactCode : (D.clockAt334 ⟨env 0,hi⟩) = c := by
      simp only [clockAt334]
      rw [(arithmetic q l r hq hl hr hi).mp computation]
      exact Configuration.decode_encode c
    exact ⟨hi,exactCode.symm ▸ ((c.encodes_set _).mp coded).symm⟩
  · rintro ⟨hi,eq⟩
    let c := D.clockAt334 ⟨env 0,hi⟩
    refine ⟨hi,c.state.val,c.left.val,c.right.val,c.state.property,c.left.property,c.right.property,
      (configurationAt_eval _ _ _ _ _).mpr ((c.encodes_set _).mpr eq.symm),?_⟩
    exact (arithmetic _ _ _ c.state.property c.left.property c.right.property hi).mpr
      ((Configuration.encode_decode (clock (M := W) 334 PalomarI3334.packedLiteral ⟨env 0,hi⟩ 0)).symm)

private theorem bitFlag334 (n : Nat) : (Nat.mod n 2 == 1).toNat = Nat.mod n 2 := by
  rcases (show Nat.mod n 2 = 0 ∨ Nat.mod n 2 = 1 from Nat.mod_two_eq_zero_or_one n) with h | h <;> simp [h]

theorem tick_move334 (s : Configuration D) (q : Fin 334) (read : Bool)
    (state : s.state = (q.val : W)) (input : remIn s.right 2 = D.bitValue read) :
    Configuration.decode (D := D) (tick 334 PalomarI3334.packedLiteral s.code) =
      D.moveResult s (PalomarI3334.sourceWrites q read) (PalomarI3334.sourceMovesRight q read) (PalomarI3334.sourceTarget q read) := by
  classical
  let row := PalomarI3334.sourceRow q read
  have guard : s.state < (334 : W) := (D.lt_numeral_iff s.state 334).mpr ⟨q.val,q.isLt,state⟩
  have lookup : digit PalomarI3334.packedLiteral s.state s.right = (row : W) := by
    change digit PalomarI3334.machine.packedRows s.state s.right = (row : W)
    rw [state,digit_at_row PalomarI3334.machine,input]
    cases read
    · simpa [bitValue,row] using congrArg (fun n : Nat => (n : W)) (PalomarI3334.sourceRow_lookup q false)
    · simpa [bitValue,row] using congrArg (fun n : Nat => (n : W)) (PalomarI3334.sourceRow_lookup q true)
  have wb : D.bitValue (Nat.mod (Nat.div row 2) 2 == 1) = Nat.mod (Nat.div row 2) 2 := by
    rw [D.bitValue_cast,bitFlag334]
  have parity : remIn (row : W) 2 = 1 ↔ Nat.mod row 2 = 1 := by
    rw [← Nat.cast_two,remIn_cast]
    exact Nat.cast_eq_one
  have twice : (2 : W) * 2 = 4 := by
    exact_mod_cast (show (2 : Nat) * 2 = 4 from rfl)
  have next : divIn (row : W) 4 = Nat.div row 4 := by
    simpa only [Nat.cast_ofNat] using divIn_cast (M := W) row 4
  have write : remIn (divIn (row : W) 2) 2 = D.bitValue (Nat.mod (Nat.div row 2) 2 == 1) := by
    rw [wb]
    have first := divIn_cast (M := W) row 2
    have second := remIn_cast (M := W) (Nat.div row 2) 2
    simpa only [Nat.cast_ofNat] using (congrArg (fun x => remIn x ((2 : Nat) : W)) first).trans second
  have unfoldTick :
      tick 334 PalomarI3334.packedLiteral s.code =
        if remIn (row : W) 2 = 1 then
          ArithmeticMachine.encode (divIn (row : W) 4) (2*s.left+remIn (divIn (row : W) 2) 2) (divIn s.right 2)
        else
          ArithmeticMachine.encode (divIn (row : W) 4) (divIn s.left 2)
            (4*divIn s.right 2+2*remIn (divIn (row : W) 2) 2+remIn s.left 2) := by
    simp only [tick,Configuration.code,ArithmeticMachine.encode,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair,
      Nat.cast_ofNat,guard,↓reduceIte,lookup]
  rw [unfoldTick]
  change _ = D.moveResult s _ (Nat.mod row 2 == 1) _
  simp only [parity,next,write,moveResult,PalomarI3334.sourceWrites_eq,PalomarI3334.sourceTarget_eq,← show row = PalomarI3334.sourceRow q read from rfl,beq_iff_eq]
  split
  · simp only [Configuration.decode,ArithmeticMachine.encode,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair,add_comm]
  · simp only [Configuration.decode,ArithmeticMachine.encode,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair]
    rw [mul_add,← mul_assoc,twice]
    rw [add_comm (2 * D.bitValue (Nat.mod (Nat.div row 2) 2 == 1)) (4 * divIn s.right 2)]
    rw [add_comm (4 * divIn s.right 2 + 2 * D.bitValue (Nat.mod (Nat.div row 2) 2 == 1)) (remIn s.left 2)]

theorem literalStep_eval334 (s t : Configuration D) :
    PalomarI3334.Internal.LiteralStep E s.raw t.raw ↔
      s.state < (334 : W) ∧ Configuration.decode (D := D) (tick 334 PalomarI3334.packedLiteral s.code) = t := by
  have rowShape (q : Fin 334) (read : Bool) :
      PalomarI3334.literal[2*q.val+(if read then 1 else 0)]?.getD 0 = PalomarI3334.sourceRow q read := by cases read <;> rfl
  constructor
  · rintro ⟨q,atQ,read,edge⟩
    have state : s.state = (q.val : W) := Subtype.ext (D.numeral_value.mp atQ)
    rw [rowShape] at edge
    obtain ⟨input,moved⟩ := (D.move_eval _ _ _ _ _ _).mp edge
    exact ⟨(D.lt_numeral_iff s.state 334).mpr ⟨q.val,q.isLt,state⟩,
      (D.tick_move334 s q read state input).trans moved.symm⟩
  · rintro ⟨guard,moved⟩
    obtain ⟨q,hq,hState⟩ := (D.lt_numeral_iff _ _).mp guard
    obtain ⟨read,input⟩ := D.bit_read s.right
    let i : Fin 334 := ⟨q,hq⟩
    refine ⟨i,D.numeral_value.mpr (congrArg Subtype.val hState),read,?_⟩
    rw [rowShape]
    exact (D.move_eval _ _ _ _ _ _).mpr ⟨input,moved.symm.trans (D.tick_move334 s i read hState input)⟩

noncomputable def clockGraph334 : ClassRelation E G :=
  ⟨fun i z => ∃ hi : E i D.omega, (D.clockAt334 ⟨i,hi⟩).setCode = z,
    ⟨clockGraphFormula334 D.omega,clockGraphFormula_scope334 D.omega,D.clockGraphFormula_eval334⟩⟩

theorem clock_graph_exists334 (n : W) :
    ∃ f, Internal.FunctionOn E f ((K).succ n.val) ∧
      ∀ i z, Internal.At E f i z ↔ E i ((K).succ n.val) ∧ D.clockGraph334.holds i z := by
  have desc := Definable.atom (S := (K).square) (n := 2) D.clockGraph334
    (i := 0) (j := 1) (by decide) (by decide)
  apply (K).functionOf [] desc
  · rintro i a b ⟨hi,eq⟩ ⟨_,other⟩
    exact eq.symm.trans other
  · intro i hi
    have inside := D.member_of_time_domain n i hi
    exact ⟨(D.clockAt334 ⟨i,inside⟩).setCode,inside,rfl⟩

theorem clock_successor_matches334 {i : W} {c : Configuration D}
    (step : PalomarI3334.Internal.LiteralStep E (D.clockAt334 i).raw c.raw) :
    D.clockAt334 (D.successor i) = c :=
  (D.clockAt_succ334 i).trans ((D.literalStep_eval334 _ _).mp step).2

abbrev HistorySteps334 (f n : V) : Prop :=
  ∀ i, E i n → ∃ next s t before after, Internal.Succ E i next ∧
    Internal.At E f i before ∧ Internal.At E f next after ∧
    Internal.ConfigurationCode E s before ∧ Internal.ConfigurationCode E t after ∧ PalomarI3334.Internal.LiteralStep E s t

private theorem valid_history_label334 {n : W} {f first : V}
    (fn : Internal.FunctionOn E f ((K).succ n.val))
    (atZero : Internal.At E f (0 : W).val first)
    (blank : Internal.ConfigurationCode E ⟨(0 : W).val,(0 : W).val,(0 : W).val⟩ first)
    (steps : HistorySteps334 (E := E) f n.val) :
    ∀ i, E i D.omega → E i ((K).succ n.val) → ∀ z, Internal.At E f i z → D.clockGraph334.holds i z := by
  have allowed := Definable.mem (N := (K)) (n := 3) (i := 0) (j := 1) (by decide) (by decide)
  have value := Definable.graphValue (N := (K)) (n := 4) (i := 3) (j := 1) (k := 0)
    (by decide) (by decide) (by decide)
  have clock := Definable.atom (S := (K).square) (n := 4) D.clockGraph334 (i := 1) (j := 0)
    (by decide) (by decide)
  have assertion := allowed.implies (Definable.all (value.implies clock))
  apply (K).omega_induction D.specification [f] assertion ((K).succ n.val)
  · intro _ z hit
    let c : Configuration D := ⟨0,0,0⟩
    have same := (K).at_unique fn hit atZero
    refine ⟨(0 : W).property,?_⟩
    change (D.clockAt334 (0 : W)).setCode = z
    rw [D.clockAt_zero334]
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
    have prev : D.clockGraph334.holds i before :=
      induction_ (((K).mem_succ _ _).mpr (Or.inl earlier)) before origin
    obtain ⟨ini,sourceCode⟩ := prev
    have configEq := D.typed_code_unique (sourceCode.trans ((source.encodes_set _).mp codeS))
    rw [← configEq] at link
    have updated := D.clock_successor_matches334 link
    have eq := (K).at_unique fn hit target
    exact ⟨(K).omega_succ D.specification hi,by
      change (D.clockAt334 (D.successor ⟨i,ini⟩)).setCode = z
      rw [updated]
      exact ((dest.encodes_set _).mp codeT).symm.trans eq.symm⟩

theorem clock_halts_of_internal334 (h : PalomarI3334.Internal.Halts E) :
    ∃ i : W, ¬(D.clockAt334 i).state < (334 : W) := by
  obtain ⟨n,domain,f,z,first,finish,hn,succ,fn,empty,blank,initial,last,ending,steps⟩ := h
  let idx : W := ⟨n,((K).natObject_iff D.specification _).mp hn⟩
  have domainEq := ((K).internal_succ n domain).mp succ
  have zero := ((K).empty_unique z).mp empty
  subst domain z
  obtain ⟨c,hc,halt⟩ := ending
  obtain ⟨endState,raw⟩ := D.typed_configuration hc
  rw [← raw] at hc halt
  have label := valid_history_label334 D (n := idx) fn initial blank steps
    n idx.property (((K).mem_succ _ _).mpr (Or.inr rfl)) finish last
  obtain ⟨_,same⟩ := label
  have state := D.typed_code_unique (same.trans ((endState.encodes_set _).mp hc))
  exact ⟨idx,by rw [state,Subtype.ext (D.numeral_value.mp halt)]; exact D.lt_irrefl _⟩

def terminalAt334 : ArithmeticSemisentence 1 :=
  “i. ∃ q l r, !clockCoordinates334 i q l r ∧ ¬q < 334”

theorem terminalAt_eval334 (i : W) :
    terminalAt334.Evalb ![i] ↔ ¬(D.clockAt334 i).state < (334 : W) := by
  have readings : terminalAt334.Evalb ![i] ↔
      ∃ q l r : W, clock 334 PalomarI3334.packedLiteral i 0 = ArithmeticMachine.encode q l r ∧ ¬q < (334 : W) := by
    simp [terminalAt334,clockCoordinates_eval334,Semiformula.eval_rew,Function.comp_def,Matrix.comp_vecCons',
      Empty.eq_elim,Matrix.empty_eq,Matrix.constant_eq_singleton,numeral_eq_natCast,
      -not_lt,-exists_and_left,-exists_and_right]
  rw [readings]
  constructor
  · rintro ⟨q,l,r,eq,terminal⟩
    simpa [clockAt334,Configuration.decode,eq,ArithmeticMachine.encode] using terminal
  · intro terminal
    let c := D.clockAt334 i
    exact ⟨c.state,c.left,c.right,(Configuration.encode_decode _).symm,terminal⟩

theorem terminal_class334 :
    Binary E G (fun x (_ : V) => ∃ h : E x D.omega, ¬(D.clockAt334 ⟨x,h⟩).state < (334 : W)) :=
  D.unary_arithmetic_class terminalAt334
    (fun i => ¬(D.clockAt334 i).state < (334 : W)) D.terminalAt_eval334

theorem first_clock_halt334 {witness : W} (hwitness : ¬(D.clockAt334 witness).state < (334 : W)) :
    ∃ first : W, ¬(D.clockAt334 first).state < (334 : W) ∧
      ∀ i : W, i < first → (D.clockAt334 i).state < (334 : W) := by
  let halted := fun x (_ : V) => ∃ h : E x D.omega, ¬(D.clockAt334 ⟨x,h⟩).state < (334 : W)
  obtain ⟨cut,spec⟩ := L.separation halted D.terminal_class334 D.omega D.omega
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

theorem first_clock_state334 {first : W} (stop : ¬(D.clockAt334 first).state < (334 : W))
    (earlier : ∀ i : W, i < first → (D.clockAt334 i).state < (334 : W)) :
    (D.clockAt334 first).state = (334 : W) := by
  rcases D.nat_predecessor first with rfl | ⟨i,rfl⟩
  · exact (stop (by rw [D.clockAt_zero334]; exact (D.lt_numeral_iff _ _).mpr ⟨0,by decide,rfl⟩)).elim
  have working := earlier i (D.lt_succ_self i)
  obtain ⟨q,hq,eq⟩ := (D.lt_numeral_iff _ _).mp working
  obtain ⟨read,bit⟩ := D.bit_read (D.clockAt334 i).right
  let qi : Fin 334 := ⟨q,hq⟩
  have next := (D.clockAt_succ334 i).trans (D.tick_move334 (D.clockAt334 i) qi read eq bit)
  have state : (D.clockAt334 (D.successor i)).state = (PalomarI3334.sourceTarget qi read : W) := by
    rw [next]
    unfold moveResult
    split <;> rfl
  rcases Nat.eq_or_lt_of_le (PalomarI3334.sourceRow_target qi read) with equal | lower
  · rw [state,show PalomarI3334.sourceTarget qi read = 334 from equal,Nat.cast_ofNat]
  · exact (stop ((D.lt_numeral_iff _ _).mpr ⟨_,lower,state⟩)).elim

theorem internal_halts_of_clock334 {time : W} (h : ¬(D.clockAt334 time).state < (334 : W)) :
    PalomarI3334.Internal.Halts E := by
  obtain ⟨n,terminal,earlier⟩ := D.first_clock_halt334 h
  have state := D.first_clock_state334 terminal earlier
  obtain ⟨f,funOn,lookup⟩ := D.clock_graph_exists334 n
  let initial := D.clockAt334 0
  let last := D.clockAt334 n
  have atIndex (i : W) (hi : E i.val ((K).succ n.val)) :
      Internal.At E f i.val (D.clockAt334 i).setCode := (lookup _ _).mpr ⟨hi,i.property,rfl⟩
  have zeroIn : E (0 : W).val ((K).succ n.val) :=
    ((K).mem_succ _ _).mpr ((D.zero_le n).imp_right (congrArg Subtype.val))
  have blank : Internal.ConfigurationCode E ⟨(0 : W).val,(0 : W).val,(0 : W).val⟩ initial.setCode := by
    have initialCode := (initial.encodes_set _).mpr rfl
    simpa only [initial,D.clockAt_zero334,Configuration.raw] using initialCode
  refine ⟨n.val,(K).succ n.val,f,(0 : W).val,initial.setCode,last.setCode,D.nat_object n,(K).mem_succ _,
    funOn,(K).empty_mem,blank,atIndex 0 zeroIn,atIndex n (((K).mem_succ _ _).mpr (Or.inr rfl)),
    ⟨last.raw,(last.encodes_set _).mpr rfl,D.numeral_value.mpr (congrArg Subtype.val state)⟩,?_⟩
  intro i hi
  have startIn : E i ((K).succ n.val) := ((K).mem_succ _ _).mpr (Or.inl hi)
  have typed := D.member_of_time_domain n i startIn
  let source : W := ⟨i,typed⟩
  let target := D.successor source
  have targetIn : E target.val ((K).succ n.val) := (D.successor_in_domain typed).mpr hi
  let start := D.clockAt334 source
  let finish := D.clockAt334 target
  exact ⟨target.val,start.raw,finish.raw,start.setCode,finish.setCode,(K).mem_succ _,
    atIndex source startIn,atIndex target targetIn,(start.encodes_set _).mpr rfl,(finish.encodes_set _).mpr rfl,
    (D.literalStep_eval334 _ _).mpr ⟨earlier source hi,(D.clockAt_succ334 source).symm⟩⟩

theorem internal_halts_iff_arithmetic334 :
    PalomarI3334.Internal.Halts E ↔ (haltsDef 334 PalomarI3334.packedLiteral).val.Evalb (![] : Fin 0 → W) := by
  rw [haltsDef_eval]
  exact ⟨D.clock_halts_of_internal334,fun ⟨time,h⟩ => D.internal_halts_of_clock334 (time := time) h⟩

end PalomarI3380.Logic.Expanded.OmegaDomain

namespace PalomarI3334

open PalomarI3380.Logic PalomarI3380.Logic.Expanded
open PalomarI3380 (HaltsFrom blank)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

theorem halting_is_sigma1 :
    ∃ p : SigmaFormula, p.bound 0 ∧ RepresentsArithmetic p haltingSentence ∧
      ∀ env : Nat → Nat, p.natEval env ↔ HaltsFrom machine blank := by
  let formula := PalomarI3380.ArithmeticMachine.haltsDef 334 packedLiteral
  obtain ⟨p,scope,reads⟩ := sigma_representable formula.val formula.sigma_prop
  refine ⟨p,scope,⟨haltingSentence_represents.1,?_⟩,?_⟩
  · intro V E inhabited model s env nat
    have ordinary : ZFCModel E := fun f h => model f (h.elim Or.inl (fun c => Or.inr (Or.inl c)))
    obtain ⟨w,omega⟩ := ordinary.omega s
    let L := ClassAxioms.from_ordinary ordinary
    let D : OmegaDomain L inhabited := ⟨w,omega⟩
    let m := L.context inhabited
    let family : Nat → D.Points := fun i => ⟨env i,(m.natObject_iff omega _).mp (nat i)⟩
    have same : (fun i : Fin 0 => family i.val) = ![] := funext fun i => i.elim0
    exact (haltingSentence_represents.2 V E inhabited model s).trans
      (D.internal_halts_iff_arithmetic334.trans (((same ▸ reads D.Points family)).trans (D.sigma_eval p family).symm))
  · intro env
    have empty : (fun i : Fin 0 => env i.val) = ![] := funext fun i => i.elim0
    exact ((reads Nat env).symm.trans (empty.symm ▸ PalomarI3380.ArithmeticMachine.haltsDef_nat_for machine))

theorem halting_unprovable_of_nonhalting (soundness : ArithmeticSigma1Sound)
    (nonhalting : ¬HaltsFrom machine blank) : ¬ZFCI3Provable haltingSentence := by
  obtain ⟨p,scope,rep,meaning⟩ := halting_is_sigma1
  exact fun proof => nonhalting ((meaning _).mp (soundness p scope haltingSentence rep proof (fun _ => 0)))

end PalomarI3334
