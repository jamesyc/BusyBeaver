module
public import I3_380.Arithmetic.StandardReplay
public import I3_380.Engine.Arithmetic.RegisterWords
public import I3_380.Engine.FrameWords
@[expose] public section

namespace PalomarI3380.ArithmeticMachine

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem encode_cast (q l r : Nat) :
    encode (q : M) (l : M) (r : M) = ((encode (M := Nat) q l r : Nat) : M) := by
  let graph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma pair₃Def.val
  let v : Fin 4 → Nat := ![encode (M := Nat) q l r,q,l,r]
  have standard : graph.val.Evalb v := by
    simp [graph,v,pair₃_defined.iff,encode]
  have lift := sigmaOne_upward_absolute (V := M) graph v standard
  have coords : (Nat.cast ∘ v) = ![((encode (M := Nat) q l r : Nat) : M),(q : M),(l : M),(r : M)] := by
    simp [v,Function.comp_def,Matrix.comp_vecCons',Matrix.constant_eq_singleton]
  rw [coords] at lift
  have meaning : ((encode (M := Nat) q l r : Nat) : M) = encode (q : M) (l : M) (r : M) := by
    simpa [graph,pair₃_defined.iff,encode] using lift
  exact meaning.symm

theorem repeatBit_cast (b : Bool) (n : Nat) (tail : M) :
    repeatBit b (n : M) tail = packWord (List.replicate n b) tail := by
  induction n with
  | zero => simp [packWord]
  | succ n ih =>
    rw [Nat.cast_succ,repeatBit_succ,ih]
    rfl

theorem packWord_bits (word : List Bool) : packWord word (0 : M) = (Engine.bits word : M) := by
  induction word with
  | nil => simp [packWord,Engine.bits]
  | cons b rest ih =>
    change pushBit b (packWord rest 0) = (Engine.bits (b::rest) : M)
    rw [ih]
    cases b <;> simp [Engine.bits,Engine.bit,pushBit,Nat.cast_add,Nat.cast_mul,add_comm]

private theorem encodeLiteral_injective : Function.Injective encodeLiteral := by
  rintro ⟨q,l,r⟩ ⟨q',l',r'⟩ eq
  have states := congrArg (fun n : Nat => π₁ n) eq
  have left := congrArg (fun n : Nat => π₁ (π₂ n)) eq
  have right := congrArg (fun n : Nat => π₂ (π₂ n)) eq
  simp only [encodeLiteral,encode,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair] at states left right
  subst q' l' r'
  rfl

private theorem literalRun_of_totalRun (m : Machine) (n : Nat) (start stop : Configuration)
    (running : stop.state < m.workingStates) (eq : totalRun m n start = stop) :
    run m n start = some stop := by
  induction n generalizing start with
  | zero => exact congrArg some eq
  | succ n ih =>
    cases first : PalomarI3380.step m start with
    | none =>
      have frozen : ∀ k, totalRun m k start = start := by
        intro k
        induction k with
        | zero => rfl
        | succ k step => rw [totalRun_last,step]; simp [totalStep,first]
      rw [frozen] at eq
      subst stop
      exact ((Nat.not_le_of_gt running) ((step_none_iff m start).mp first)).elim
    | some next =>
      have rest : totalRun m n next = stop := by simpa only [totalRun,totalStep,first,Option.getD_some] using eq
      simpa only [run,first] using ih next rest

theorem reach_of_arithmetic {m : Machine} {start stop : Configuration}
    (reach : Reaches m (encodeLiteral start) (encodeLiteral stop))
    (active : stop.state < m.workingStates) :
    ∃ n, run m n start = some stop := by
  obtain ⟨n,path⟩ := reach
  rw [clock_nat] at path
  exact ⟨n,literalRun_of_totalRun m n start stop active (encodeLiteral_injective path)⟩

namespace Reference
open scoped PalomarI3380.Engine

theorem positive_of_arithmetic {start stop : Configuration}
    (reach : Reaches referenceMachine (encodeLiteral start) (encodeLiteral stop))
    (active : stop.state < referenceMachine.workingStates) (changedState : start.state ≠ stop.state) :
    Engine.Progress start stop := by
  obtain ⟨n,runTo⟩ := reach_of_arithmetic reach active
  cases n with
  | zero =>
    have equal : start = stop := Option.some.inj runTo
    exact (changedState (congrArg Configuration.state equal)).elim
  | succ n => exact ⟨n+1,Nat.succ_pos _,runTo⟩


open Engine.Port

theorem registers_cast (values : List Nat) (tail : M) :
    registers (values.map Nat.cast) tail = packWord (Engine.registers values) tail := by
  induction values with
  | nil => rfl
  | cons v values ih =>
    change pushBit false (repeatBit true ((v : M)+1) (registers (values.map Nat.cast) tail)) = _
    rw [← Nat.cast_succ,repeatBit_cast,ih]
    simp only [Engine.registers,List.flatMap_cons,packWord_append]
    rfl

theorem frame_cast (path : List Bool) (gap : Nat) (values : List Nat) :
    frame path (gap : M) (values.map Nat.cast) = ((encodeLiteral (Engine.frame path gap values)) : M) := by
  unfold frame
  rw [registers_cast,repeatBit_cast,← packWord_append,← packWord_append,packWord_bits]
  simpa [cell,Engine.frame,Engine.atRight,encodeLiteral,List.append_assoc,Engine.zeros,
    show Engine.bits [true] = 1 from rfl] using
    encode_cast (M := M) root 1 (Engine.bits (path ++ (Engine.zeros gap ++ Engine.registers values)))

theorem encode_atRight (q : Nat) (l r : List Bool) :
    encodeLiteral (Engine.atRight q l r) =
      cell q (packWord l (0 : Nat)) (packWord r 0) := by
  simp only [Engine.atRight,encodeLiteral,cell,packWord_bits,Arithmetic.natCast_nat]

theorem encode_atLeft (q : Nat) (l r : List Bool) :
    encodeLiteral (Engine.atLeft q l r) =
      fromLeft q (packWord l (0 : Nat)) (packWord r 0) := by
  cases l with
  | nil =>
    rw [Engine.atLeft,List.tail_nil,List.headD_nil,encode_atRight,packWord_nil,packWord_cons]
    rw [← pushBit_false_zero (M := Nat),fromLeft_pushBit,pushBit_false_zero]
    rfl
  | cons b l =>
    rw [Engine.atLeft,List.tail_cons,List.headD_cons,encode_atRight,packWord_cons,packWord_cons,
      fromLeft_pushBit]
    rfl

theorem pack_replicate (bit : Bool) (n : Nat) (l : List Bool) (tail : Nat) :
    packWord (List.replicate n bit ++ l) tail = repeatBit bit n (packWord l tail) := by
  rw [packWord_append,← repeatBit_cast]
  simp only [Arithmetic.natCast_nat]

theorem pack_registers (values : List Nat) (l : List Bool) (tail : Nat) :
    packWord (Engine.registers values ++ l) tail = registers values (packWord l tail) := by
  rw [packWord_append]
  have castId : @Nat.cast Nat (Arithmetic.natCast Nat) = id := funext Arithmetic.natCast_nat
  simpa only [castId,List.map_id] using
    (registers_cast (M := Nat) values (packWord l tail)).symm

theorem pack_replicate_nil (bit : Bool) (n : Nat) (tail : Nat) :
    packWord (List.replicate n bit) tail = repeatBit bit n tail := by
  simpa only [List.append_nil,packWord_nil] using pack_replicate bit n [] tail

theorem pack_registers_nil (values : List Nat) (tail : Nat) :
    packWord (Engine.registers values) tail = registers values tail := by
  simpa only [List.append_nil,packWord_nil] using pack_registers values [] tail

end Reference
end PalomarI3380.ArithmeticMachine
