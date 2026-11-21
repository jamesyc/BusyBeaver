module
public import I0451.ArithmeticCommands

/-! Arithmetic command packets. The four short selectors read one
operand. AX also reads the generalization mode and two formula operands. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Runtime
open I0451.Logic (Command ProofStore)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def packModelCommand (c : Command V) (tail : V) : V :=
  match c with
  | .mp p => cantor 0 (cantor p tail)
  | .drop p => cantor 1 (cantor p tail)
  | .nip p => cantor 2 (cantor p tail)
  | .extra p => cantor 3 (cantor p tail)
  | .ax k p y f => cantor (k + 4) (cantor p (cantor y (cantor f tail)))

def modelSearchRegisters (next queue : V) (s : ProofStore V) : Fin 9 → V :=
  boundaryRegisters next s.top s.stack s.operand s.cache queue

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
@[simp] theorem modelSearchRegisters_ready (next queue : V) (s : ProofStore V) :
    CommandReady (modelSearchRegisters next queue s) :=
  ⟨rfl, rfl, rfl⟩

noncomputable def runModelAxioms (mode y formula : V) (s : ProofStore V) : ProofStore V :=
  let a := s.operand
  let b := s.cache + y
  ⟨if mode = a ∨ mode = b then 0 else modelEncoding.bundle a b mode,
    (modelEncoding.heads a b mode formula).foldr cantor
      (cantor (modelEncoding.all a s.cache) (cantor s.top s.stack)), 0, 0⟩

noncomputable def runModelCommand (c : Command V) (s : ProofStore V) : Option (ProofStore V) :=
  match c with
  | .mp p =>
    let arg := s.operand + p
    if s.cache = modelImp s.top arg then some ⟨arg, cantor 0 s.stack, arg, 0⟩
    else some ⟨0, s.stack, arg, 0⟩
  | .drop p =>
    some ⟨s.cache, cantor s.top s.stack, s.operand + p, s.cache⟩
  | .nip p =>
    if s.cache = 1 then none
    else some ⟨s.top, cantorRight s.stack, s.operand + p, cantorLeft s.stack⟩
  | .extra _ =>
    some ⟨(literalBerkeleyCode : V), cantor (literalFoundationCode : V) (cantor s.top s.stack), 0, 0⟩
  | .ax mode p y formula =>
    some (runModelAxioms mode y formula { s with operand := s.operand + p })

private theorem result_mp (n q : V) (s : ProofStore V) :
    modelCommandResult 0 (modelSearchRegisters n q s) =
      (runModelCommand (.mp 0) s).map (modelSearchRegisters n q) := by
  simp only [modelCommandResult, ite_true, runModelCommand, add_zero, modelMPResult]
  have cache : modelSearchRegisters n q s parameterTwo = s.cache := rfl
  have top : modelSearchRegisters n q s topWff = s.top := rfl
  have operand : modelSearchRegisters n q s parameterOne = s.operand := rfl
  rw [cache, top, operand]
  split <;> congr 1 <;> funext i <;>
    rcases index_cases i with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> rfl

private theorem result_drop (n q : V) (s : ProofStore V) :
    modelCommandResult 1 (modelSearchRegisters n q s) =
      (runModelCommand (.drop 0) s).map (modelSearchRegisters n q) := by
  simp only [modelCommandResult, show (1 : V) ≠ 0 by simp, ite_false, ite_true, runModelCommand,
    add_zero, Option.map_some]
  congr 1
  funext i
  rcases index_cases i with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> rfl

private theorem result_nip (n q : V) (s : ProofStore V) :
    modelCommandResult 2 (modelSearchRegisters n q s) =
      (runModelCommand (.nip 0) s).map (modelSearchRegisters n q) := by
  have cache : modelSearchRegisters n q s parameterTwo = s.cache := rfl
  have n0 : (2 : V) ≠ 0 := by simp
  have n1 : (2 : V) ≠ 1 := by
    simpa only [Nat.cast_ofNat, Nat.cast_one] using
      (mt (fun eq : ((2 : Nat) : V) = ((1 : Nat) : V) => nat_cast_inj.mp eq)
        (by decide : (2 : Nat) ≠ 1))
  simp only [modelCommandResult, n0, n1, ite_false, ite_true, cache, runModelCommand, add_zero]
  split
  · rfl
  · simp only [Option.map_some]
    congr 1
    funext i
    rcases index_cases i with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      first | rfl | exact zero_add _

private theorem result_extra (n q : V) (s : ProofStore V) :
    modelCommandResult 3 (modelSearchRegisters n q s) =
      (runModelCommand (.extra 0) s).map (modelSearchRegisters n q) := by
  have n0 : (3 : V) ≠ 0 := by simp
  have n1 : (3 : V) ≠ 1 := by
    simpa only [Nat.cast_ofNat, Nat.cast_one] using
      (mt (fun eq : ((3 : Nat) : V) = ((1 : Nat) : V) => nat_cast_inj.mp eq)
        (by decide : (3 : Nat) ≠ 1))
  have n2 : (3 : V) ≠ 2 := by
    simpa only [Nat.cast_ofNat, Nat.cast_one] using
      (mt (fun eq : ((3 : Nat) : V) = ((2 : Nat) : V) => nat_cast_inj.mp eq)
        (by decide : (3 : Nat) ≠ 2))
  simp only [modelCommandResult, n0, n1, n2, ite_false, ite_true, runModelCommand, Option.map_some]
  congr 1
  funext i
  rcases index_cases i with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> rfl

private theorem result_axiom (n q y f mode : V) (s : ProofStore V) :
    modelCommandResult (mode + 4) (modelSearchRegisters n (cantor y (cantor f q)) s) =
      (runModelCommand (.ax mode 0 y f) s).map (modelSearchRegisters n q) := by
  have ge : (4 : V) ≤ mode + 4 := by simp
  have n0 : mode + 4 ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) ge)
  have n1 : mode + 4 ≠ 1 := ne_of_gt (lt_of_lt_of_le (by norm_num) ge)
  have n2 : mode + 4 ≠ 2 := ne_of_gt (lt_of_lt_of_le ((Nat.cast_lt (α := V)).mpr (by decide : (2 : Nat) < 4)) ge)
  have n3 : mode + 4 ≠ 3 := ne_of_gt (lt_of_lt_of_le ((Nat.cast_lt (α := V)).mpr (by decide : (3 : Nat) < 4)) ge)
  simp only [modelCommandResult, ite_eq_right n0, ite_eq_right n1, ite_eq_right n2, ite_eq_right n3,
    add_tsub_cancel_right, runModelCommand, Option.map_some, add_zero]
  congr 1
  funext i
  rcases index_cases i with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp [modelAxiomResult, modelSearchRegisters, runModelAxioms, boundaryRegisters, putRegister,
      nextProof, topWff, wffStack, axiomIndex, parameterOne, parameterTwo, scratchOne, scratchTwo, proofList,
      cantorLeft_pair, cantorRight_pair]

private theorem commandInput_pair {n q selector operand tail : V} {s : ProofStore V}
    (input : modelPayload (modelSearchRegisters n q s) = cantor selector (cantor operand tail)) :
    modelCommandInput (modelSearchRegisters n q s) =
      modelSearchRegisters (modelNextIndex (modelSearchRegisters n q s)) tail
        { s with operand := s.operand + operand } := by
  unfold modelCommandInput
  rw [input]
  simp only [cantorRight_pair, cantorLeft_pair]
  funext i
  rcases index_cases i with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> rfl

/-- The command packet's exact update, regardless of whether it was
loaded as a fresh candidate or read from the pending queue. -/
theorem modelCommandStep_packed {n q tail : V} {s : ProofStore V} {cmd : Command V}
    (packet : modelPayload (modelSearchRegisters n q s) = packModelCommand cmd tail) :
    modelCommandStep (modelSearchRegisters n q s) =
      (runModelCommand cmd s).map (modelSearchRegisters (modelNextIndex (modelSearchRegisters n q s)) tail) := by
  let index := modelNextIndex (modelSearchRegisters n q s)
  unfold modelCommandStep
  cases cmd with
  | mp p =>
    have input := commandInput_pair packet
    rw [input, packet, packModelCommand, cantorLeft_pair]
    simpa only [runModelCommand, add_zero] using result_mp index tail {s with operand := s.operand + p}
  | drop p =>
    have input := commandInput_pair packet
    rw [input, packet, packModelCommand, cantorLeft_pair]
    simpa only [runModelCommand, add_zero] using result_drop index tail {s with operand := s.operand + p}
  | nip p =>
    have input := commandInput_pair packet
    rw [input, packet, packModelCommand, cantorLeft_pair]
    simpa only [runModelCommand, add_zero] using result_nip index tail {s with operand := s.operand + p}
  | extra p =>
    have input := commandInput_pair packet
    rw [input, packet, packModelCommand, cantorLeft_pair]
    simpa only [runModelCommand] using result_extra index tail {s with operand := s.operand + p}
  | ax mode p y f =>
    have input := commandInput_pair packet
    rw [input, packet, packModelCommand, cantorLeft_pair]
    simpa only [runModelCommand, add_zero] using result_axiom index tail y f mode {s with operand := s.operand + p}

theorem modelCommandStep_queued (n tail : V) (cmd : Command V) (s : ProofStore V) :
    modelCommandStep (modelSearchRegisters n (packModelCommand cmd tail + 1) s) =
      (runModelCommand cmd s).map (modelSearchRegisters n tail) := by
  have live : packModelCommand cmd tail + 1 ≠ 0 := by simp
  have q : modelSearchRegisters n (packModelCommand cmd tail + 1) s proofList = packModelCommand cmd tail + 1 := rfl
  have input : modelPayload (modelSearchRegisters n (packModelCommand cmd tail + 1) s) =
      packModelCommand cmd tail := by rw [modelPayload, q, ite_eq_right live, add_tsub_cancel_right]
  have next : modelNextIndex (modelSearchRegisters n (packModelCommand cmd tail + 1) s) = n := by
    rw [modelNextIndex, q, ite_eq_right live]
    rfl
  simpa only [next] using modelCommandStep_packed input

theorem modelCommandStep_fresh (tail : V) (cmd : Command V) (s : ProofStore V) :
    modelCommandStep (modelSearchRegisters (packModelCommand cmd tail) 0 s) =
      (runModelCommand cmd s).map (modelSearchRegisters (packModelCommand cmd tail + 1) tail) := by
  have payload : modelPayload (modelSearchRegisters (packModelCommand cmd tail) 0 s) =
      packModelCommand cmd tail := by
    simp [modelPayload, modelSearchRegisters, boundaryRegisters, proofList, nextProof]
  have next : modelNextIndex (modelSearchRegisters (packModelCommand cmd tail) 0 s) =
      packModelCommand cmd tail + 1 := by
    simp [modelNextIndex, modelSearchRegisters, boundaryRegisters, proofList, nextProof]
  simpa only [next] using modelCommandStep_packed payload

end I0451.Arithmetization
