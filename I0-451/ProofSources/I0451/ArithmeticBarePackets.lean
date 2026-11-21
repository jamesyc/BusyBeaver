module
public import I0451.ArithmeticQueueCode
public import I0451.ArithmeticCommandCoding

/-! Execute a command packet on the proof store independently of its
position in a queue. The packed store uses the same arithmetic coding
as a command boundary, with the two scheduler fields set to zero. -/
@[expose] public section
namespace I0451.Arithmetization

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open _root_.I0451.Runtime
open I0451.Logic (Command ProofStore)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem packModelCommand_surjective (packet : V) : ∃ cmd tail, packModelCommand cmd tail = packet := by
  let selector := cantorLeft packet
  let fields := cantorRight packet
  let arg := cantorLeft fields
  let queue := cantorRight fields
  have head : cantor selector fields = packet := cantor_encode_decode packet
  have parts : cantor arg queue = fields := cantor_encode_decode fields
  have same : cantor selector (cantor arg queue) = packet := by rw [parts, head]
  rcases selector_cases selector with mp | drop | nip | extra | ⟨mode, large⟩
  · rw [mp] at same
    exact ⟨.mp arg, queue, same⟩
  · rw [drop] at same
    exact ⟨.drop arg, queue, same⟩
  · rw [nip] at same
    exact ⟨.nip arg, queue, same⟩
  · rw [extra] at same
    exact ⟨.extra arg, queue, same⟩
  · let y := cantorLeft queue
    let operands := cantorRight queue
    let form := cantorLeft operands
    let tail := cantorRight operands
    have parameters : cantor y operands = queue := cantor_encode_decode queue
    have final : cantor form tail = operands := cantor_encode_decode operands
    refine ⟨.ax mode arg y form, tail, ?_⟩
    change cantor (mode + 4) (cantor arg (cantor y (cantor form tail))) = packet
    rw [final, parameters, ← large, same]

def readModelStore (regs : Fin 9 → V) : ProofStore V :=
  ⟨regs topWff, regs wffStack, regs parameterOne, regs parameterTwo⟩

noncomputable def packModelStore (s : ProofStore V) : V :=
  packBoundary (modelSearchRegisters 0 0 s)

noncomputable def unpackModelStore (code : V) : ProofStore V :=
  readModelStore (unpackBoundary code)

theorem unpack_packModelStore (s : ProofStore V) : unpackModelStore (packModelStore s) = s := by
  unfold unpackModelStore packModelStore
  rw [unpack_packBoundary (modelSearchRegisters_ready _ _ _)]
  cases s
  rfl

@[simp] theorem packModelStore_nonzero (s : ProofStore V) : packModelStore s ≠ 0 :=
  packBoundary_nonzero _

noncomputable def encodeStoreResult (out : Option (ProofStore V)) : V :=
  (out.map packModelStore).getD 0

noncomputable def barePacketStep (packet store : V) : V :=
  if store = 0 then 0 else
    let next := codeOfResult (modelCommandStep (modelSearchRegisters packet 0 (unpackModelStore store)))
    if next = 0 then 0 else packModelStore (unpackModelStore next)

theorem barePacketStep_command (cmd : Command V) (store tail : V) (live : store ≠ 0) :
    barePacketStep (packModelCommand cmd tail) store =
      encodeStoreResult (runModelCommand cmd (unpackModelStore store)) := by
  simp only [barePacketStep, ite_eq_right live, modelCommandStep_fresh]
  cases ran : runModelCommand cmd (unpackModelStore store) with
  | none => simp [codeOfResult, encodeStoreResult]
  | some after =>
    simp only [Option.map_some, codeOfResult_some, ite_eq_right (packBoundary_nonzero _), unpackModelStore,
      unpack_packBoundary (modelSearchRegisters_ready _ _ _), encodeStoreResult, Option.getD]
    cases after
    rfl

theorem barePacketStep_pack (cmd : Command V) (s : ProofStore V) (tail : V) :
    barePacketStep (packModelCommand cmd tail) (packModelStore s) = encodeStoreResult (runModelCommand cmd s) := by
  rw [barePacketStep_command cmd _ _ (packModelStore_nonzero s), unpack_packModelStore]

theorem searchRegisters_modelDefined {k : Nat} (next queue store : (Fin k → V) → V)
    (dn : 𝚺ᴬ₁.DefinableFunction (V := V) next) (dq : 𝚺ᴬ₁.DefinableFunction (V := V) queue)
    (ds : 𝚺ᴬ₁.DefinableFunction (V := V) store) (i : Fin 9) :
    𝚺ᴬ₁.DefinableFunction (V := V) (fun v =>
      modelSearchRegisters (next v) (queue v) (unpackModelStore (store v)) i) := by
  have transfer (j : Fin 9) : 𝚺ᴬ₁.DefinableFunction (V := V) (fun v => unpackBoundary (store v) j) := by
    have field := unpackBoundary_field_defined (V := V) j
    exact Bounding.HierarchySymbol.DefinableFunction₁.comp (F := fun x => unpackBoundary x j) ds
  rcases index_cases i with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact dn
  · exact transfer topWff
  · exact transfer wffStack
  · exact Bounding.HierarchySymbol.DefinableFunction.const 0
  · exact transfer parameterOne
  · exact transfer parameterTwo
  · exact Bounding.HierarchySymbol.DefinableFunction.const 0
  · exact Bounding.HierarchySymbol.DefinableFunction.const 0
  · exact dq

theorem barePacketStep_defined {k : Nat} (packet store : (Fin k → V) → V)
    (dp : 𝚺ᴬ₁.DefinableFunction (V := V) packet) (ds : 𝚺ᴬ₁.DefinableFunction (V := V) store) :
    𝚺ᴬ₁.DefinableFunction (V := V) (fun v => barePacketStep (packet v) (store v)) := by
  let regs (v : Fin k → V) := modelSearchRegisters (packet v) 0 (unpackModelStore (store v))
  let next (v : Fin k → V) := codeOfResult (modelCommandStep (regs v))
  have constant : 𝚺ᴬ₁.DefinableFunction (V := V) (fun _ : Fin k → V => (0 : V)) :=
    Bounding.HierarchySymbol.DefinableFunction.const 0
  have nextDefined : 𝚺ᴬ₁.DefinableFunction (V := V) next :=
    codeOfCommandStep_defined regs (searchRegisters_modelDefined packet _ store dp constant ds)
  have normalized : 𝚺ᴬ₁.DefinableFunction (V := V) (fun v => packModelStore (unpackModelStore (next v))) :=
    packBoundary_definable _ (searchRegisters_modelDefined _ _ next constant constant nextDefined)
  exact arithmeticCompare_defined store _ _ _ ds constant constant
    (arithmeticCompare_defined next _ _ _ nextDefined constant constant normalized)

noncomputable def wordStep (word state : V) : V :=
  ⟪π₁ state + 1, barePacketStep (znth word (π₁ state)) (π₂ state)⟫

theorem wordStep_defined (word : V) :
    𝚺ᴬ₁-Function₁[V] (wordStep word) := by
  have applied := barePacketStep_defined
    (fun v : Fin 1 → V => znth word (π₁ (v 0))) (fun v => π₂ (v 0)) (by definability) (by definability)
  unfold wordStep
  definability

theorem wordStep_binary_defined :
    𝚺ᴬ₁-Function₂[V] (wordStep : V → V → V) := by
  have applied := barePacketStep_defined
    (fun v : Fin 2 → V => znth (v 0) (π₁ (v 1))) (fun v => π₂ (v 1)) (by definability) (by definability)
  unfold wordStep
  definability

theorem wordStep_index {word history start length : V}
    (ran : Iteration (wordStep word) ⟪0, start⟫ history length) :
    ∀ i ≤ length, π₁ (znth history i) = i := by
  exact ran.clock (pi₁_pair _ _) (fun state => by simp [wordStep])

end I0451.Arithmetization
