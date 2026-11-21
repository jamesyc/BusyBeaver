module
public import I3_380.Search.Compiler.Forward
public import I3_380.Engine.Logical
@[expose] public section

namespace PalomarI3380.Compiler

open Engine (Exit Decoded height transition exitFor follow zeros)

def sourceOp : Exit → Op
  | .register false r => .inc r
  | .register true r => .decNZ r
  | .break skip => .break_ (if skip then 1 else 0)
  | .continue skip => .continue_ (if skip then 1 else 0)
  | .halt => .halt

private def exitFlags (b : Bool) : Exit → Bool
  | .break skip => skip && b
  | .continue _ => b
  | _ => true

private def legalReference : Bool :=
  (List.range 394).all fun q =>
    if 0 < height q then [false, true].all fun b =>
      (exitFor (transition q b).target).all (exitFlags b)
    else true

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem checked_reference : legalReference = true := by decide +kernel

private theorem decoded_flags {input scanned : List Bool} {d : Decoded}
    (h : Engine.DecodedFrom 59 Engine.Port.root [] input scanned d) : exitFlags d.read d.command = true := by
  obtain ⟨range, active, decoded⟩ := h.leaf
  have check := List.all_eq_true.mp checked_reference _ (List.mem_range.mpr range)
  have bits := List.all_eq_true.mp (by simpa only [active, ↓reduceIte] using check) d.read
    (by cases d.read <;> simp)
  change (exitFor (transition d.node d.read).target).all (exitFlags d.read) = true at bits
  change exitFor (transition d.node d.read).target = some d.command at decoded
  simpa only [decoded, Option.all_some] using bits

/-- The shared decoder DAG, unfolded into a binary program. An edge is
decoded from the literal reference rows, including its register or jump. -/
def tableNode : Nat → Nat → Program
  | 0, _ => .op .halt
  | fuel + 1, q =>
    let child := fun b =>
      let edge := transition q b
      if 0 < height edge.target then tableNode fuel edge.target
      else .op (sourceOp ((exitFor edge.target).getD .halt))
    .seq (child false) (child true)

def referenceProgram : Program := tableNode 59 Engine.Port.root

theorem tableNode_walk {fuel q : Nat} {before input : List Bool} {d : Decoded}
    (h : follow fuel q before input = some d) :
    (walk (tableNode fuel q) input).1 = sourceOp d.command ∧
      before.reverse ++ (walk (tableNode fuel q) input).2 = d.path := by
  induction fuel generalizing q before input d with
  | zero => simp [follow] at h
  | succ fuel ih =>
    cases input with
    | nil => simp [follow] at h
    | cons b rest =>
      have walkBranch :
          walk (tableNode (fuel + 1) q) (b :: rest) =
            let edge := transition q b
            let child := if 0 < height edge.target then tableNode fuel edge.target
                else .op (sourceOp ((exitFor edge.target).getD .halt))
            let result := walk child rest
            (result.1, b :: result.2) := by
        cases b <;> simp only [tableNode, walk, List.headD_cons, List.tail_cons,
          Bool.false_eq_true, ↓reduceIte]
      rw [walkBranch]
      by_cases deeper : 0 < height (transition q b).target
      · have child : follow fuel (transition q b).target (b :: before) rest = some d := by
          simpa only [follow, deeper, ↓reduceIte] using h
        have below := ih child
        simp only [deeper, ↓reduceIte]
        exact ⟨below.1, by simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using below.2⟩
      · cases exit : exitFor (transition q b).target with
        | none => simp [follow, deeper, exit] at h
        | some op =>
          simp only [follow, deeper, ↓reduceIte, exit, Option.map_some, Option.some.injEq] at h
          subst d
          simp only [deeper, ↓reduceIte, exit, Option.getD_some, walk, Decoded.path, true_and]

def storeOf {V : Type} [OfNat V 0] (allRegisters : List V) : Store V :=
  fun r => allRegisters[allRegisters.length - (r.val + 1)]?.getD 0

def project {V : Type} [OfNat V 0] (s : Engine.LogicalState V) : PathState V := atPath s.path (storeOf s.registers)

theorem storeOf_set {V : Type} [OfNat V 0] (rs : List V) (hLen : 12 ≤ rs.length) (p : Register) (value : V) :
    storeOf (rs.set (rs.length - (p.val + 1)) value) = (storeOf rs).set p value := by
  funext r
  unfold storeOf Store.set
  simp only [List.length_set]
  by_cases eq : r = p
  · subst r
    have idx : rs.length - (p.val + 1) < rs.length := by have h := p.isLt; omega
    simp only [List.getElem?_set_self idx, Option.getD_some, ↓reduceIte]
  · have different : rs.length - (r.val + 1) ≠ rs.length - (p.val + 1) := by
      intro same
      apply eq
      apply Fin.ext
      have hr := r.isLt
      have hp := p.isLt
      omega
    simp only [eq, ↓reduceIte, List.getElem?_set_ne different.symm]

theorem project_reference_step {V : Type} [OfNat V 0] [OfNat V 1] [Add V] [Sub V] [DecidableEq V]
    (s : Engine.LogicalState V) (hLen : 12 ≤ s.registers.length) :
    (Engine.logicalNext s).map project = step referenceProgram (project s) := by
  obtain ⟨d, hd⟩ := Engine.decode_root (s.path ++ zeros 59)
    (by simp only [Engine.zeros, List.length_append, List.length_replicate]; omega)
  have evidence := Engine.decode_facts _ hd
  have flags := decoded_flags evidence
  have walkEq := tableNode_walk hd
  have walkRef : walk referenceProgram s.path = (sourceOp d.command, d.path) := by
    have hWalk : walk referenceProgram (s.path ++ zeros 59) = (sourceOp d.command, d.path) :=
      Prod.ext walkEq.1 walkEq.2
    simpa only [walk_zeros] using hWalk
  simp only [Engine.logicalNext, hd, Option.bind_some, step, project, atPath, walk_trim, walkRef]
  cases command : d.command with
  | halt => simp [Engine.logicalDecoded, command, sourceOp, Op.effect]
  | «break» skip =>
    simp only [command, exitFlags, Bool.and_eq_true] at flags
    obtain ⟨rfl, readOne⟩ := flags
    simp [command, Engine.logicalDecoded, sourceOp, Op.effect, project, destination, atPath,
      Engine.breakPath, Decoded.path, List.reverse_append, readOne, stripMany, Engine.stripThrough]
  | «continue» skip =>
    simp only [command, exitFlags] at flags
    cases skip <;> simp [command, Engine.logicalDecoded, sourceOp, Op.effect, project,
      destination, atPath, Decoded.path, List.reverse_append, flags, stripMany, Engine.stripThrough]
  | register dec r =>
    let value := storeOf s.registers r
    have update (new : V) := storeOf_set s.registers hLen r new
    cases dec with
    | false =>
      simp [command, Engine.logicalDecoded, sourceOp, Op.effect, project, Engine.registerValue,
        Engine.zeroDecrement, destination, atPath, incrementPath, Engine.breakPath, update, storeOf]
    | true =>
      by_cases zero : value = 0
      · have reset : (storeOf s.registers).set r 0 = storeOf s.registers := by
          rw [← zero]
          exact Store.set_same _ _
        have hZero : s.registers[s.registers.length - (r.val + 1)]?.getD 0 = 0 := zero
        simp [command, Engine.logicalDecoded, sourceOp, Op.effect, project, Engine.registerValue,
          Engine.zeroDecrement, destination, atPath, Engine.breakPath, update, hZero, reset,
          storeOf, stripMany]
      · have hValue : s.registers[s.registers.length - (r.val + 1)]?.getD 0 ≠ 0 := zero
        simp [command, Engine.logicalDecoded, sourceOp, Op.effect, project, Engine.registerValue,
          Engine.zeroDecrement, destination, atPath, incrementPath, Engine.breakPath, update, hValue, storeOf]

theorem logical_count {s t : Engine.LogicalState}
    (h : Engine.logicalNext s = some t) : 12 ≤ s.registers.length → 12 ≤ t.registers.length := by
  intro hLen
  cases decoded : follow 59 Engine.Port.root [] (s.path ++ zeros 59) with
  | none => simp [Engine.logicalNext, decoded] at h
  | some d =>
    cases command : d.command with
    | halt => simp [Engine.logicalNext, decoded, Engine.logicalDecoded, command] at h
    | «break» skip =>
      simp only [Engine.logicalNext, decoded, Option.bind_some, Engine.logicalDecoded, command,
        Option.some.injEq] at h
      rw [← h]
      exact hLen
    | «continue» skip =>
      cases skip <;>
        simp only [Engine.logicalNext, decoded, Option.bind_some, Engine.logicalDecoded, command,
          Option.some.injEq] at h <;> rw [← h] <;> exact hLen
    | register dec r =>
      simp only [Engine.logicalNext, decoded, Option.bind_some, Engine.logicalDecoded, command,
        Option.some.injEq] at h
      rw [← h]
      simpa only [List.length_set] using hLen

theorem initial_store : storeOf Engine.initialState.registers = fun _ => 0 := by
  have checked : ∀ r : Register, storeOf Engine.initialState.registers r = 0 := by decide +kernel
  exact funext checked

/-- The exact blank-tape machine and the decoded binary register program
have the same termination behavior from zeroed logical registers. -/
theorem literal_halts_iff_reference_program :
    HaltsFrom machine blank ↔ Terminates (step referenceProgram) (atPath [] (fun _ => 0)) := by
  have hLen : 12 ≤ Engine.initialState.logical.registers.length := by
    simp only [Engine.RegisterState.logical, Engine.initialState, List.length_append,
      List.length_replicate, List.length_singleton]
    decide
  have eq := Terminates.map_iff (small := Engine.logicalNext) (large := step referenceProgram)
    project (fun s => 12 ≤ s.registers.length) project_reference_step
    (fun h₁ h₂ => logical_count h₂ h₁) hLen
  have initial : project Engine.initialState.logical = atPath [] (fun _ => 0) := by
    change atPath [] (storeOf Engine.initialState.registers) = _
    rw [initial_store]
  rw [initial] at eq
  exact Engine.literal_halts_iff_logical.trans eq

end PalomarI3380.Compiler
