module
public import I3_334.Tape.ControlWords
public import I3_334Support.Search.Compiler.Program
@[expose] public section

namespace PalomarI3334.Decoder

open PalomarI3380
open Control (root boundedZeros dispatch breakPort continuePort)
open Engine (leadingZeros)
open ArithmeticMachine
open ArithmeticMachine.Reference (cell)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

structure Transition where
  target : Nat
  write : Bool
  right : Bool
  deriving DecidableEq, Repr

def transition (q : Nat) (b : Bool) : Transition :=
  let row := decoderReference.row q b.toNat
  ⟨row / 4, row / 2 % 2 == 1, row % 2 == 1⟩

theorem transition_row (q : Fin 344) (b : Bool) :
    Stock.Row decoderReference q.val b (transition q b).write
      (transition q b).right (transition q b).target := by
  refine ⟨q.isLt, ?_⟩
  unfold transition
  generalize decoderReference.row q.val b.toNat = data
  have lo : data % 2 < 2 := Nat.mod_lt _ (by decide)
  have hi : data / 2 % 2 < 2 := Nat.mod_lt _ (by decide)
  have bit (n : Nat) (small : n < 2) : (n == 1).toNat = n := by
    have cases : n = 0 ∨ n = 1 := by omega
    rcases cases with rfl | rfl <;> rfl
  rw [bit _ hi, bit _ lo]
  change data = 4 * (data / 4) + 2 * (data / 2 % 2) + data % 2
  omega

def registerPort (dec : Bool) (r : Nat) : Nat :=
  let ports := if dec then referenceDecPorts else referenceIncPorts
  ports[r]?.getD 344

inductive Exit where
  | register (dec : Bool) (rank : Fin 11)
  | break (skip : Bool)
  | continue (skip : Fin 5)
  | halt
  deriving DecidableEq, Repr

def Exit.port : Exit → Nat
  | .register dec r => registerPort dec r.val
  | .break skip => breakPort skip
  | .continue skip => continuePort skip.val
  | .halt => 344

theorem Exit.port_ne_root (op : Exit) : op.port ≠ root := by
  cases op with
  | register dec rank => revert dec rank; decide +kernel
  | «break» skip => cases skip <;> decide +kernel
  | «continue» skip => revert skip; decide +kernel
  | halt => decide +kernel

def Exit.op : Exit → Compiler.Op
  | .register false r => .inc ⟨r.val, by have h := r.isLt; omega⟩
  | .register true r => .decNZ ⟨r.val, by have h := r.isLt; omega⟩
  | .break skip => .break_ skip.toNat
  | .continue skip => .continue_ skip.val
  | .halt => .halt

def exitAt (q : Nat) : Option Exit :=
  let special := [.halt, .break false, .break true] ++ (List.finRange 5).map Exit.continue
  let registers := (List.finRange 11).flatMap fun r => [.register false r, .register true r]
  (special ++ registers).find? fun op => op.port == q

theorem exit_port {q : Nat} {op : Exit} (h : exitAt q = some op) : op.port = q :=
  beq_iff_eq.mp (List.find?_some (p := fun item : Exit => item.port == q) h)

def height (q : Nat) : Nat := (referenceDecoderShape >>> (13 * q)) % 128
def zeroBound (q : Nat) : Nat := (referenceDecoderShape >>> (13 * q + 7)) % 8
def oneBound (q : Nat) : Nat := (referenceDecoderShape >>> (13 * q + 10)) % 8

def extendedZeros (q : Nat) (b : Bool) : Nat := if b then 0 else zeroBound q + 1

def checkEdge (q : Nat) (b : Bool) : Bool :=
  let e := transition q b
  if 0 < height e.target then
    (e.write == b) && e.right && decide (e.target < 344) && decide (height e.target < height q) &&
      decide (extendedZeros q b ≤ 5) && decide (extendedZeros q b ≤ zeroBound e.target) &&
      decide (oneBound e.target ≤ oneBound q + b.toNat)
  else
    match exitAt e.target with
    | some (.register _ _) => (e.write == b) && e.right && decide (extendedZeros q b ≤ 5)
    | some (.break skip) => !e.right && !e.write && skip && b
    | some (.continue k) => !e.right && !e.write && b && decide (k.val ≤ oneBound q)
    | some .halt => e.right
    | none => false

def checkGraph : Bool :=
  (List.range 344).all fun q => if 0 < height q then checkEdge q false && checkEdge q true else true

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem checkedGraph : checkGraph = true := by decide +kernel

theorem checked_edge (q : Fin 344) (b : Bool) (active : 0 < height q.val) :
    checkEdge q b = true := by
  have check := List.all_eq_true.mp checkedGraph _ (List.mem_range.mpr q.isLt)
  simp only [active, ↓reduceIte, Bool.and_eq_true] at check
  cases b
  · exact check.1
  · exact check.2

structure PrefixValid (q : Nat) (before : List Bool) : Prop where
  limited : boundedZeros 0 before = true
  zeros : leadingZeros before ≤ zeroBound q
  ones : oneBound q ≤ Control.ones before

theorem extend_limited {q : Nat} {b : Bool} {before : List Bool} (invariant : PrefixValid q before)
    (good : extendedZeros q b ≤ 5) : boundedZeros 0 (b :: before) = true := by
  cases b
  · have zeros := invariant.zeros
    simp only [extendedZeros, Bool.false_eq_true, ↓reduceIte] at good
    have follow := Control.boundedZeros_of_leading before 1 invariant.limited (by omega)
    simp only [boundedZeros, show (0 : Nat) < 5 by decide, decide_true, Bool.true_and]
    exact follow
  · exact invariant.limited

theorem interior (q : Fin 344) (b : Bool) (before : List Bool) (active : 0 < height q.val)
    (invariant : PrefixValid q before) (inside : 0 < height (transition q b).target) :
    let e := transition q b
    e.write = b ∧ e.right = true ∧ e.target < 344 ∧ height e.target < height q.val ∧
      PrefixValid e.target (b :: before) := by
  have checked := checked_edge q b active
  simp only [checkEdge, inside, ↓reduceIte, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at checked
  obtain ⟨⟨⟨⟨⟨⟨write, right⟩, range⟩, rank⟩, zeros⟩, nextZeros⟩, ones⟩ := checked
  refine ⟨write, right, range, rank, extend_limited invariant zeros, ?_, ?_⟩
  · cases b
    · have trailing := invariant.zeros
      simp only [extendedZeros, Bool.false_eq_true, ↓reduceIte, leadingZeros] at nextZeros ⊢
      omega
    · exact Nat.zero_le _
  · have old := invariant.ones
    simp only [Control.ones]
    omega

def LeafShape (q : Nat) (b : Bool) (before : List Bool) : Exit → Prop
  | .register _ _ => (transition q b).write = b ∧ (transition q b).right = true ∧
      boundedZeros 0 (b :: before) = true
  | .break skip => (transition q b).right = false ∧ (transition q b).write = false ∧
      skip = true ∧ b = true ∧ boundedZeros 0 before = true
  | .continue skip => (transition q b).right = false ∧ (transition q b).write = false ∧
      b = true ∧ skip.val ≤ Control.ones before ∧ boundedZeros 0 before = true
  | .halt => (transition q b).right = true

theorem leaf (q : Fin 344) (b : Bool) (before : List Bool) (active : 0 < height q.val)
    (invariant : PrefixValid q before) (last : ¬ 0 < height (transition q b).target)
    {op : Exit} (exit : exitAt (transition q b).target = some op) : LeafShape q b before op := by
  have checked := checked_edge q b active
  simp only [checkEdge, last, ↓reduceIte, exit] at checked
  cases op with
  | register _ _ =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at checked
    exact ⟨checked.1.1, checked.1.2, extend_limited invariant checked.2⟩
  | «break» skip =>
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at checked
    exact ⟨checked.1.1.1, checked.1.1.2, checked.1.2, checked.2, invariant.limited⟩
  | «continue» skip =>
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at checked
    exact ⟨checked.1.1.1, checked.1.1.2, checked.1.2, Nat.le_trans checked.2 invariant.ones, invariant.limited⟩
  | halt => exact checked

structure Result where
  node : Fin 344
  before : List Bool
  read : Bool
  rest : List Bool
  command : Exit
  deriving DecidableEq, Repr

def Result.path (d : Result) : List Bool := d.before.reverse ++ [d.read]

def follow : Nat → Nat → List Bool → List Bool → Option Result
  | 0, _, _, _ => none
  | _ + 1, _, _, [] => none
  | remaining + 1, q, before, b :: rest =>
    if range : q < 344 then
      let next := (transition q b).target
      if 0 < height next then follow remaining next (b :: before) rest
      else (exitAt next).map fun op => ⟨⟨q, range⟩, before, b, rest, op⟩
    else none

/-- Valid prefixes read only inside the decoder, possibly ending at its exit. -/
def ValidPrefix (q : Nat) : List Bool → Prop
  | [] => True
  | b :: rest => 0 < height q ∧ ValidPrefix (transition q b).target rest

noncomputable def Result.destination {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (d : Result) (left tail : M) : M :=
  let e := transition d.node d.read
  let l := packWord d.before left
  if e.right then cell e.target (pushBit e.write l) tail
  else fromLeft e.target l (pushBit e.write tail)

structure Decodes (q : Nat) (before input : List Bool) (d : Result) where
  scanned : List Bool
  consumed : scanned ++ d.rest = input
  path : before.reverse ++ scanned = d.path
  bounded : input.length ≤ height q + d.rest.length
  leaf : LeafShape d.node d.read d.before d.command
  target : (transition d.node d.read).target = d.command.port
  invariant : ValidPrefix q scanned
  covers : ∀ stem tail, ValidPrefix q stem → stem ++ tail = input → stem.length ≤ scanned.length
  run : ∀ {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (left tail : M),
    Reaches decoderReference (cell q (packWord before left) (packWord scanned tail))
      (d.destination left tail)

/-- A walk uses the literal read-only rows. Its trace is valid with arbitrary
arithmetic-model tape beyond the last bit read. -/
theorem follow_facts (fuel : Nat) (q : Fin 344) (before input : List Bool)
    (active : 0 < height q.val) (valid : PrefixValid q before)
    {d : Result} (found : follow fuel q before input = some d) :
    Nonempty (Decodes q before input d) := by
  induction fuel generalizing q before input d with
  | zero => simp [follow] at found
  | succ fuel ih =>
    cases input with
    | nil => simp [follow] at found
    | cons b rest =>
      let e := transition q b
      have row := transition_row q b
      by_cases deeper : 0 < height e.target
      · obtain ⟨write, right, range, rank, invariant⟩ := interior q b before active valid deeper
        have sub : follow fuel e.target (b :: before) rest = some d := by
          simpa only [follow, q.isLt, dite_true, show 0 < height (transition q b).target from deeper,
            ↓reduceIte] using found
        obtain ⟨facts⟩ := ih ⟨e.target, range⟩ _ _ deeper invariant sub
        refine ⟨⟨b :: facts.scanned, ?_, ?_, ?_, facts.leaf, facts.target, ⟨active, facts.invariant⟩, ?_, ?_⟩⟩
        · rw [List.cons_append, facts.consumed]
        · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using facts.path
        · have bounded := facts.bounded
          change rest.length ≤ height e.target + d.rest.length at bounded
          change height e.target < height q.val at rank
          simp only [List.length_cons]
          omega
        · intro stem tail check joined
          cases stem with
          | nil => exact Nat.zero_le _
          | cons first stem =>
            simp only [List.cons_append, List.cons.injEq] at joined
            obtain ⟨rfl, joined⟩ := joined
            exact Nat.succ_le_succ (facts.covers stem tail check.2 joined)
        · intro M _ _ left tail
          have move : Stock.Row decoderReference q.val b b true e.target := by rwa [write, right] at row
          exact (Stock.right move _ _).trans (facts.run left tail)
      · cases exit : exitAt e.target with
        | none =>
          simp only [follow, q.isLt, dite_true, show ¬ 0 < height (transition q b).target from deeper,
            ↓reduceIte, show exitAt (transition q b).target = none from exit, Option.map_none] at found
          contradiction
        | some op =>
          have eq : (⟨q, before, b, rest, op⟩ : Result) = d := by
            simpa only [follow, q.isLt, dite_true, show ¬ 0 < height (transition q b).target from deeper,
              ↓reduceIte, show exitAt (transition q b).target = some op from exit,
              Option.map_some, Option.some.injEq] using found
          subst d
          refine ⟨⟨[b], rfl, rfl, ?_, leaf q b before active valid deeper exit, (exit_port exit).symm,
            ⟨active, trivial⟩, ?_, ?_⟩⟩
          · simp only [List.length_cons]
            omega
          · intro stem tail check joined
            cases stem with
            | nil => exact Nat.zero_le _
            | cons first stem =>
              simp only [List.cons_append, List.cons.injEq] at joined
              obtain ⟨rfl, _⟩ := joined
              cases stem with
              | nil => exact Nat.le_refl _
              | cons second stem => exact (deeper check.2.1).elim
          · intro M _ _ left tail
            by_cases right : e.right = true
            · have move : Stock.Row decoderReference q.val b e.write true e.target := by rwa [right] at row
              simpa only [Result.destination, packWord_cons, packWord_nil,
                show (transition q b).right = true from right, ↓reduceIte] using
                Stock.right move (packWord before left) tail
            · have direction : e.right = false := Bool.of_not_eq_true right
              have move : Stock.Row decoderReference q.val b e.write false e.target := by rwa [direction] at row
              simpa only [Result.destination, packWord_cons, packWord_nil,
                show (transition q b).right = false from direction, Bool.false_eq_true, ↓reduceIte] using
                Stock.left move (packWord before left) tail

theorem follow_exists (fuel : Nat) (q : Fin 344) (before input : List Bool)
    (active : 0 < height q.val) (valid : PrefixValid q before)
    (enoughFuel : height q.val ≤ fuel) (enoughInput : height q.val ≤ input.length) :
    ∃ d, follow fuel q before input = some d := by
  induction fuel generalizing q before input with
  | zero => omega
  | succ fuel ih =>
    cases input with
    | nil => simp at enoughInput; omega
    | cons b rest =>
      by_cases deeper : 0 < height (transition q b).target
      · obtain ⟨_, _, range, rank, invariant⟩ := interior q b before active valid deeper
        have len : height (transition q b).target ≤ rest.length := by
          simp only [List.length_cons] at enoughInput
          omega
        have childFuel : height (transition q b).target ≤ fuel := by
          change height (transition q b).target < height q.val at rank
          omega
        simpa only [follow, q.isLt, dite_true, deeper, ↓reduceIte] using
          ih ⟨(transition q b).target, range⟩ _ _ deeper invariant childFuel len
      · have checked := checked_edge q b active
        cases exit : exitAt (transition q b).target with
        | none => simp [checkEdge, deeper, exit] at checked
        | some op =>
          exact ⟨⟨q, before, b, rest, op⟩,
            by simp only [follow, q.isLt, dite_true, deeper, ↓reduceIte, exit, Option.map_some]⟩

theorem root_shape : height root = 70 ∧ PrefixValid root [] := by
  constructor
  · decide +kernel
  · constructor <;> decide +kernel

theorem decode (input : List Bool) (size : 70 ≤ input.length) :
    ∃ d, follow 70 root [] input = some d ∧ Nonempty (Decodes root [] input d) := by
  have rank := root_shape.1
  have active : 0 < height root := by omega
  let q : Fin 344 := ⟨root, by decide⟩
  have qrank : height q.val = 70 := rank
  obtain ⟨d, found⟩ := follow_exists 70 q [] input active root_shape.2 (by omega) (by omega)
  exact ⟨d, found, follow_facts 70 q [] input active root_shape.2 found⟩

end PalomarI3334.Decoder
