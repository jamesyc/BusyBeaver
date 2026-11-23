module
public import I3_334Support.Search.Compiler.Program
public import I3_334Support.Engine.ControlWords
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.DropRight
@[expose] public section

namespace PalomarI3380.Compiler

open Engine (incrementReversed stripThrough zeros)

def trimPC (path : List Bool) : List Bool := (path.reverse.dropWhile (!·)).reverse

theorem trimPC_append_zero (path : List Bool) : trimPC (path ++ [false]) = trimPC path := by
  simp [trimPC, List.reverse_append]

theorem trimPC_padding (p : List Bool) : ∃ n, p = trimPC p ++ zeros n := by
  let leading := p.reverse.takeWhile (!·)
  have zerosOnly : leading = zeros leading.length := (List.eq_replicate_length (l := leading)).mpr (by
    intro bit mem
    have dropped : !bit = true := List.mem_takeWhile_imp mem
    cases bit <;> simp_all)
  refine ⟨leading.length, ?_⟩
  have split := congrArg List.reverse
    (List.takeWhile_append_dropWhile (p := (!·)) (l := p.reverse))
  change (leading ++ p.reverse.dropWhile (!·)).reverse = p.reverse.reverse at split
  rw [List.reverse_append, List.reverse_reverse, zerosOnly, Engine.reverse_zeros] at split
  exact split.symm

/-- A path may stop at a sequence node, or exactly at an instruction. -/
def locate (p : Program) : List Bool → Option Program
  | [] => some p
  | b :: rest =>
    match p with
    | .op _ => none
    | .seq lhs rhs => locate (if b then rhs else lhs) rest

theorem locate_append (root : Program) (p q : List Bool) :
    locate root (p ++ q) = (locate root p).bind (fun child => locate child q) := by
  induction p generalizing root with
  | nil => rfl
  | cons b p ih =>
    cases root with
    | op _ => rfl
    | seq left right => exact ih _

theorem locate_left {root l r : Program} {p : List Bool} (h : locate root p = some (.seq l r)) :
    locate root (p ++ [false]) = some l := by
  rw [locate_append, h]
  rfl

theorem locate_right {root l r : Program} {p : List Bool} (h : locate root p = some (.seq l r)) :
    locate root (p ++ [true]) = some r := by
  rw [locate_append, h]
  rfl

/-- Follow the decoder with implicit zero padding, recording precisely the
bits it reads. -/
def walk : Program → List Bool → Op × List Bool
  | .op op, _ => (op, [])
  | .seq lhs rhs, path =>
    let bit := path.headD false
    if bit then
      let result := walk rhs path.tail
      (result.1, true :: result.2)
    else
      let result := walk lhs path.tail
      (result.1, false :: result.2)

theorem walk_zeros (p : Program) (pc : List Bool) (n : Nat) :
    walk p (pc ++ zeros n) = walk p pc := by
  induction p generalizing pc n with
  | op _ => rfl
  | seq left right ihL ihR =>
    cases pc with
    | nil =>
      cases n with
      | zero => rfl
      | succ n =>
        have h : walk left (zeros n) = walk left [] := ihL [] n
        change ((walk left (zeros n)).1, false :: (walk left (zeros n)).2) =
          ((walk left []).1, false :: (walk left []).2)
        rw [h]
    | cons b rest =>
      cases b
      · simp only [List.cons_append, walk, List.headD_cons, List.tail_cons,
          Bool.false_eq_true, ↓reduceIte, ihL]
      · simp only [List.cons_append, walk, List.headD_cons, List.tail_cons, ↓reduceIte, ihR]

theorem walk_trim (p : Program) (path : List Bool) : walk p (trimPC path) = walk p path := by
  obtain ⟨n, eq⟩ := trimPC_padding path
  have h := walk_zeros p (trimPC path) n
  rw [← eq] at h
  exact h.symm

theorem walk_located {root subtree : Program} {path : List Bool} (h : locate root path = some subtree)
    (rest : List Bool) :
    walk root (path ++ rest) =
      ((walk subtree rest).1, path ++ (walk subtree rest).2) := by
  induction path generalizing root with
  | nil =>
    have eq : root = subtree := Option.some.inj h
    subst root
    rfl
  | cons b path ih =>
    cases root with
    | op op => simp [locate] at h
    | seq left right =>
      cases b
      · have eq := ih (root := left) h
        simp only [List.cons_append, walk, List.headD_cons, List.tail_cons, Bool.false_eq_true,
          ↓reduceIte, eq]
      · have eq := ih (root := right) h
        simp only [List.cons_append, walk, List.headD_cons, List.tail_cons, ↓reduceIte, eq]

def stripMany (bit : Bool) : Nat → List Bool → List Bool
  | 0, path => path
  | k + 1, path => stripMany bit k (stripThrough bit path)

def incrementPath (p : List Bool) : List Bool := (incrementReversed p.reverse).reverse

def destination (path : List Bool) : Flow → List Bool
  | .normal => incrementPath path
  | .escape k => (incrementReversed (stripMany false (k + 1) path.reverse)).reverse
  | .repeatAt k => (stripMany true (k + 1) path.reverse).reverse
  | .halt => path

theorem increment_left (p : List Bool) : incrementPath (p ++ [false]) = p ++ [true] := by
  simp only [incrementPath, List.reverse_append, List.reverse_nil, List.nil_append, List.singleton_append,
    incrementReversed, List.reverse_cons, List.reverse_reverse]

theorem increment_right (p : List Bool) : incrementPath (p ++ [true]) = incrementPath p ++ [false] := by
  simp only [incrementPath, List.reverse_append, List.reverse_nil, List.nil_append, List.singleton_append,
    incrementReversed, List.reverse_cons]

theorem stripMany_hit (bit : Bool) (k : Nat) (p : List Bool) :
    stripMany bit (k + 1) (bit :: p) = stripMany bit k p := by
  simp only [stripMany, stripThrough, ↓reduceIte]

theorem stripMany_miss {hit other : Bool} (different : other ≠ hit) (k : Nat) (p : List Bool) :
    stripMany hit (k + 1) (other :: p) = stripMany hit (k + 1) p := by
  rw [stripMany, stripThrough, ite_eq_right different]
  rfl

theorem destination_left_exit (p : List Bool) {input output : Flow}
    (exit : input.fromLeft = some output) :
    trimPC (destination (p ++ [false]) input) = trimPC (destination p output) := by
  cases input with
  | normal => cases exit
  | halt => cases exit; exact trimPC_append_zero p
  | repeatAt n =>
    cases exit
    simp only [destination,List.reverse_append,List.reverse_singleton,List.singleton_append,
      stripMany_miss (by decide : false ≠ true)]
  | escape n =>
    cases n with
    | zero =>
      cases exit
      simp only [destination,List.reverse_append,List.reverse_singleton,List.singleton_append,
        stripMany,incrementPath,stripThrough,↓reduceIte]
    | succ n =>
      cases exit
      simp only [destination,List.reverse_append,List.reverse_singleton,List.singleton_append,stripMany_hit]

theorem destination_right_exit (p : List Bool) {input output : Flow}
    (exit : input.fromRight = some output) (continuing : output ≠ .halt) :
    trimPC (destination (p ++ [true]) input) = trimPC (destination p output) := by
  cases input with
  | normal => cases exit; simp only [destination,increment_right,trimPC_append_zero]
  | halt => cases exit; exact (continuing rfl).elim
  | repeatAt n =>
    cases n with
    | zero => cases exit
    | succ n =>
      cases exit
      simp only [destination,List.reverse_append,List.reverse_singleton,List.singleton_append,stripMany_hit]
  | escape n =>
    cases exit
    simp only [destination,List.reverse_append,List.reverse_singleton,List.singleton_append,
      stripMany_miss (by decide : true ≠ false)]

theorem destination_right_loop (p : List Bool) :
    destination (p ++ [true]) (.repeatAt 0) = p := by
  simp only [destination,List.reverse_append,List.reverse_singleton,List.singleton_append,
    stripMany,stripThrough,↓reduceIte,List.reverse_reverse]

structure PathState (V : Type := Nat) where
  pc : List Bool
  registers : Store V

def atPath {V : Type} (p : List Bool) (s : Store V) : PathState V := ⟨trimPC p, s⟩

def step {V : Type} [OfNat V 0] [OfNat V 1] [Add V] [Sub V] [DecidableEq V]
    (root : Program) (s : PathState V) : Option (PathState V) :=
  let (op, path) := walk root s.pc
  let (flow, registers) := op.effect s.registers
  if flow = .halt then none else some (atPath (destination path flow) registers)

theorem step_at_op {V : Type} [OfNat V 0] [OfNat V 1] [Add V] [Sub V] [DecidableEq V]
    {root : Program} {p : List Bool} {op : Op}
    (located : locate root p = some (.op op)) (s : Store V) :
    step root (atPath p s) =
      if (op.effect s).1 = .halt then none
      else some (atPath (destination p (op.effect s).1) (op.effect s).2) := by
  have leaf := walk_located located []
  simp only [List.append_nil, walk] at leaf
  simp only [step, atPath, walk_trim, leaf]

end PalomarI3380.Compiler
