module
public import ZF192Support.Execution.Registers.Arithmetic.Footprints

@[expose] public section

/-! # Executable checks of the decoded AX macro plan -/

namespace ZF192Support.NativeAXSymbolic

inductive Op where
  | push | cons | copyA | copyD | copyH | incT | readH | readD
  deriving DecidableEq, Repr

instance transferDecidable (base : Nat) (src dst : Fin 9) :
    Decidable (NativeTransfer.Bound base src dst) :=
  decidable_of_iff
    (base+3 < 4341 ∧ src ≠ dst ∧
      RegisterMachine.Source.program base = some (.dec src.val (base+3) (base+1)) ∧
      RegisterMachine.Source.program (base+1) = some (.inc dst.val (base+2)) ∧
      RegisterMachine.Source.program (base+2) = some (.jump base))
    ⟨fun ⟨hr, hd, h0, h1, h2⟩ => ⟨hr, hd, h0, h1, h2⟩,
      fun h => ⟨h.range, h.distinct, h.row0, h.row1, h.row2⟩⟩

instance pairDecidable (base : Nat) : Decidable (NativePair.Bound base) :=
  decidable_of_iff (base+10 < 4341 ∧
    ∀ j : Fin 10, RegisterMachine.Source.program (base+j.val) = some (NativePair.expected base j.val))
    ⟨fun ⟨hr, rows⟩ => ⟨hr, rows⟩, fun h => ⟨h.range, h.rows⟩⟩

instance popDecidable (base : Nat) : Decidable (NativePop.Bound base) :=
  decidable_of_iff (base+11 < 4341 ∧
    (∀ j : Fin 11, RegisterMachine.Source.program (base+j.val) = some (NativePop.expected base j.val)) ∧
    NativeTransfer.Bound (base+4) 5 8 ∧ NativeTransfer.Bound (base+8) 5 0)
    ⟨fun ⟨hr, rows, transfer, restore⟩ => ⟨hr, rows, transfer, restore⟩,
      fun h => ⟨h.range, h.rows, h.transfer, h.restore⟩⟩

instance timesFourDecidable (base : Nat) : Decidable (NativeTimesFour.Bound base) :=
  decidable_of_iff (base+6 < 4341 ∧
    ∀ j : Fin 6, RegisterMachine.Source.program (base+j.val) = some (NativeTimesFour.expected base j.val))
    ⟨fun ⟨hr, rows⟩ => ⟨hr, rows⟩, fun h => ⟨h.range, h.rows⟩⟩

instance pushDecidable (base : Nat) : Decidable (NativePush.Bound base) :=
  decidable_of_iff (NativeTransfer.Bound base 2 8 ∧ NativeTransfer.Bound (base+3) 0 2 ∧
    NativePair.Bound (base+6) ∧ NativeTransfer.Bound (base+16) 5 0)
    ⟨fun ⟨t,w,p,y⟩ => ⟨t,w,p,y⟩, fun h => ⟨h.transferT, h.transferW, h.pair, h.transferY⟩⟩

instance drainDecidable (base : Nat) (src dst scratch : Fin 9) :
    Decidable (NativeCopyLoop.Bound base src dst scratch) :=
  decidable_of_iff
    (base+3 < 4341 ∧ src ≠ dst ∧ src ≠ scratch ∧ dst ≠ scratch ∧
      RegisterMachine.Source.program base = some (.dec src.val (base+4) (base+1)) ∧
      RegisterMachine.Source.program (base+1) = some (.inc dst.val (base+2)) ∧
      RegisterMachine.Source.program (base+2) = some (.inc scratch.val (base+3)) ∧
      RegisterMachine.Source.program (base+3) = some (.jump base))
    ⟨fun ⟨hr, hsd, hst, hdt, hd, hi, hs, hj⟩ => ⟨hr, hsd, hst, hdt, hd, hi, hs, hj⟩,
      fun h => ⟨h.range, h.srcDst, h.srcScratch, h.dstScratch, h.dec, h.incDst, h.incScratch, h.jump⟩⟩

instance copyDecidable (base : Nat) (src dst scratch : Fin 9) :
    Decidable (NativeCopyLoop.CopyBound base src dst scratch) :=
  decidable_of_iff (NativeCopyLoop.Bound base src dst scratch ∧ NativeTransfer.Bound (base+4) scratch src)
    ⟨fun ⟨drain, restore⟩ => ⟨drain, restore⟩, fun h => ⟨h.drain, h.restore⟩⟩

def Op.next (op : Op) (pc : Nat) : Nat := pc + match op with
  | .push => 19
  | .cons => 27
  | .copyA | .copyD | .copyH => 7
  | .incT => 1
  | .readD | .readH => 14

def Op.Valid (op : Op) (pc : Nat) : Prop := match op with
  | .push => NativePush.Bound pc
  | .cons => NativePop.Bound pc ∧ NativePair.Bound (pc+11) ∧ NativeTimesFour.Bound (pc+21)
  | .copyA => NativeCopyLoop.CopyBound pc 4 2 8
  | .copyD => NativeCopyLoop.CopyBound pc 3 2 8
  | .copyH => NativeCopyLoop.CopyBound pc 7 2 8
  | .incT => pc < 4341 ∧ RegisterMachine.Source.program pc = some (.inc 2 (pc+1))
  | .readD => pc = 224
  | .readH => pc = 131

instance (op : Op) (pc : Nat) : Decidable (op.Valid pc) := by
  cases op <;> unfold Op.Valid <;> infer_instance

def checkPlan (start : Nat) (ops : List Op) (stop : Nat) : Bool := match ops with
  | [] => start == stop
  | op :: rest => decide (op.Valid start) && checkPlan (op.next start) rest stop

/-- Select a candidate from a macro's entry row. The complete footprint is
checked by `Op.Valid` when the decoded plan is certified. -/
def candidate (pc : Nat) : Option Op :=
  match RegisterMachine.Source.program pc with
  | some (.dec 2 _ _) => some .push
  | some (.dec 0 _ _) => some .cons
  | some (.dec 4 _ _) => some .copyA
  | some (.dec 3 _ _) => some .copyD
  | some (.dec 7 _ _) => some .copyH
  | some (.inc 2 _) => some .incT
  | some (.dec 1 _ _) =>
    match RegisterMachine.Source.program (pc + 12) with
    | some (.inc 7 _) => some .readH
    | some (.inc 3 _) => some .readD
    | _ => none
  | _ => none

/-- Decode a bounded segment using the lengths of the recognized macros. -/
def readPlan : Nat → Nat → Option (List Op)
  | 0, _ => some []
  | n + 1, pc => do
    let op ← candidate pc
    let tail ← readPlan n (op.next pc)
    return op :: tail

end ZF192Support.NativeAXSymbolic
