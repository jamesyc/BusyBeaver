module
public import ZF192Support.Machine.RegisterProgram.Instructions

@[expose] public section

/-! # Row contracts for source register macros -/

open RegisterMachine.Source (Instruction program)

namespace ZF192Support.NativeTransfer

structure Bound (base:Nat) (src dst:Fin 9) : Prop where
 range : base+3<4341
 distinct : src≠dst
 row0 : program base=some (.dec src.val (base+3) (base+1))
 row1 : program (base+1)=some (.inc dst.val (base+2))
 row2 : program (base+2)=some (.jump base)

end ZF192Support.NativeTransfer

namespace ZF192Support.NativePair

def expected (offset:Nat) : Nat→Instruction
 | 0 => .dec 2 (offset+4) (offset+1)
 | 1 => .inc 5 (offset+2)
 | 2 => .inc 8 (offset+3)
 | 3 => .jump offset
 | 4 => .dec 8 (offset+10) (offset+5)
 | 5 => .inc 5 (offset+6)
 | 6 => .dec 8 (offset+9) (offset+7)
 | 7 => .inc 2 (offset+8)
 | 8 => .jump (offset+6)
 | 9 => .jump offset
 | _ => .halt
structure Bound (offset:Nat) : Prop where
 range : offset+10<4341
 rows : ∀j:Fin 10,program (offset+j.val)=some (expected offset j.val)

end ZF192Support.NativePair

namespace ZF192Support.NativePop

def expected (offset:Nat) : Nat→Instruction
 | 0 => .dec 0 (offset+8) (offset+1)
 | 1 => .inc 5 (offset+2)
 | 2 => .dec 8 (offset+4) (offset+3)
 | 3 => .jump (offset+7)
 | 4 => .dec 5 (offset+7) (offset+5)
 | 5 => .inc 8 (offset+6)
 | 6 => .jump (offset+4)
 | 7 => .jump offset
 | 8 => .dec 5 (offset+11) (offset+9)
 | 9 => .inc 0 (offset+10)
 | _ => .jump (offset+8)
structure Bound (offset:Nat) : Prop where
 range : offset+11<4341
 rows : ∀j:Fin 11,program (offset+j.val)=some (expected offset j.val)
 transfer : NativeTransfer.Bound (offset+4) 5 8
 restore : NativeTransfer.Bound (offset+8) 5 0

end ZF192Support.NativePop

namespace ZF192Support.NativeTimesFour

def expected (base:Nat) : Nat→Instruction
 | 0 => .dec 5 (base+6) (base+1)
 | 1 => .inc 2 (base+2)
 | 2 => .inc 2 (base+3)
 | 3 => .inc 2 (base+4)
 | 4 => .inc 2 (base+5)
 | _ => .jump base
structure Bound (base:Nat) : Prop where
 range : base+6<4341
 rows : ∀j:Fin 6,program (base+j.val)=some (expected base j.val)

end ZF192Support.NativeTimesFour

namespace ZF192Support.NativePush

structure Bound (base:Nat) : Prop where
 transferT : NativeTransfer.Bound base 2 8
 transferW : NativeTransfer.Bound (base+3) 0 2
 pair : NativePair.Bound (base+6)
 transferY : NativeTransfer.Bound (base+16) 5 0

end ZF192Support.NativePush

namespace ZF192Support.NativeCopyLoop

/-- The drain moves a source value into both the destination and scratch registers. -/
structure Bound (base : Nat) (src dst scratch : Fin 9) : Prop where
  range : base + 3 < 4341
  srcDst : src ≠ dst
  srcScratch : src ≠ scratch
  dstScratch : dst ≠ scratch
  dec : program base = some (.dec src.val (base+4) (base+1))
  incDst : program (base+1) = some (.inc dst.val (base+2))
  incScratch : program (base+2) = some (.inc scratch.val (base+3))
  jump : program (base+3) = some (.jump base)

structure CopyBound (base : Nat) (src dst scratch : Fin 9) : Prop where
  drain : Bound base src dst scratch
  restore : NativeTransfer.Bound (base+4) scratch src

end ZF192Support.NativeCopyLoop
