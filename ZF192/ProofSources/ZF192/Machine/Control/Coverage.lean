module
public import ZF192.Machine.Control.Coverage.Range00
public import ZF192.Machine.Control.Coverage.Range01
public import ZF192.Machine.Control.Coverage.Range02
public import ZF192.Machine.Control.Coverage.Range03
public import ZF192.Machine.Control.Coverage.Range04
public import ZF192.Machine.Control.Coverage.Range05
public import ZF192.Machine.Control.Coverage.Range06
public import ZF192.Machine.Control.Coverage.Range07
public import ZF192.Machine.Control.Coverage.Range08
public import ZF192.Machine.Control.Coverage.Range09
public import ZF192.Machine.Control.Coverage.Range10
public import ZF192.Machine.Control.Coverage.Range11
public import ZF192.Machine.Control.Coverage.Range12
public import ZF192.Machine.Control.Coverage.Range13
public import ZF192.Machine.Control.Coverage.Range14
public import ZF192.Machine.Control.Coverage.Range15
public import ZF192.Machine.Control.Coverage.Range16

@[expose] public section
namespace M192.Control
open M192.FiniteChecks

set_option maxRecDepth 100000 in
theorem allAligned : block check 0 4341 = true :=
  join_blocks check 256 4341 [
    aligned00, aligned01, aligned02, aligned03, aligned04, aligned05,
    aligned06, aligned07, aligned08, aligned09, aligned10, aligned11,
    aligned12, aligned13, aligned14, aligned15, aligned16]

theorem checked_at (pc : Nat) (bound : pc < 4341) : check pc = true := by
  simpa using of_block allAligned bound

end M192.Control
