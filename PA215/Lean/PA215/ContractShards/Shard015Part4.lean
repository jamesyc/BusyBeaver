import PA215.CertifiedContracts
import PA215.Census.C015
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard015Part4
open PA215.Contracts PA215.Census

def original1990 : RawOriginal := C015.records[70]'(by decide)
theorem original_id1990 : original1990.index = 1990 := by decide

def c1990 : Contract := original1990.toContract.get (by decide)
theorem binding1990 : original1990.toContract = some c1990 := rfl

theorem checked1990 : check 4000 c1990 = true := by decide

def original1991 : RawOriginal := C015.records[71]'(by decide)
theorem original_id1991 : original1991.index = 1991 := by decide

def c1991 : Contract := original1991.toContract.get (by decide)
theorem binding1991 : original1991.toContract = some c1991 := rfl

theorem checked1991 : check 4000 c1991 = true := by decide

def original1992 : RawOriginal := C015.records[72]'(by decide)
theorem original_id1992 : original1992.index = 1992 := by decide

def c1992 : Contract := original1992.toContract.get (by decide)
theorem binding1992 : original1992.toContract = some c1992 := rfl

theorem checked1992 : check 4000 c1992 = true := by decide

def original1993 : RawOriginal := C015.records[73]'(by decide)
theorem original_id1993 : original1993.index = 1993 := by decide

def c1993 : Contract := original1993.toContract.get (by decide)
theorem binding1993 : original1993.toContract = some c1993 := rfl

theorem checked1993 : check 4000 c1993 = true := by decide

def original1994 : RawOriginal := C015.records[74]'(by decide)
theorem original_id1994 : original1994.index = 1994 := by decide

def c1994 : Contract := original1994.toContract.get (by decide)
theorem binding1994 : original1994.toContract = some c1994 := rfl

theorem checked1994 : check 4000 c1994 = true := by decide

def original1995 : RawOriginal := C015.records[75]'(by decide)
theorem original_id1995 : original1995.index = 1995 := by decide

def c1995 : Contract := original1995.toContract.get (by decide)
theorem binding1995 : original1995.toContract = some c1995 := rfl

theorem checked1995 : check 4000 c1995 = true := by decide

def original1996 : RawOriginal := C015.records[76]'(by decide)
theorem original_id1996 : original1996.index = 1996 := by decide

def c1996 : Contract := original1996.toContract.get (by decide)
theorem binding1996 : original1996.toContract = some c1996 := rfl

theorem checked1996 : check 4000 c1996 = true := by decide

def original1997 : RawOriginal := C015.records[77]'(by decide)
theorem original_id1997 : original1997.index = 1997 := by decide

def c1997 : Contract := original1997.toContract.get (by decide)
theorem binding1997 : original1997.toContract = some c1997 := rfl

theorem checked1997 : check 4000 c1997 = true := by decide

def original1998 : RawOriginal := C015.records[78]'(by decide)
theorem original_id1998 : original1998.index = 1998 := by decide

def c1998 : Contract := original1998.toContract.get (by decide)
theorem binding1998 : original1998.toContract = some c1998 := rfl

theorem checked1998 : check 4000 c1998 = true := by decide

def original1999 : RawOriginal := C015.records[79]'(by decide)
theorem original_id1999 : original1999.index = 1999 := by decide

def c1999 : Contract := original1999.toContract.get (by decide)
theorem binding1999 : original1999.toContract = some c1999 := rfl

theorem checked1999 : check 4000 c1999 = true := by decide

def original2000 : RawOriginal := C015.records[80]'(by decide)
theorem original_id2000 : original2000.index = 2000 := by decide

def c2000 : Contract := original2000.toContract.get (by decide)
theorem binding2000 : original2000.toContract = some c2000 := rfl

theorem checked2000 : check 4000 c2000 = true := by decide

def original2001 : RawOriginal := C015.records[81]'(by decide)
theorem original_id2001 : original2001.index = 2001 := by decide

def c2001 : Contract := original2001.toContract.get (by decide)
theorem binding2001 : original2001.toContract = some c2001 := rfl

theorem checked2001 : check 4000 c2001 = true := by decide

def original2002 : RawOriginal := C015.records[82]'(by decide)
theorem original_id2002 : original2002.index = 2002 := by decide

def c2002 : Contract := original2002.toContract.get (by decide)
theorem binding2002 : original2002.toContract = some c2002 := rfl

theorem checked2002 : check 4000 c2002 = true := by decide

def original2003 : RawOriginal := C015.records[83]'(by decide)
theorem original_id2003 : original2003.index = 2003 := by decide

def c2003 : Contract := original2003.toContract.get (by decide)
theorem binding2003 : original2003.toContract = some c2003 := rfl

theorem checked2003 : check 4000 c2003 = true := by decide

def original2004 : RawOriginal := C015.records[84]'(by decide)
theorem original_id2004 : original2004.index = 2004 := by decide

def c2004 : Contract := original2004.toContract.get (by decide)
theorem binding2004 : original2004.toContract = some c2004 := rfl

theorem checked2004 : check 4000 c2004 = true := by decide

def original2005 : RawOriginal := C015.records[85]'(by decide)
theorem original_id2005 : original2005.index = 2005 := by decide

def c2005 : Contract := original2005.toContract.get (by decide)
theorem binding2005 : original2005.toContract = some c2005 := rfl

theorem checked2005 : check 4000 c2005 = true := by decide

def records : List Certified := [
  ⟨1990, c1990, 4000, checked1990⟩,
  ⟨1991, c1991, 4000, checked1991⟩,
  ⟨1992, c1992, 4000, checked1992⟩,
  ⟨1993, c1993, 4000, checked1993⟩,
  ⟨1994, c1994, 4000, checked1994⟩,
  ⟨1995, c1995, 4000, checked1995⟩,
  ⟨1996, c1996, 4000, checked1996⟩,
  ⟨1997, c1997, 4000, checked1997⟩,
  ⟨1998, c1998, 4000, checked1998⟩,
  ⟨1999, c1999, 4000, checked1999⟩,
  ⟨2000, c2000, 4000, checked2000⟩,
  ⟨2001, c2001, 4000, checked2001⟩,
  ⟨2002, c2002, 4000, checked2002⟩,
  ⟨2003, c2003, 4000, checked2003⟩,
  ⟨2004, c2004, 4000, checked2004⟩,
  ⟨2005, c2005, 4000, checked2005⟩]

end PA215.ContractShards.Shard015Part4
