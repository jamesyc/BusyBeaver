import PA213.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S006
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s0292_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s0292_zero_checked : check 290 s0292_zero_contract = true := by decide +kernel
def s0292_zero : CertifiedContract :=
  ⟨292, 295, 0, .none, s0292_zero_contract, 290, s0292_zero_checked⟩

def s0292_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0292_positive_checked : check 296 s0292_positive_contract = true := by decide +kernel
def s0292_positive : CertifiedContract :=
  ⟨292, 293, 1, (.dec 2), s0292_positive_contract, 296, s0292_positive_checked⟩

def s0293_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s0293_plain_checked : check 309 s0293_plain_contract = true := by decide +kernel
def s0293_plain : CertifiedContract :=
  ⟨293, 294, 0, (.inc 8), s0293_plain_contract, 309, s0293_plain_checked⟩

def s0294_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, false, false] 0 .none⟩
theorem s0294_plain_checked : check 76 s0294_plain_contract = true := by decide +kernel
def s0294_plain : CertifiedContract :=
  ⟨294, 292, 0, .none, s0294_plain_contract, 76, s0294_plain_checked⟩

def s0295_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0295_zero_checked : check 311 s0295_zero_contract = true := by decide +kernel
def s0295_zero : CertifiedContract :=
  ⟨295, 298, 0, .none, s0295_zero_contract, 311, s0295_zero_checked⟩

def s0295_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0295_positive_checked : check 317 s0295_positive_contract = true := by decide +kernel
def s0295_positive : CertifiedContract :=
  ⟨295, 296, 1, (.dec 0), s0295_positive_contract, 317, s0295_positive_checked⟩

def s0296_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0296_plain_checked : check 309 s0296_plain_contract = true := by decide +kernel
def s0296_plain : CertifiedContract :=
  ⟨296, 297, 0, (.inc 2), s0296_plain_contract, 309, s0296_plain_checked⟩

def s0297_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s0297_plain_checked : check 79 s0297_plain_contract = true := by decide +kernel
def s0297_plain : CertifiedContract :=
  ⟨297, 295, 0, .none, s0297_plain_contract, 79, s0297_plain_checked⟩

def s0298_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0298_zero_checked : check 317 s0298_zero_contract = true := by decide +kernel
def s0298_zero : CertifiedContract :=
  ⟨298, 302, 0, .none, s0298_zero_contract, 317, s0298_zero_checked⟩

def s0298_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0298_positive_checked : check 323 s0298_positive_contract = true := by decide +kernel
def s0298_positive : CertifiedContract :=
  ⟨298, 299, 1, (.dec 2), s0298_positive_contract, 323, s0298_positive_checked⟩

def s0299_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0299_plain_checked : check 336 s0299_plain_contract = true := by decide +kernel
def s0299_plain : CertifiedContract :=
  ⟨299, 300, 0, (.inc 5), s0299_plain_contract, 336, s0299_plain_checked⟩

def s0300_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0300_plain_checked : check 363 s0300_plain_contract = true := by decide +kernel
def s0300_plain : CertifiedContract :=
  ⟨300, 301, 0, (.inc 8), s0300_plain_contract, 363, s0300_plain_checked⟩

def s0301_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0301_plain_checked : check 94 s0301_plain_contract = true := by decide +kernel
def s0301_plain : CertifiedContract :=
  ⟨301, 298, 0, .none, s0301_plain_contract, 94, s0301_plain_checked⟩

def s0302_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, true, false] 0 .none⟩
theorem s0302_zero_checked : check 338 s0302_zero_contract = true := by decide +kernel
def s0302_zero : CertifiedContract :=
  ⟨302, 308, 0, .none, s0302_zero_contract, 338, s0302_zero_checked⟩

def s0302_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0302_positive_checked : check 341 s0302_positive_contract = true := by decide +kernel
def s0302_positive : CertifiedContract :=
  ⟨302, 303, 1, (.dec 8), s0302_positive_contract, 341, s0302_positive_checked⟩

def s0303_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0303_plain_checked : check 336 s0303_plain_contract = true := by decide +kernel
def s0303_plain : CertifiedContract :=
  ⟨303, 304, 0, (.inc 5), s0303_plain_contract, 336, s0303_plain_checked⟩

def s0304_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s0304_zero_checked : check 356 s0304_zero_contract = true := by decide +kernel
def s0304_zero : CertifiedContract :=
  ⟨304, 307, 0, .none, s0304_zero_contract, 356, s0304_zero_checked⟩

def s0304_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0304_positive_checked : check 359 s0304_positive_contract = true := by decide +kernel
def s0304_positive : CertifiedContract :=
  ⟨304, 305, 1, (.dec 8), s0304_positive_contract, 359, s0304_positive_checked⟩

def s0305_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0305_plain_checked : check 354 s0305_plain_contract = true := by decide +kernel
def s0305_plain : CertifiedContract :=
  ⟨305, 306, 0, (.inc 2), s0305_plain_contract, 354, s0305_plain_checked⟩

def s0306_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0306_plain_checked : check 94 s0306_plain_contract = true := by decide +kernel
def s0306_plain : CertifiedContract :=
  ⟨306, 304, 0, .none, s0306_plain_contract, 94, s0306_plain_checked⟩

def s0307_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0307_plain_checked : check 97 s0307_plain_contract = true := by decide +kernel
def s0307_plain : CertifiedContract :=
  ⟨307, 298, 0, .none, s0307_plain_contract, 97, s0307_plain_checked⟩

def s0308_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, false, false] 0 .none⟩
theorem s0308_zero_checked : check 326 s0308_zero_contract = true := by decide +kernel
def s0308_zero : CertifiedContract :=
  ⟨308, 311, 0, .none, s0308_zero_contract, 326, s0308_zero_checked⟩

def s0308_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0308_positive_checked : check 323 s0308_positive_contract = true := by decide +kernel
def s0308_positive : CertifiedContract :=
  ⟨308, 309, 1, (.dec 5), s0308_positive_contract, 323, s0308_positive_checked⟩

def s0309_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0309_plain_checked : check 336 s0309_plain_contract = true := by decide +kernel
def s0309_plain : CertifiedContract :=
  ⟨309, 310, 0, (.inc 0), s0309_plain_contract, 336, s0309_plain_checked⟩

def s0310_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, true, false] 0 .none⟩
theorem s0310_plain_checked : check 85 s0310_plain_contract = true := by decide +kernel
def s0310_plain : CertifiedContract :=
  ⟨310, 308, 0, .none, s0310_plain_contract, 85, s0310_plain_checked⟩

def s0311_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s0311_zero_checked : check 290 s0311_zero_contract = true := by decide +kernel
def s0311_zero : CertifiedContract :=
  ⟨311, 315, 0, .none, s0311_zero_contract, 290, s0311_zero_checked⟩

def s0311_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, false, true, false] 1 (.dec 4)⟩
theorem s0311_positive_checked : check 296 s0311_positive_contract = true := by decide +kernel
def s0311_positive : CertifiedContract :=
  ⟨311, 312, 1, (.dec 4), s0311_positive_contract, 296, s0311_positive_checked⟩

def s0312_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0312_plain_checked : check 309 s0312_plain_contract = true := by decide +kernel
def s0312_plain : CertifiedContract :=
  ⟨312, 313, 0, (.inc 2), s0312_plain_contract, 309, s0312_plain_checked⟩

def s0313_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0313_plain_checked : check 336 s0313_plain_contract = true := by decide +kernel
def s0313_plain : CertifiedContract :=
  ⟨313, 314, 0, (.inc 8), s0313_plain_contract, 336, s0313_plain_checked⟩

def s0314_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, false, false] 0 .none⟩
theorem s0314_plain_checked : check 85 s0314_plain_contract = true := by decide +kernel
def s0314_plain : CertifiedContract :=
  ⟨314, 311, 0, .none, s0314_plain_contract, 85, s0314_plain_checked⟩

def s0315_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, false] 0 .none⟩
theorem s0315_zero_checked : check 299 s0315_zero_contract = true := by decide +kernel
def s0315_zero : CertifiedContract :=
  ⟨315, 318, 0, .none, s0315_zero_contract, 299, s0315_zero_checked⟩

def s0315_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s0315_positive_checked : check 296 s0315_positive_contract = true := by decide +kernel
def s0315_positive : CertifiedContract :=
  ⟨315, 316, 1, (.dec 8), s0315_positive_contract, 296, s0315_positive_checked⟩

def s0316_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, true, true, true] 0 (.inc 4)⟩
theorem s0316_plain_checked : check 300 s0316_plain_contract = true := by decide +kernel
def s0316_plain : CertifiedContract :=
  ⟨316, 317, 0, (.inc 4), s0316_plain_contract, 300, s0316_plain_checked⟩

def s0317_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s0317_plain_checked : check 76 s0317_plain_contract = true := by decide +kernel
def s0317_plain : CertifiedContract :=
  ⟨317, 315, 0, .none, s0317_plain_contract, 76, s0317_plain_checked⟩

def s0318_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, true, false] 0 .none⟩
theorem s0318_zero_checked : check 320 s0318_zero_contract = true := by decide +kernel
def s0318_zero : CertifiedContract :=
  ⟨318, 326, 0, .none, s0318_zero_contract, 320, s0318_zero_checked⟩

def s0318_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, false] 1 (.dec 0)⟩
theorem s0318_positive_checked : check 326 s0318_positive_contract = true := by decide +kernel
def s0318_positive : CertifiedContract :=
  ⟨318, 319, 1, (.dec 0), s0318_positive_contract, 326, s0318_positive_checked⟩

def s0319_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s0319_plain_checked : check 336 s0319_plain_contract = true := by decide +kernel
def s0319_plain : CertifiedContract :=
  ⟨319, 320, 0, (.inc 5), s0319_plain_contract, 336, s0319_plain_checked⟩

def s0320_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0320_zero_checked : check 362 s0320_zero_contract = true := by decide +kernel
def s0320_zero : CertifiedContract :=
  ⟨320, 322, 0, .none, s0320_zero_contract, 362, s0320_zero_checked⟩

def s0320_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s0320_positive_checked : check 368 s0320_positive_contract = true := by decide +kernel
def s0320_positive : CertifiedContract :=
  ⟨320, 321, 1, (.dec 8), s0320_positive_contract, 368, s0320_positive_checked⟩

def s0321_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s0321_plain_checked : check 97 s0321_plain_contract = true := by decide +kernel
def s0321_plain : CertifiedContract :=
  ⟨321, 325, 0, .none, s0321_plain_contract, 97, s0321_plain_checked⟩

def s0322_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s0322_zero_checked : check 374 s0322_zero_contract = true := by decide +kernel
def s0322_zero : CertifiedContract :=
  ⟨322, 325, 0, .none, s0322_zero_contract, 374, s0322_zero_checked⟩

def s0322_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0322_positive_checked : check 377 s0322_positive_contract = true := by decide +kernel
def s0322_positive : CertifiedContract :=
  ⟨322, 323, 1, (.dec 5), s0322_positive_contract, 377, s0322_positive_checked⟩

def s0323_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0323_plain_checked : check 381 s0323_plain_contract = true := by decide +kernel
def s0323_plain : CertifiedContract :=
  ⟨323, 324, 0, (.inc 8), s0323_plain_contract, 381, s0323_plain_checked⟩

def s0324_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0324_plain_checked : check 100 s0324_plain_contract = true := by decide +kernel
def s0324_plain : CertifiedContract :=
  ⟨324, 322, 0, .none, s0324_plain_contract, 100, s0324_plain_checked⟩

def s0325_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, false] 0 .none⟩
theorem s0325_plain_checked : check 91 s0325_plain_contract = true := by decide +kernel
def s0325_plain : CertifiedContract :=
  ⟨325, 318, 0, .none, s0325_plain_contract, 91, s0325_plain_checked⟩

def s0326_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s0326_zero_checked : check 320 s0326_zero_contract = true := by decide +kernel
def s0326_zero : CertifiedContract :=
  ⟨326, 329, 0, .none, s0326_zero_contract, 320, s0326_zero_checked⟩

def s0326_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, true, true, false] 1 (.dec 5)⟩
theorem s0326_positive_checked : check 323 s0326_positive_contract = true := by decide +kernel
def s0326_positive : CertifiedContract :=
  ⟨326, 327, 1, (.dec 5), s0326_positive_contract, 323, s0326_positive_checked⟩

def s0327_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, true, true, true] 0 (.inc 0)⟩
theorem s0327_plain_checked : check 336 s0327_plain_contract = true := by decide +kernel
def s0327_plain : CertifiedContract :=
  ⟨327, 328, 0, (.inc 0), s0327_plain_contract, 336, s0327_plain_checked⟩

def s0328_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, true, false] 0 .none⟩
theorem s0328_plain_checked : check 85 s0328_plain_contract = true := by decide +kernel
def s0328_plain : CertifiedContract :=
  ⟨328, 326, 0, .none, s0328_plain_contract, 85, s0328_plain_checked⟩

def s0329_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, false] 0 .none⟩
theorem s0329_zero_checked : check 317 s0329_zero_contract = true := by decide +kernel
def s0329_zero : CertifiedContract :=
  ⟨329, 333, 0, .none, s0329_zero_contract, 317, s0329_zero_checked⟩

def s0329_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0329_positive_checked : check 323 s0329_positive_contract = true := by decide +kernel
def s0329_positive : CertifiedContract :=
  ⟨329, 330, 1, (.dec 2), s0329_positive_contract, 323, s0329_positive_checked⟩

def s0330_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0330_plain_checked : check 336 s0330_plain_contract = true := by decide +kernel
def s0330_plain : CertifiedContract :=
  ⟨330, 331, 0, (.inc 5), s0330_plain_contract, 336, s0330_plain_checked⟩

def s0331_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0331_plain_checked : check 363 s0331_plain_contract = true := by decide +kernel
def s0331_plain : CertifiedContract :=
  ⟨331, 332, 0, (.inc 8), s0331_plain_contract, 363, s0331_plain_checked⟩

def s0332_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s0332_plain_checked : check 94 s0332_plain_contract = true := by decide +kernel
def s0332_plain : CertifiedContract :=
  ⟨332, 329, 0, .none, s0332_plain_contract, 94, s0332_plain_checked⟩

def s0333_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, true, false] 0 .none⟩
theorem s0333_zero_checked : check 338 s0333_zero_contract = true := by decide +kernel
def s0333_zero : CertifiedContract :=
  ⟨333, 339, 0, .none, s0333_zero_contract, 338, s0333_zero_checked⟩

def s0333_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0333_positive_checked : check 341 s0333_positive_contract = true := by decide +kernel
def s0333_positive : CertifiedContract :=
  ⟨333, 334, 1, (.dec 8), s0333_positive_contract, 341, s0333_positive_checked⟩

def s0334_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0334_plain_checked : check 336 s0334_plain_contract = true := by decide +kernel
def s0334_plain : CertifiedContract :=
  ⟨334, 335, 0, (.inc 5), s0334_plain_contract, 336, s0334_plain_checked⟩

def s0335_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, true] 0 .none⟩
theorem s0335_zero_checked : check 356 s0335_zero_contract = true := by decide +kernel
def s0335_zero : CertifiedContract :=
  ⟨335, 338, 0, .none, s0335_zero_contract, 356, s0335_zero_checked⟩

def s0335_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0335_positive_checked : check 359 s0335_positive_contract = true := by decide +kernel
def s0335_positive : CertifiedContract :=
  ⟨335, 336, 1, (.dec 8), s0335_positive_contract, 359, s0335_positive_checked⟩

def s0336_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0336_plain_checked : check 354 s0336_plain_contract = true := by decide +kernel
def s0336_plain : CertifiedContract :=
  ⟨336, 337, 0, (.inc 2), s0336_plain_contract, 354, s0336_plain_checked⟩

def s0337_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0337_plain_checked : check 94 s0337_plain_contract = true := by decide +kernel
def s0337_plain : CertifiedContract :=
  ⟨337, 335, 0, .none, s0337_plain_contract, 94, s0337_plain_checked⟩

def s0338_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s0338_plain_checked : check 97 s0338_plain_contract = true := by decide +kernel
def s0338_plain : CertifiedContract :=
  ⟨338, 329, 0, .none, s0338_plain_contract, 97, s0338_plain_checked⟩

def s0339_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, false, false] 0 .none⟩
theorem s0339_zero_checked : check 323 s0339_zero_contract = true := by decide +kernel
def s0339_zero : CertifiedContract :=
  ⟨339, 345, 0, .none, s0339_zero_contract, 323, s0339_zero_checked⟩

def s0339_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s0339_positive_checked : check 323 s0339_positive_contract = true := by decide +kernel
def s0339_positive : CertifiedContract :=
  ⟨339, 340, 1, (.dec 5), s0339_positive_contract, 323, s0339_positive_checked⟩

def nonterminal : Array CertifiedContract := #[
  s0292_zero,
  s0292_positive,
  s0293_plain,
  s0294_plain,
  s0295_zero,
  s0295_positive,
  s0296_plain,
  s0297_plain,
  s0298_zero,
  s0298_positive,
  s0299_plain,
  s0300_plain,
  s0301_plain,
  s0302_zero,
  s0302_positive,
  s0303_plain,
  s0304_zero,
  s0304_positive,
  s0305_plain,
  s0306_plain,
  s0307_plain,
  s0308_zero,
  s0308_positive,
  s0309_plain,
  s0310_plain,
  s0311_zero,
  s0311_positive,
  s0312_plain,
  s0313_plain,
  s0314_plain,
  s0315_zero,
  s0315_positive,
  s0316_plain,
  s0317_plain,
  s0318_zero,
  s0318_positive,
  s0319_plain,
  s0320_zero,
  s0320_positive,
  s0321_plain,
  s0322_zero,
  s0322_positive,
  s0323_plain,
  s0324_plain,
  s0325_plain,
  s0326_zero,
  s0326_positive,
  s0327_plain,
  s0328_plain,
  s0329_zero,
  s0329_positive,
  s0330_plain,
  s0331_plain,
  s0332_plain,
  s0333_zero,
  s0333_positive,
  s0334_plain,
  s0335_zero,
  s0335_positive,
  s0336_plain,
  s0337_plain,
  s0338_plain,
  s0339_zero,
  s0339_positive
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S006
