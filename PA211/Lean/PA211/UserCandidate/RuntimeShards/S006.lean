import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S006
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s0292_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s0292_zero_checked : check 291 s0292_zero_contract = true := by decide +kernel
def s0292_zero : CertifiedContract :=
  ⟨292, 295, 0, .none, s0292_zero_contract, 291, s0292_zero_checked⟩

def s0292_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0292_positive_checked : check 297 s0292_positive_contract = true := by decide +kernel
def s0292_positive : CertifiedContract :=
  ⟨292, 293, 1, (.dec 2), s0292_positive_contract, 297, s0292_positive_checked⟩

def s0293_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s0293_plain_checked : check 310 s0293_plain_contract = true := by decide +kernel
def s0293_plain : CertifiedContract :=
  ⟨293, 294, 0, (.inc 8), s0293_plain_contract, 310, s0293_plain_checked⟩

def s0294_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, false, false] 0 .none⟩
theorem s0294_plain_checked : check 77 s0294_plain_contract = true := by decide +kernel
def s0294_plain : CertifiedContract :=
  ⟨294, 292, 0, .none, s0294_plain_contract, 77, s0294_plain_checked⟩

def s0295_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0295_zero_checked : check 312 s0295_zero_contract = true := by decide +kernel
def s0295_zero : CertifiedContract :=
  ⟨295, 298, 0, .none, s0295_zero_contract, 312, s0295_zero_checked⟩

def s0295_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0295_positive_checked : check 318 s0295_positive_contract = true := by decide +kernel
def s0295_positive : CertifiedContract :=
  ⟨295, 296, 1, (.dec 0), s0295_positive_contract, 318, s0295_positive_checked⟩

def s0296_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0296_plain_checked : check 310 s0296_plain_contract = true := by decide +kernel
def s0296_plain : CertifiedContract :=
  ⟨296, 297, 0, (.inc 2), s0296_plain_contract, 310, s0296_plain_checked⟩

def s0297_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s0297_plain_checked : check 80 s0297_plain_contract = true := by decide +kernel
def s0297_plain : CertifiedContract :=
  ⟨297, 295, 0, .none, s0297_plain_contract, 80, s0297_plain_checked⟩

def s0298_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0298_zero_checked : check 318 s0298_zero_contract = true := by decide +kernel
def s0298_zero : CertifiedContract :=
  ⟨298, 302, 0, .none, s0298_zero_contract, 318, s0298_zero_checked⟩

def s0298_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0298_positive_checked : check 324 s0298_positive_contract = true := by decide +kernel
def s0298_positive : CertifiedContract :=
  ⟨298, 299, 1, (.dec 2), s0298_positive_contract, 324, s0298_positive_checked⟩

def s0299_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0299_plain_checked : check 337 s0299_plain_contract = true := by decide +kernel
def s0299_plain : CertifiedContract :=
  ⟨299, 300, 0, (.inc 5), s0299_plain_contract, 337, s0299_plain_checked⟩

def s0300_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0300_plain_checked : check 364 s0300_plain_contract = true := by decide +kernel
def s0300_plain : CertifiedContract :=
  ⟨300, 301, 0, (.inc 8), s0300_plain_contract, 364, s0300_plain_checked⟩

def s0301_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0301_plain_checked : check 95 s0301_plain_contract = true := by decide +kernel
def s0301_plain : CertifiedContract :=
  ⟨301, 298, 0, .none, s0301_plain_contract, 95, s0301_plain_checked⟩

def s0302_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, true, false] 0 .none⟩
theorem s0302_zero_checked : check 339 s0302_zero_contract = true := by decide +kernel
def s0302_zero : CertifiedContract :=
  ⟨302, 308, 0, .none, s0302_zero_contract, 339, s0302_zero_checked⟩

def s0302_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0302_positive_checked : check 342 s0302_positive_contract = true := by decide +kernel
def s0302_positive : CertifiedContract :=
  ⟨302, 303, 1, (.dec 8), s0302_positive_contract, 342, s0302_positive_checked⟩

def s0303_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0303_plain_checked : check 337 s0303_plain_contract = true := by decide +kernel
def s0303_plain : CertifiedContract :=
  ⟨303, 304, 0, (.inc 5), s0303_plain_contract, 337, s0303_plain_checked⟩

def s0304_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s0304_zero_checked : check 357 s0304_zero_contract = true := by decide +kernel
def s0304_zero : CertifiedContract :=
  ⟨304, 307, 0, .none, s0304_zero_contract, 357, s0304_zero_checked⟩

def s0304_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0304_positive_checked : check 360 s0304_positive_contract = true := by decide +kernel
def s0304_positive : CertifiedContract :=
  ⟨304, 305, 1, (.dec 8), s0304_positive_contract, 360, s0304_positive_checked⟩

def s0305_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0305_plain_checked : check 355 s0305_plain_contract = true := by decide +kernel
def s0305_plain : CertifiedContract :=
  ⟨305, 306, 0, (.inc 2), s0305_plain_contract, 355, s0305_plain_checked⟩

def s0306_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0306_plain_checked : check 95 s0306_plain_contract = true := by decide +kernel
def s0306_plain : CertifiedContract :=
  ⟨306, 304, 0, .none, s0306_plain_contract, 95, s0306_plain_checked⟩

def s0307_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s0307_plain_checked : check 98 s0307_plain_contract = true := by decide +kernel
def s0307_plain : CertifiedContract :=
  ⟨307, 298, 0, .none, s0307_plain_contract, 98, s0307_plain_checked⟩

def s0308_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, false, false] 0 .none⟩
theorem s0308_zero_checked : check 327 s0308_zero_contract = true := by decide +kernel
def s0308_zero : CertifiedContract :=
  ⟨308, 311, 0, .none, s0308_zero_contract, 327, s0308_zero_checked⟩

def s0308_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s0308_positive_checked : check 324 s0308_positive_contract = true := by decide +kernel
def s0308_positive : CertifiedContract :=
  ⟨308, 309, 1, (.dec 5), s0308_positive_contract, 324, s0308_positive_checked⟩

def s0309_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s0309_plain_checked : check 337 s0309_plain_contract = true := by decide +kernel
def s0309_plain : CertifiedContract :=
  ⟨309, 310, 0, (.inc 0), s0309_plain_contract, 337, s0309_plain_checked⟩

def s0310_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, false, true, true, true, false] 0 .none⟩
theorem s0310_plain_checked : check 86 s0310_plain_contract = true := by decide +kernel
def s0310_plain : CertifiedContract :=
  ⟨310, 308, 0, .none, s0310_plain_contract, 86, s0310_plain_checked⟩

def s0311_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s0311_zero_checked : check 291 s0311_zero_contract = true := by decide +kernel
def s0311_zero : CertifiedContract :=
  ⟨311, 315, 0, .none, s0311_zero_contract, 291, s0311_zero_checked⟩

def s0311_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, false, true, false] 1 (.dec 4)⟩
theorem s0311_positive_checked : check 297 s0311_positive_contract = true := by decide +kernel
def s0311_positive : CertifiedContract :=
  ⟨311, 312, 1, (.dec 4), s0311_positive_contract, 297, s0311_positive_checked⟩

def s0312_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s0312_plain_checked : check 310 s0312_plain_contract = true := by decide +kernel
def s0312_plain : CertifiedContract :=
  ⟨312, 313, 0, (.inc 2), s0312_plain_contract, 310, s0312_plain_checked⟩

def s0313_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0313_plain_checked : check 337 s0313_plain_contract = true := by decide +kernel
def s0313_plain : CertifiedContract :=
  ⟨313, 314, 0, (.inc 8), s0313_plain_contract, 337, s0313_plain_checked⟩

def s0314_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, false, false] 0 .none⟩
theorem s0314_plain_checked : check 86 s0314_plain_contract = true := by decide +kernel
def s0314_plain : CertifiedContract :=
  ⟨314, 311, 0, .none, s0314_plain_contract, 86, s0314_plain_checked⟩

def s0315_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, false] 0 .none⟩
theorem s0315_zero_checked : check 300 s0315_zero_contract = true := by decide +kernel
def s0315_zero : CertifiedContract :=
  ⟨315, 318, 0, .none, s0315_zero_contract, 300, s0315_zero_checked⟩

def s0315_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s0315_positive_checked : check 297 s0315_positive_contract = true := by decide +kernel
def s0315_positive : CertifiedContract :=
  ⟨315, 316, 1, (.dec 8), s0315_positive_contract, 297, s0315_positive_checked⟩

def s0316_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, true, true, true] 0 (.inc 4)⟩
theorem s0316_plain_checked : check 301 s0316_plain_contract = true := by decide +kernel
def s0316_plain : CertifiedContract :=
  ⟨316, 317, 0, (.inc 4), s0316_plain_contract, 301, s0316_plain_checked⟩

def s0317_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s0317_plain_checked : check 77 s0317_plain_contract = true := by decide +kernel
def s0317_plain : CertifiedContract :=
  ⟨317, 315, 0, .none, s0317_plain_contract, 77, s0317_plain_checked⟩

def s0318_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, true, false] 0 .none⟩
theorem s0318_zero_checked : check 321 s0318_zero_contract = true := by decide +kernel
def s0318_zero : CertifiedContract :=
  ⟨318, 326, 0, .none, s0318_zero_contract, 321, s0318_zero_checked⟩

def s0318_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, false] 1 (.dec 0)⟩
theorem s0318_positive_checked : check 327 s0318_positive_contract = true := by decide +kernel
def s0318_positive : CertifiedContract :=
  ⟨318, 319, 1, (.dec 0), s0318_positive_contract, 327, s0318_positive_checked⟩

def s0319_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s0319_plain_checked : check 337 s0319_plain_contract = true := by decide +kernel
def s0319_plain : CertifiedContract :=
  ⟨319, 320, 0, (.inc 5), s0319_plain_contract, 337, s0319_plain_checked⟩

def s0320_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0320_zero_checked : check 363 s0320_zero_contract = true := by decide +kernel
def s0320_zero : CertifiedContract :=
  ⟨320, 322, 0, .none, s0320_zero_contract, 363, s0320_zero_checked⟩

def s0320_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s0320_positive_checked : check 369 s0320_positive_contract = true := by decide +kernel
def s0320_positive : CertifiedContract :=
  ⟨320, 321, 1, (.dec 8), s0320_positive_contract, 369, s0320_positive_checked⟩

def s0321_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s0321_plain_checked : check 98 s0321_plain_contract = true := by decide +kernel
def s0321_plain : CertifiedContract :=
  ⟨321, 325, 0, .none, s0321_plain_contract, 98, s0321_plain_checked⟩

def s0322_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s0322_zero_checked : check 375 s0322_zero_contract = true := by decide +kernel
def s0322_zero : CertifiedContract :=
  ⟨322, 325, 0, .none, s0322_zero_contract, 375, s0322_zero_checked⟩

def s0322_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0322_positive_checked : check 378 s0322_positive_contract = true := by decide +kernel
def s0322_positive : CertifiedContract :=
  ⟨322, 323, 1, (.dec 5), s0322_positive_contract, 378, s0322_positive_checked⟩

def s0323_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0323_plain_checked : check 382 s0323_plain_contract = true := by decide +kernel
def s0323_plain : CertifiedContract :=
  ⟨323, 324, 0, (.inc 8), s0323_plain_contract, 382, s0323_plain_checked⟩

def s0324_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0324_plain_checked : check 101 s0324_plain_contract = true := by decide +kernel
def s0324_plain : CertifiedContract :=
  ⟨324, 322, 0, .none, s0324_plain_contract, 101, s0324_plain_checked⟩

def s0325_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, false, false] 0 .none⟩
theorem s0325_plain_checked : check 92 s0325_plain_contract = true := by decide +kernel
def s0325_plain : CertifiedContract :=
  ⟨325, 318, 0, .none, s0325_plain_contract, 92, s0325_plain_checked⟩

def s0326_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s0326_zero_checked : check 321 s0326_zero_contract = true := by decide +kernel
def s0326_zero : CertifiedContract :=
  ⟨326, 329, 0, .none, s0326_zero_contract, 321, s0326_zero_checked⟩

def s0326_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, true, true, false] 1 (.dec 5)⟩
theorem s0326_positive_checked : check 324 s0326_positive_contract = true := by decide +kernel
def s0326_positive : CertifiedContract :=
  ⟨326, 327, 1, (.dec 5), s0326_positive_contract, 324, s0326_positive_checked⟩

def s0327_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, true, true, true] 0 (.inc 0)⟩
theorem s0327_plain_checked : check 337 s0327_plain_contract = true := by decide +kernel
def s0327_plain : CertifiedContract :=
  ⟨327, 328, 0, (.inc 0), s0327_plain_contract, 337, s0327_plain_checked⟩

def s0328_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, false, true, false] 0 .none⟩
theorem s0328_plain_checked : check 86 s0328_plain_contract = true := by decide +kernel
def s0328_plain : CertifiedContract :=
  ⟨328, 326, 0, .none, s0328_plain_contract, 86, s0328_plain_checked⟩

def s0329_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, false] 0 .none⟩
theorem s0329_zero_checked : check 318 s0329_zero_contract = true := by decide +kernel
def s0329_zero : CertifiedContract :=
  ⟨329, 333, 0, .none, s0329_zero_contract, 318, s0329_zero_checked⟩

def s0329_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0329_positive_checked : check 324 s0329_positive_contract = true := by decide +kernel
def s0329_positive : CertifiedContract :=
  ⟨329, 330, 1, (.dec 2), s0329_positive_contract, 324, s0329_positive_checked⟩

def s0330_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0330_plain_checked : check 337 s0330_plain_contract = true := by decide +kernel
def s0330_plain : CertifiedContract :=
  ⟨330, 331, 0, (.inc 5), s0330_plain_contract, 337, s0330_plain_checked⟩

def s0331_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0331_plain_checked : check 364 s0331_plain_contract = true := by decide +kernel
def s0331_plain : CertifiedContract :=
  ⟨331, 332, 0, (.inc 8), s0331_plain_contract, 364, s0331_plain_checked⟩

def s0332_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s0332_plain_checked : check 95 s0332_plain_contract = true := by decide +kernel
def s0332_plain : CertifiedContract :=
  ⟨332, 329, 0, .none, s0332_plain_contract, 95, s0332_plain_checked⟩

def s0333_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, true, false] 0 .none⟩
theorem s0333_zero_checked : check 339 s0333_zero_contract = true := by decide +kernel
def s0333_zero : CertifiedContract :=
  ⟨333, 339, 0, .none, s0333_zero_contract, 339, s0333_zero_checked⟩

def s0333_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0333_positive_checked : check 342 s0333_positive_contract = true := by decide +kernel
def s0333_positive : CertifiedContract :=
  ⟨333, 334, 1, (.dec 8), s0333_positive_contract, 342, s0333_positive_checked⟩

def s0334_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0334_plain_checked : check 337 s0334_plain_contract = true := by decide +kernel
def s0334_plain : CertifiedContract :=
  ⟨334, 335, 0, (.inc 5), s0334_plain_contract, 337, s0334_plain_checked⟩

def s0335_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, true] 0 .none⟩
theorem s0335_zero_checked : check 357 s0335_zero_contract = true := by decide +kernel
def s0335_zero : CertifiedContract :=
  ⟨335, 338, 0, .none, s0335_zero_contract, 357, s0335_zero_checked⟩

def s0335_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0335_positive_checked : check 360 s0335_positive_contract = true := by decide +kernel
def s0335_positive : CertifiedContract :=
  ⟨335, 336, 1, (.dec 8), s0335_positive_contract, 360, s0335_positive_checked⟩

def s0336_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0336_plain_checked : check 355 s0336_plain_contract = true := by decide +kernel
def s0336_plain : CertifiedContract :=
  ⟨336, 337, 0, (.inc 2), s0336_plain_contract, 355, s0336_plain_checked⟩

def s0337_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0337_plain_checked : check 95 s0337_plain_contract = true := by decide +kernel
def s0337_plain : CertifiedContract :=
  ⟨337, 335, 0, .none, s0337_plain_contract, 95, s0337_plain_checked⟩

def s0338_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s0338_plain_checked : check 98 s0338_plain_contract = true := by decide +kernel
def s0338_plain : CertifiedContract :=
  ⟨338, 329, 0, .none, s0338_plain_contract, 98, s0338_plain_checked⟩

def s0339_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, true, false, false, false, false] 0 .none⟩
theorem s0339_zero_checked : check 324 s0339_zero_contract = true := by decide +kernel
def s0339_zero : CertifiedContract :=
  ⟨339, 345, 0, .none, s0339_zero_contract, 324, s0339_zero_checked⟩

def s0339_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, false, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s0339_positive_checked : check 324 s0339_positive_contract = true := by decide +kernel
def s0339_positive : CertifiedContract :=
  ⟨339, 340, 1, (.dec 5), s0339_positive_contract, 324, s0339_positive_checked⟩

end PA211.UserCandidate.RuntimeShards.S006
