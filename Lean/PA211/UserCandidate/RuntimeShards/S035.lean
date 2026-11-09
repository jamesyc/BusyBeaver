module

public import PA211.UserCandidate.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S035
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s1723_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, false, false, false] 0 .none⟩
theorem s1723_plain_checked : check 116 s1723_plain_contract = true := by decide +kernel
def s1723_plain : CertifiedContract :=
  ⟨1723, 1720, 0, .none, s1723_plain_contract, 116, s1723_plain_checked⟩

def s1724_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s1724_zero_checked : check 402 s1724_zero_contract = true := by decide +kernel
def s1724_zero : CertifiedContract :=
  ⟨1724, 1730, 0, .none, s1724_zero_contract, 402, s1724_zero_checked⟩

def s1724_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1724_positive_checked : check 405 s1724_positive_contract = true := by decide +kernel
def s1724_positive : CertifiedContract :=
  ⟨1724, 1725, 1, (.dec 8), s1724_positive_contract, 405, s1724_positive_checked⟩

def s1725_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1725_plain_checked : check 400 s1725_plain_contract = true := by decide +kernel
def s1725_plain : CertifiedContract :=
  ⟨1725, 1726, 0, (.inc 5), s1725_plain_contract, 400, s1725_plain_checked⟩

def s1726_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, false, true, true, true] 0 .none⟩
theorem s1726_zero_checked : check 420 s1726_zero_contract = true := by decide +kernel
def s1726_zero : CertifiedContract :=
  ⟨1726, 1729, 0, .none, s1726_zero_contract, 420, s1726_zero_checked⟩

def s1726_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1726_positive_checked : check 423 s1726_positive_contract = true := by decide +kernel
def s1726_positive : CertifiedContract :=
  ⟨1726, 1727, 1, (.dec 8), s1726_positive_contract, 423, s1726_positive_checked⟩

def s1727_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1727_plain_checked : check 418 s1727_plain_contract = true := by decide +kernel
def s1727_plain : CertifiedContract :=
  ⟨1727, 1728, 0, (.inc 2), s1727_plain_contract, 418, s1727_plain_checked⟩

def s1728_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s1728_plain_checked : check 116 s1728_plain_contract = true := by decide +kernel
def s1728_plain : CertifiedContract :=
  ⟨1728, 1726, 0, .none, s1728_plain_contract, 116, s1728_plain_checked⟩

def s1729_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, false, false, false] 0 .none⟩
theorem s1729_plain_checked : check 119 s1729_plain_contract = true := by decide +kernel
def s1729_plain : CertifiedContract :=
  ⟨1729, 1720, 0, .none, s1729_plain_contract, 119, s1729_plain_checked⟩

def s1730_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, true, false] 0 .none⟩
theorem s1730_zero_checked : check 387 s1730_zero_contract = true := by decide +kernel
def s1730_zero : CertifiedContract :=
  ⟨1730, 1736, 0, .none, s1730_zero_contract, 387, s1730_zero_checked⟩

def s1730_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s1730_positive_checked : check 387 s1730_positive_contract = true := by decide +kernel
def s1730_positive : CertifiedContract :=
  ⟨1730, 1731, 1, (.dec 5), s1730_positive_contract, 387, s1730_positive_checked⟩

def s1731_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s1731_plain_checked : check 400 s1731_plain_contract = true := by decide +kernel
def s1731_plain : CertifiedContract :=
  ⟨1731, 1732, 0, (.inc 2), s1731_plain_contract, 400, s1731_plain_checked⟩

def s1732_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s1732_plain_checked : check 403 s1732_plain_contract = true := by decide +kernel
def s1732_plain : CertifiedContract :=
  ⟨1732, 1733, 0, (.inc 2), s1732_plain_contract, 403, s1732_plain_checked⟩

def s1733_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s1733_plain_checked : check 409 s1733_plain_contract = true := by decide +kernel
def s1733_plain : CertifiedContract :=
  ⟨1733, 1734, 0, (.inc 2), s1733_plain_contract, 409, s1733_plain_checked⟩

def s1734_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, true, true, true] 0 (.inc 2)⟩
theorem s1734_plain_checked : check 415 s1734_plain_contract = true := by decide +kernel
def s1734_plain : CertifiedContract :=
  ⟨1734, 1735, 0, (.inc 2), s1734_plain_contract, 415, s1734_plain_checked⟩

def s1735_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s1735_plain_checked : check 104 s1735_plain_contract = true := by decide +kernel
def s1735_plain : CertifiedContract :=
  ⟨1735, 1730, 0, .none, s1735_plain_contract, 104, s1735_plain_checked⟩

def s1736_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, true, true] 0 (.inc 2)⟩
theorem s1736_plain_checked : check 355 s1736_plain_contract = true := by decide +kernel
def s1736_plain : CertifiedContract :=
  ⟨1736, 1737, 0, (.inc 2), s1736_plain_contract, 355, s1736_plain_checked⟩

def s1737_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, false, false] 0 (.inc 2)⟩
theorem s1737_plain_checked : check 361 s1737_plain_contract = true := by decide +kernel
def s1737_plain : CertifiedContract :=
  ⟨1737, 1738, 0, (.inc 2), s1737_plain_contract, 361, s1737_plain_checked⟩

def s1738_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, true, false] 0 .none⟩
theorem s1738_zero_checked : check 375 s1738_zero_contract = true := by decide +kernel
def s1738_zero : CertifiedContract :=
  ⟨1738, 1746, 0, .none, s1738_zero_contract, 375, s1738_zero_checked⟩

def s1738_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, false, true, false] 1 (.dec 0)⟩
theorem s1738_positive_checked : check 381 s1738_positive_contract = true := by decide +kernel
def s1738_positive : CertifiedContract :=
  ⟨1738, 1739, 1, (.dec 0), s1738_positive_contract, 381, s1738_positive_checked⟩

def s1739_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s1739_plain_checked : check 391 s1739_plain_contract = true := by decide +kernel
def s1739_plain : CertifiedContract :=
  ⟨1739, 1740, 0, (.inc 5), s1739_plain_contract, 391, s1739_plain_checked⟩

def s1740_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s1740_zero_checked : check 417 s1740_zero_contract = true := by decide +kernel
def s1740_zero : CertifiedContract :=
  ⟨1740, 1742, 0, .none, s1740_zero_contract, 417, s1740_zero_checked⟩

def s1740_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s1740_positive_checked : check 423 s1740_positive_contract = true := by decide +kernel
def s1740_positive : CertifiedContract :=
  ⟨1740, 1741, 1, (.dec 8), s1740_positive_contract, 423, s1740_positive_checked⟩

def s1741_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, false, true, true, true] 0 .none⟩
theorem s1741_plain_checked : check 116 s1741_plain_contract = true := by decide +kernel
def s1741_plain : CertifiedContract :=
  ⟨1741, 1745, 0, .none, s1741_plain_contract, 116, s1741_plain_checked⟩

def s1742_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, false, true, true, true] 0 .none⟩
theorem s1742_zero_checked : check 429 s1742_zero_contract = true := by decide +kernel
def s1742_zero : CertifiedContract :=
  ⟨1742, 1745, 0, .none, s1742_zero_contract, 429, s1742_zero_checked⟩

def s1742_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s1742_positive_checked : check 432 s1742_positive_contract = true := by decide +kernel
def s1742_positive : CertifiedContract :=
  ⟨1742, 1743, 1, (.dec 5), s1742_positive_contract, 432, s1742_positive_checked⟩

def s1743_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1743_plain_checked : check 436 s1743_plain_contract = true := by decide +kernel
def s1743_plain : CertifiedContract :=
  ⟨1743, 1744, 0, (.inc 8), s1743_plain_contract, 436, s1743_plain_checked⟩

def s1744_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s1744_plain_checked : check 119 s1744_plain_contract = true := by decide +kernel
def s1744_plain : CertifiedContract :=
  ⟨1744, 1742, 0, .none, s1744_plain_contract, 119, s1744_plain_checked⟩

def s1745_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, false, false] 0 .none⟩
theorem s1745_plain_checked : check 110 s1745_plain_contract = true := by decide +kernel
def s1745_plain : CertifiedContract :=
  ⟨1745, 1738, 0, .none, s1745_plain_contract, 110, s1745_plain_checked⟩

def s1746_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s1746_zero_checked : check 375 s1746_zero_contract = true := by decide +kernel
def s1746_zero : CertifiedContract :=
  ⟨1746, 1749, 0, .none, s1746_zero_contract, 375, s1746_zero_checked⟩

def s1746_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, true, true, false] 1 (.dec 5)⟩
theorem s1746_positive_checked : check 378 s1746_positive_contract = true := by decide +kernel
def s1746_positive : CertifiedContract :=
  ⟨1746, 1747, 1, (.dec 5), s1746_positive_contract, 378, s1746_positive_checked⟩

def s1747_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, true, true, true] 0 (.inc 0)⟩
theorem s1747_plain_checked : check 391 s1747_plain_contract = true := by decide +kernel
def s1747_plain : CertifiedContract :=
  ⟨1747, 1748, 0, (.inc 0), s1747_plain_contract, 391, s1747_plain_checked⟩

def s1748_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, false, true, false] 0 .none⟩
theorem s1748_plain_checked : check 104 s1748_plain_contract = true := by decide +kernel
def s1748_plain : CertifiedContract :=
  ⟨1748, 1746, 0, .none, s1748_plain_contract, 104, s1748_plain_checked⟩

def s1749_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1749_zero_checked : check 372 s1749_zero_contract = true := by decide +kernel
def s1749_zero : CertifiedContract :=
  ⟨1749, 1753, 0, .none, s1749_zero_contract, 372, s1749_zero_checked⟩

def s1749_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1749_positive_checked : check 378 s1749_positive_contract = true := by decide +kernel
def s1749_positive : CertifiedContract :=
  ⟨1749, 1750, 1, (.dec 2), s1749_positive_contract, 378, s1749_positive_checked⟩

def s1750_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1750_plain_checked : check 391 s1750_plain_contract = true := by decide +kernel
def s1750_plain : CertifiedContract :=
  ⟨1750, 1751, 0, (.inc 5), s1750_plain_contract, 391, s1750_plain_checked⟩

def s1751_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1751_plain_checked : check 418 s1751_plain_contract = true := by decide +kernel
def s1751_plain : CertifiedContract :=
  ⟨1751, 1752, 0, (.inc 8), s1751_plain_contract, 418, s1751_plain_checked⟩

def s1752_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s1752_plain_checked : check 113 s1752_plain_contract = true := by decide +kernel
def s1752_plain : CertifiedContract :=
  ⟨1752, 1749, 0, .none, s1752_plain_contract, 113, s1752_plain_checked⟩

def s1753_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s1753_zero_checked : check 393 s1753_zero_contract = true := by decide +kernel
def s1753_zero : CertifiedContract :=
  ⟨1753, 1759, 0, .none, s1753_zero_contract, 393, s1753_zero_checked⟩

def s1753_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1753_positive_checked : check 396 s1753_positive_contract = true := by decide +kernel
def s1753_positive : CertifiedContract :=
  ⟨1753, 1754, 1, (.dec 8), s1753_positive_contract, 396, s1753_positive_checked⟩

def s1754_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1754_plain_checked : check 391 s1754_plain_contract = true := by decide +kernel
def s1754_plain : CertifiedContract :=
  ⟨1754, 1755, 0, (.inc 5), s1754_plain_contract, 391, s1754_plain_checked⟩

def s1755_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s1755_zero_checked : check 411 s1755_zero_contract = true := by decide +kernel
def s1755_zero : CertifiedContract :=
  ⟨1755, 1758, 0, .none, s1755_zero_contract, 411, s1755_zero_checked⟩

def s1755_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1755_positive_checked : check 414 s1755_positive_contract = true := by decide +kernel
def s1755_positive : CertifiedContract :=
  ⟨1755, 1756, 1, (.dec 8), s1755_positive_contract, 414, s1755_positive_checked⟩

def s1756_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1756_plain_checked : check 409 s1756_plain_contract = true := by decide +kernel
def s1756_plain : CertifiedContract :=
  ⟨1756, 1757, 0, (.inc 2), s1756_plain_contract, 409, s1756_plain_checked⟩

def s1757_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1757_plain_checked : check 113 s1757_plain_contract = true := by decide +kernel
def s1757_plain : CertifiedContract :=
  ⟨1757, 1755, 0, .none, s1757_plain_contract, 113, s1757_plain_checked⟩

def s1758_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s1758_plain_checked : check 116 s1758_plain_contract = true := by decide +kernel
def s1758_plain : CertifiedContract :=
  ⟨1758, 1749, 0, .none, s1758_plain_contract, 116, s1758_plain_checked⟩

def s1759_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s1759_zero_checked : check 381 s1759_zero_contract = true := by decide +kernel
def s1759_zero : CertifiedContract :=
  ⟨1759, 1765, 0, .none, s1759_zero_contract, 381, s1759_zero_checked⟩

def s1759_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s1759_positive_checked : check 378 s1759_positive_contract = true := by decide +kernel
def s1759_positive : CertifiedContract :=
  ⟨1759, 1760, 1, (.dec 5), s1759_positive_contract, 378, s1759_positive_checked⟩

def s1760_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s1760_plain_checked : check 391 s1760_plain_contract = true := by decide +kernel
def s1760_plain : CertifiedContract :=
  ⟨1760, 1761, 0, (.inc 2), s1760_plain_contract, 391, s1760_plain_checked⟩

def s1761_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s1761_plain_checked : check 394 s1761_plain_contract = true := by decide +kernel
def s1761_plain : CertifiedContract :=
  ⟨1761, 1762, 0, (.inc 2), s1761_plain_contract, 394, s1761_plain_checked⟩

def s1762_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s1762_plain_checked : check 400 s1762_plain_contract = true := by decide +kernel
def s1762_plain : CertifiedContract :=
  ⟨1762, 1763, 0, (.inc 2), s1762_plain_contract, 400, s1762_plain_checked⟩

def s1763_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, true, true, true] 0 (.inc 2)⟩
theorem s1763_plain_checked : check 406 s1763_plain_contract = true := by decide +kernel
def s1763_plain : CertifiedContract :=
  ⟨1763, 1764, 0, (.inc 2), s1763_plain_contract, 406, s1763_plain_checked⟩

def s1764_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s1764_plain_checked : check 101 s1764_plain_contract = true := by decide +kernel
def s1764_plain : CertifiedContract :=
  ⟨1764, 1759, 0, .none, s1764_plain_contract, 101, s1764_plain_checked⟩

def s1765_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s1765_zero_checked : check 399 s1765_zero_contract = true := by decide +kernel
def s1765_zero : CertifiedContract :=
  ⟨1765, 1768, 0, .none, s1765_zero_contract, 399, s1765_zero_checked⟩

def s1765_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s1765_positive_checked : check 405 s1765_positive_contract = true := by decide +kernel
def s1765_positive : CertifiedContract :=
  ⟨1765, 1766, 1, (.dec 2), s1765_positive_contract, 405, s1765_positive_checked⟩

def s1766_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s1766_plain_checked : check 418 s1766_plain_contract = true := by decide +kernel
def s1766_plain : CertifiedContract :=
  ⟨1766, 1767, 0, (.inc 8), s1766_plain_contract, 418, s1766_plain_checked⟩

def s1767_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s1767_plain_checked : check 113 s1767_plain_contract = true := by decide +kernel
def s1767_plain : CertifiedContract :=
  ⟨1767, 1765, 0, .none, s1767_plain_contract, 113, s1767_plain_checked⟩

def s1768_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1768_zero_checked : check 420 s1768_zero_contract = true := by decide +kernel
def s1768_zero : CertifiedContract :=
  ⟨1768, 1771, 0, .none, s1768_zero_contract, 420, s1768_zero_checked⟩

def s1768_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s1768_positive_checked : check 426 s1768_positive_contract = true := by decide +kernel
def s1768_positive : CertifiedContract :=
  ⟨1768, 1769, 1, (.dec 0), s1768_positive_contract, 426, s1768_positive_checked⟩

def s1769_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s1769_plain_checked : check 418 s1769_plain_contract = true := by decide +kernel
def s1769_plain : CertifiedContract :=
  ⟨1769, 1770, 0, (.inc 2), s1769_plain_contract, 418, s1769_plain_checked⟩

def s1770_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s1770_plain_checked : check 116 s1770_plain_contract = true := by decide +kernel
def s1770_plain : CertifiedContract :=
  ⟨1770, 1768, 0, .none, s1770_plain_contract, 116, s1770_plain_checked⟩

def s1771_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1771_zero_checked : check 426 s1771_zero_contract = true := by decide +kernel
def s1771_zero : CertifiedContract :=
  ⟨1771, 1775, 0, .none, s1771_zero_contract, 426, s1771_zero_checked⟩

def s1771_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1771_positive_checked : check 432 s1771_positive_contract = true := by decide +kernel
def s1771_positive : CertifiedContract :=
  ⟨1771, 1772, 1, (.dec 2), s1771_positive_contract, 432, s1771_positive_checked⟩

def s1772_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1772_plain_checked : check 445 s1772_plain_contract = true := by decide +kernel
def s1772_plain : CertifiedContract :=
  ⟨1772, 1773, 0, (.inc 5), s1772_plain_contract, 445, s1772_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S035
