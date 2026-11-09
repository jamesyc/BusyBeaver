module

public import PA211.UserCandidate.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S036
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s1773_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1773_plain_checked : check 472 s1773_plain_contract = true := by decide +kernel
def s1773_plain : CertifiedContract :=
  ⟨1773, 1774, 0, (.inc 8), s1773_plain_contract, 472, s1773_plain_checked⟩

def s1774_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1774_plain_checked : check 131 s1774_plain_contract = true := by decide +kernel
def s1774_plain : CertifiedContract :=
  ⟨1774, 1771, 0, .none, s1774_plain_contract, 131, s1774_plain_checked⟩

def s1775_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s1775_zero_checked : check 447 s1775_zero_contract = true := by decide +kernel
def s1775_zero : CertifiedContract :=
  ⟨1775, 1781, 0, .none, s1775_zero_contract, 447, s1775_zero_checked⟩

def s1775_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1775_positive_checked : check 450 s1775_positive_contract = true := by decide +kernel
def s1775_positive : CertifiedContract :=
  ⟨1775, 1776, 1, (.dec 8), s1775_positive_contract, 450, s1775_positive_checked⟩

def s1776_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1776_plain_checked : check 445 s1776_plain_contract = true := by decide +kernel
def s1776_plain : CertifiedContract :=
  ⟨1776, 1777, 0, (.inc 5), s1776_plain_contract, 445, s1776_plain_checked⟩

def s1777_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s1777_zero_checked : check 465 s1777_zero_contract = true := by decide +kernel
def s1777_zero : CertifiedContract :=
  ⟨1777, 1780, 0, .none, s1777_zero_contract, 465, s1777_zero_checked⟩

def s1777_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1777_positive_checked : check 468 s1777_positive_contract = true := by decide +kernel
def s1777_positive : CertifiedContract :=
  ⟨1777, 1778, 1, (.dec 8), s1777_positive_contract, 468, s1777_positive_checked⟩

def s1778_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1778_plain_checked : check 463 s1778_plain_contract = true := by decide +kernel
def s1778_plain : CertifiedContract :=
  ⟨1778, 1779, 0, (.inc 2), s1778_plain_contract, 463, s1778_plain_checked⟩

def s1779_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1779_plain_checked : check 131 s1779_plain_contract = true := by decide +kernel
def s1779_plain : CertifiedContract :=
  ⟨1779, 1777, 0, .none, s1779_plain_contract, 131, s1779_plain_checked⟩

def s1780_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1780_plain_checked : check 134 s1780_plain_contract = true := by decide +kernel
def s1780_plain : CertifiedContract :=
  ⟨1780, 1771, 0, .none, s1780_plain_contract, 134, s1780_plain_checked⟩

def s1781_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s1781_zero_checked : check 435 s1781_zero_contract = true := by decide +kernel
def s1781_zero : CertifiedContract :=
  ⟨1781, 1784, 0, .none, s1781_zero_contract, 435, s1781_zero_checked⟩

def s1781_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s1781_positive_checked : check 432 s1781_positive_contract = true := by decide +kernel
def s1781_positive : CertifiedContract :=
  ⟨1781, 1782, 1, (.dec 5), s1781_positive_contract, 432, s1781_positive_checked⟩

def s1782_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s1782_plain_checked : check 445 s1782_plain_contract = true := by decide +kernel
def s1782_plain : CertifiedContract :=
  ⟨1782, 1783, 0, (.inc 0), s1782_plain_contract, 445, s1782_plain_checked⟩

def s1783_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s1783_plain_checked : check 122 s1783_plain_contract = true := by decide +kernel
def s1783_plain : CertifiedContract :=
  ⟨1783, 1781, 0, .none, s1783_plain_contract, 122, s1783_plain_checked⟩

def s1784_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s1784_zero_checked : check 399 s1784_zero_contract = true := by decide +kernel
def s1784_zero : CertifiedContract :=
  ⟨1784, 1788, 0, .none, s1784_zero_contract, 399, s1784_zero_checked⟩

def s1784_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, true, false, true, false] 1 (.dec 3)⟩
theorem s1784_positive_checked : check 405 s1784_positive_contract = true := by decide +kernel
def s1784_positive : CertifiedContract :=
  ⟨1784, 1785, 1, (.dec 3), s1784_positive_contract, 405, s1784_positive_checked⟩

def s1785_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s1785_plain_checked : check 418 s1785_plain_contract = true := by decide +kernel
def s1785_plain : CertifiedContract :=
  ⟨1785, 1786, 0, (.inc 2), s1785_plain_contract, 418, s1785_plain_checked⟩

def s1786_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1786_plain_checked : check 445 s1786_plain_contract = true := by decide +kernel
def s1786_plain : CertifiedContract :=
  ⟨1786, 1787, 0, (.inc 8), s1786_plain_contract, 445, s1786_plain_checked⟩

def s1787_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s1787_plain_checked : check 122 s1787_plain_contract = true := by decide +kernel
def s1787_plain : CertifiedContract :=
  ⟨1787, 1784, 0, .none, s1787_plain_contract, 122, s1787_plain_checked⟩

def s1788_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s1788_zero_checked : check 405 s1788_zero_contract = true := by decide +kernel
def s1788_zero : CertifiedContract :=
  ⟨1788, 1791, 0, .none, s1788_zero_contract, 405, s1788_zero_checked⟩

def s1788_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s1788_positive_checked : check 405 s1788_positive_contract = true := by decide +kernel
def s1788_positive : CertifiedContract :=
  ⟨1788, 1789, 1, (.dec 8), s1788_positive_contract, 405, s1788_positive_checked⟩

def s1789_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, true, true, true, true] 0 (.inc 3)⟩
theorem s1789_plain_checked : check 421 s1789_plain_contract = true := by decide +kernel
def s1789_plain : CertifiedContract :=
  ⟨1789, 1790, 0, (.inc 3), s1789_plain_contract, 421, s1789_plain_checked⟩

def s1790_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s1790_plain_checked : check 113 s1790_plain_contract = true := by decide +kernel
def s1790_plain : CertifiedContract :=
  ⟨1790, 1788, 0, .none, s1790_plain_contract, 113, s1790_plain_checked⟩

def s1791_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s1791_zero_checked : check 399 s1791_zero_contract = true := by decide +kernel
def s1791_zero : CertifiedContract :=
  ⟨1791, 1794, 0, .none, s1791_zero_contract, 399, s1791_zero_checked⟩

def s1791_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1791_positive_checked : check 405 s1791_positive_contract = true := by decide +kernel
def s1791_positive : CertifiedContract :=
  ⟨1791, 1792, 1, (.dec 2), s1791_positive_contract, 405, s1791_positive_checked⟩

def s1792_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s1792_plain_checked : check 418 s1792_plain_contract = true := by decide +kernel
def s1792_plain : CertifiedContract :=
  ⟨1792, 1793, 0, (.inc 8), s1792_plain_contract, 418, s1792_plain_checked⟩

def s1793_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s1793_plain_checked : check 113 s1793_plain_contract = true := by decide +kernel
def s1793_plain : CertifiedContract :=
  ⟨1793, 1791, 0, .none, s1793_plain_contract, 113, s1793_plain_checked⟩

def s1794_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1794_zero_checked : check 420 s1794_zero_contract = true := by decide +kernel
def s1794_zero : CertifiedContract :=
  ⟨1794, 1797, 0, .none, s1794_zero_contract, 420, s1794_zero_checked⟩

def s1794_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s1794_positive_checked : check 426 s1794_positive_contract = true := by decide +kernel
def s1794_positive : CertifiedContract :=
  ⟨1794, 1795, 1, (.dec 0), s1794_positive_contract, 426, s1794_positive_checked⟩

def s1795_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s1795_plain_checked : check 418 s1795_plain_contract = true := by decide +kernel
def s1795_plain : CertifiedContract :=
  ⟨1795, 1796, 0, (.inc 2), s1795_plain_contract, 418, s1795_plain_checked⟩

def s1796_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s1796_plain_checked : check 116 s1796_plain_contract = true := by decide +kernel
def s1796_plain : CertifiedContract :=
  ⟨1796, 1794, 0, .none, s1796_plain_contract, 116, s1796_plain_checked⟩

def s1797_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s1797_zero_checked : check 426 s1797_zero_contract = true := by decide +kernel
def s1797_zero : CertifiedContract :=
  ⟨1797, 1801, 0, .none, s1797_zero_contract, 426, s1797_zero_checked⟩

def s1797_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1797_positive_checked : check 432 s1797_positive_contract = true := by decide +kernel
def s1797_positive : CertifiedContract :=
  ⟨1797, 1798, 1, (.dec 2), s1797_positive_contract, 432, s1797_positive_checked⟩

def s1798_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1798_plain_checked : check 445 s1798_plain_contract = true := by decide +kernel
def s1798_plain : CertifiedContract :=
  ⟨1798, 1799, 0, (.inc 5), s1798_plain_contract, 445, s1798_plain_checked⟩

def s1799_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1799_plain_checked : check 472 s1799_plain_contract = true := by decide +kernel
def s1799_plain : CertifiedContract :=
  ⟨1799, 1800, 0, (.inc 8), s1799_plain_contract, 472, s1799_plain_checked⟩

def s1800_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1800_plain_checked : check 131 s1800_plain_contract = true := by decide +kernel
def s1800_plain : CertifiedContract :=
  ⟨1800, 1797, 0, .none, s1800_plain_contract, 131, s1800_plain_checked⟩

def s1801_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s1801_zero_checked : check 447 s1801_zero_contract = true := by decide +kernel
def s1801_zero : CertifiedContract :=
  ⟨1801, 1807, 0, .none, s1801_zero_contract, 447, s1801_zero_checked⟩

def s1801_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1801_positive_checked : check 450 s1801_positive_contract = true := by decide +kernel
def s1801_positive : CertifiedContract :=
  ⟨1801, 1802, 1, (.dec 8), s1801_positive_contract, 450, s1801_positive_checked⟩

def s1802_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1802_plain_checked : check 445 s1802_plain_contract = true := by decide +kernel
def s1802_plain : CertifiedContract :=
  ⟨1802, 1803, 0, (.inc 5), s1802_plain_contract, 445, s1802_plain_checked⟩

def s1803_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s1803_zero_checked : check 465 s1803_zero_contract = true := by decide +kernel
def s1803_zero : CertifiedContract :=
  ⟨1803, 1806, 0, .none, s1803_zero_contract, 465, s1803_zero_checked⟩

def s1803_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1803_positive_checked : check 468 s1803_positive_contract = true := by decide +kernel
def s1803_positive : CertifiedContract :=
  ⟨1803, 1804, 1, (.dec 8), s1803_positive_contract, 468, s1803_positive_checked⟩

def s1804_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1804_plain_checked : check 463 s1804_plain_contract = true := by decide +kernel
def s1804_plain : CertifiedContract :=
  ⟨1804, 1805, 0, (.inc 2), s1804_plain_contract, 463, s1804_plain_checked⟩

def s1805_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1805_plain_checked : check 131 s1805_plain_contract = true := by decide +kernel
def s1805_plain : CertifiedContract :=
  ⟨1805, 1803, 0, .none, s1805_plain_contract, 131, s1805_plain_checked⟩

def s1806_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1806_plain_checked : check 134 s1806_plain_contract = true := by decide +kernel
def s1806_plain : CertifiedContract :=
  ⟨1806, 1797, 0, .none, s1806_plain_contract, 134, s1806_plain_checked⟩

def s1807_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, true, false, false] 0 .none⟩
theorem s1807_zero_checked : check 435 s1807_zero_contract = true := by decide +kernel
def s1807_zero : CertifiedContract :=
  ⟨1807, 1810, 0, .none, s1807_zero_contract, 435, s1807_zero_checked⟩

def s1807_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s1807_positive_checked : check 432 s1807_positive_contract = true := by decide +kernel
def s1807_positive : CertifiedContract :=
  ⟨1807, 1808, 1, (.dec 5), s1807_positive_contract, 432, s1807_positive_checked⟩

def s1808_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s1808_plain_checked : check 445 s1808_plain_contract = true := by decide +kernel
def s1808_plain : CertifiedContract :=
  ⟨1808, 1809, 0, (.inc 0), s1808_plain_contract, 445, s1808_plain_checked⟩

def s1809_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s1809_plain_checked : check 122 s1809_plain_contract = true := by decide +kernel
def s1809_plain : CertifiedContract :=
  ⟨1809, 1807, 0, .none, s1809_plain_contract, 122, s1809_plain_checked⟩

def s1810_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s1810_zero_checked : check 399 s1810_zero_contract = true := by decide +kernel
def s1810_zero : CertifiedContract :=
  ⟨1810, 1814, 0, .none, s1810_zero_contract, 399, s1810_zero_checked⟩

def s1810_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, true, false, true, false] 1 (.dec 7)⟩
theorem s1810_positive_checked : check 405 s1810_positive_contract = true := by decide +kernel
def s1810_positive : CertifiedContract :=
  ⟨1810, 1811, 1, (.dec 7), s1810_positive_contract, 405, s1810_positive_checked⟩

def s1811_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s1811_plain_checked : check 409 s1811_plain_contract = true := by decide +kernel
def s1811_plain : CertifiedContract :=
  ⟨1811, 1812, 0, (.inc 2), s1811_plain_contract, 409, s1811_plain_checked⟩

def s1812_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1812_plain_checked : check 436 s1812_plain_contract = true := by decide +kernel
def s1812_plain : CertifiedContract :=
  ⟨1812, 1813, 0, (.inc 8), s1812_plain_contract, 436, s1812_plain_checked⟩

def s1813_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, true, false, false] 0 .none⟩
theorem s1813_plain_checked : check 119 s1813_plain_contract = true := by decide +kernel
def s1813_plain : CertifiedContract :=
  ⟨1813, 1810, 0, .none, s1813_plain_contract, 119, s1813_plain_checked⟩

def s1814_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, false, false] 0 .none⟩
theorem s1814_zero_checked : check 408 s1814_zero_contract = true := by decide +kernel
def s1814_zero : CertifiedContract :=
  ⟨1814, 1817, 0, .none, s1814_zero_contract, 408, s1814_zero_checked⟩

def s1814_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s1814_positive_checked : check 405 s1814_positive_contract = true := by decide +kernel
def s1814_positive : CertifiedContract :=
  ⟨1814, 1815, 1, (.dec 8), s1814_positive_contract, 405, s1814_positive_checked⟩

def s1815_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, true, true, true, true] 0 (.inc 7)⟩
theorem s1815_plain_checked : check 436 s1815_plain_contract = true := by decide +kernel
def s1815_plain : CertifiedContract :=
  ⟨1815, 1816, 0, (.inc 7), s1815_plain_contract, 436, s1815_plain_checked⟩

def s1816_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s1816_plain_checked : check 113 s1816_plain_contract = true := by decide +kernel
def s1816_plain : CertifiedContract :=
  ⟨1816, 1814, 0, .none, s1816_plain_contract, 113, s1816_plain_checked⟩

def s1817_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, true, false] 0 .none⟩
theorem s1817_zero_checked : check 402 s1817_zero_contract = true := by decide +kernel
def s1817_zero : CertifiedContract :=
  ⟨1817, 1825, 0, .none, s1817_zero_contract, 402, s1817_zero_checked⟩

def s1817_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s1817_positive_checked : check 408 s1817_positive_contract = true := by decide +kernel
def s1817_positive : CertifiedContract :=
  ⟨1817, 1818, 1, (.dec 0), s1817_positive_contract, 408, s1817_positive_checked⟩

def s1818_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s1818_plain_checked : check 418 s1818_plain_contract = true := by decide +kernel
def s1818_plain : CertifiedContract :=
  ⟨1818, 1819, 0, (.inc 5), s1818_plain_contract, 418, s1818_plain_checked⟩

def s1819_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1819_zero_checked : check 444 s1819_zero_contract = true := by decide +kernel
def s1819_zero : CertifiedContract :=
  ⟨1819, 1821, 0, .none, s1819_zero_contract, 444, s1819_zero_checked⟩

def s1819_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s1819_positive_checked : check 450 s1819_positive_contract = true := by decide +kernel
def s1819_positive : CertifiedContract :=
  ⟨1819, 1820, 1, (.dec 8), s1819_positive_contract, 450, s1819_positive_checked⟩

def s1820_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s1820_plain_checked : check 125 s1820_plain_contract = true := by decide +kernel
def s1820_plain : CertifiedContract :=
  ⟨1820, 1824, 0, .none, s1820_plain_contract, 125, s1820_plain_checked⟩

def s1821_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s1821_zero_checked : check 456 s1821_zero_contract = true := by decide +kernel
def s1821_zero : CertifiedContract :=
  ⟨1821, 1824, 0, .none, s1821_zero_contract, 456, s1821_zero_checked⟩

end PA211.UserCandidate.RuntimeShards.S036
