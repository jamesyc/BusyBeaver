import PA213.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S016
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s0784_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, true, false] 0 .none⟩
theorem s0784_plain_checked : check 97 s0784_plain_contract = true := by decide +kernel
def s0784_plain : CertifiedContract :=
  ⟨784, 782, 0, .none, s0784_plain_contract, 97, s0784_plain_checked⟩

def s0785_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s0785_zero_checked : check 353 s0785_zero_contract = true := by decide +kernel
def s0785_zero : CertifiedContract :=
  ⟨785, 789, 0, .none, s0785_zero_contract, 353, s0785_zero_checked⟩

def s0785_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0785_positive_checked : check 359 s0785_positive_contract = true := by decide +kernel
def s0785_positive : CertifiedContract :=
  ⟨785, 786, 1, (.dec 2), s0785_positive_contract, 359, s0785_positive_checked⟩

def s0786_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0786_plain_checked : check 372 s0786_plain_contract = true := by decide +kernel
def s0786_plain : CertifiedContract :=
  ⟨786, 787, 0, (.inc 5), s0786_plain_contract, 372, s0786_plain_checked⟩

def s0787_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0787_plain_checked : check 399 s0787_plain_contract = true := by decide +kernel
def s0787_plain : CertifiedContract :=
  ⟨787, 788, 0, (.inc 8), s0787_plain_contract, 399, s0787_plain_checked⟩

def s0788_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0788_plain_checked : check 106 s0788_plain_contract = true := by decide +kernel
def s0788_plain : CertifiedContract :=
  ⟨788, 785, 0, .none, s0788_plain_contract, 106, s0788_plain_checked⟩

def s0789_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s0789_zero_checked : check 374 s0789_zero_contract = true := by decide +kernel
def s0789_zero : CertifiedContract :=
  ⟨789, 795, 0, .none, s0789_zero_contract, 374, s0789_zero_checked⟩

def s0789_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0789_positive_checked : check 377 s0789_positive_contract = true := by decide +kernel
def s0789_positive : CertifiedContract :=
  ⟨789, 790, 1, (.dec 8), s0789_positive_contract, 377, s0789_positive_checked⟩

def s0790_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0790_plain_checked : check 372 s0790_plain_contract = true := by decide +kernel
def s0790_plain : CertifiedContract :=
  ⟨790, 791, 0, (.inc 5), s0790_plain_contract, 372, s0790_plain_checked⟩

def s0791_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s0791_zero_checked : check 392 s0791_zero_contract = true := by decide +kernel
def s0791_zero : CertifiedContract :=
  ⟨791, 794, 0, .none, s0791_zero_contract, 392, s0791_zero_checked⟩

def s0791_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0791_positive_checked : check 395 s0791_positive_contract = true := by decide +kernel
def s0791_positive : CertifiedContract :=
  ⟨791, 792, 1, (.dec 8), s0791_positive_contract, 395, s0791_positive_checked⟩

def s0792_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0792_plain_checked : check 390 s0792_plain_contract = true := by decide +kernel
def s0792_plain : CertifiedContract :=
  ⟨792, 793, 0, (.inc 2), s0792_plain_contract, 390, s0792_plain_checked⟩

def s0793_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0793_plain_checked : check 106 s0793_plain_contract = true := by decide +kernel
def s0793_plain : CertifiedContract :=
  ⟨793, 791, 0, .none, s0793_plain_contract, 106, s0793_plain_checked⟩

def s0794_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0794_plain_checked : check 109 s0794_plain_contract = true := by decide +kernel
def s0794_plain : CertifiedContract :=
  ⟨794, 785, 0, .none, s0794_plain_contract, 109, s0794_plain_checked⟩

def s0795_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, true, false] 0 .none⟩
theorem s0795_zero_checked : check 359 s0795_zero_contract = true := by decide +kernel
def s0795_zero : CertifiedContract :=
  ⟨795, 801, 0, .none, s0795_zero_contract, 359, s0795_zero_checked⟩

def s0795_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s0795_positive_checked : check 359 s0795_positive_contract = true := by decide +kernel
def s0795_positive : CertifiedContract :=
  ⟨795, 796, 1, (.dec 5), s0795_positive_contract, 359, s0795_positive_checked⟩

def s0796_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s0796_plain_checked : check 372 s0796_plain_contract = true := by decide +kernel
def s0796_plain : CertifiedContract :=
  ⟨796, 797, 0, (.inc 2), s0796_plain_contract, 372, s0796_plain_checked⟩

def s0797_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s0797_plain_checked : check 375 s0797_plain_contract = true := by decide +kernel
def s0797_plain : CertifiedContract :=
  ⟨797, 798, 0, (.inc 2), s0797_plain_contract, 375, s0797_plain_checked⟩

def s0798_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s0798_plain_checked : check 372 s0798_plain_contract = true := by decide +kernel
def s0798_plain : CertifiedContract :=
  ⟨798, 799, 0, (.inc 2), s0798_plain_contract, 372, s0798_plain_checked⟩

def s0799_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s0799_plain_checked : check 378 s0799_plain_contract = true := by decide +kernel
def s0799_plain : CertifiedContract :=
  ⟨799, 800, 0, (.inc 2), s0799_plain_contract, 378, s0799_plain_checked⟩

def s0800_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s0800_plain_checked : check 94 s0800_plain_contract = true := by decide +kernel
def s0800_plain : CertifiedContract :=
  ⟨800, 795, 0, .none, s0800_plain_contract, 94, s0800_plain_checked⟩

def s0801_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0801_plain_checked : check 327 s0801_plain_contract = true := by decide +kernel
def s0801_plain : CertifiedContract :=
  ⟨801, 802, 0, (.inc 2), s0801_plain_contract, 327, s0801_plain_checked⟩

def s0802_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, true] 0 (.inc 2)⟩
theorem s0802_plain_checked : check 336 s0802_plain_contract = true := by decide +kernel
def s0802_plain : CertifiedContract :=
  ⟨802, 803, 0, (.inc 2), s0802_plain_contract, 336, s0802_plain_checked⟩

def s0803_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, false] 0 (.inc 2)⟩
theorem s0803_plain_checked : check 300 s0803_plain_contract = true := by decide +kernel
def s0803_plain : CertifiedContract :=
  ⟨803, 804, 0, (.inc 2), s0803_plain_contract, 300, s0803_plain_checked⟩

def s0804_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, true, false] 0 .none⟩
theorem s0804_zero_checked : check 311 s0804_zero_contract = true := by decide +kernel
def s0804_zero : CertifiedContract :=
  ⟨804, 812, 0, .none, s0804_zero_contract, 311, s0804_zero_checked⟩

def s0804_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, false] 1 (.dec 0)⟩
theorem s0804_positive_checked : check 317 s0804_positive_contract = true := by decide +kernel
def s0804_positive : CertifiedContract :=
  ⟨804, 805, 1, (.dec 0), s0804_positive_contract, 317, s0804_positive_checked⟩

def s0805_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s0805_plain_checked : check 327 s0805_plain_contract = true := by decide +kernel
def s0805_plain : CertifiedContract :=
  ⟨805, 806, 0, (.inc 5), s0805_plain_contract, 327, s0805_plain_checked⟩

def s0806_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0806_zero_checked : check 353 s0806_zero_contract = true := by decide +kernel
def s0806_zero : CertifiedContract :=
  ⟨806, 808, 0, .none, s0806_zero_contract, 353, s0806_zero_checked⟩

def s0806_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s0806_positive_checked : check 359 s0806_positive_contract = true := by decide +kernel
def s0806_positive : CertifiedContract :=
  ⟨806, 807, 1, (.dec 8), s0806_positive_contract, 359, s0806_positive_checked⟩

def s0807_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s0807_plain_checked : check 94 s0807_plain_contract = true := by decide +kernel
def s0807_plain : CertifiedContract :=
  ⟨807, 811, 0, .none, s0807_plain_contract, 94, s0807_plain_checked⟩

def s0808_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s0808_zero_checked : check 365 s0808_zero_contract = true := by decide +kernel
def s0808_zero : CertifiedContract :=
  ⟨808, 811, 0, .none, s0808_zero_contract, 365, s0808_zero_checked⟩

def s0808_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0808_positive_checked : check 368 s0808_positive_contract = true := by decide +kernel
def s0808_positive : CertifiedContract :=
  ⟨808, 809, 1, (.dec 5), s0808_positive_contract, 368, s0808_positive_checked⟩

def s0809_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0809_plain_checked : check 372 s0809_plain_contract = true := by decide +kernel
def s0809_plain : CertifiedContract :=
  ⟨809, 810, 0, (.inc 8), s0809_plain_contract, 372, s0809_plain_checked⟩

def s0810_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0810_plain_checked : check 97 s0810_plain_contract = true := by decide +kernel
def s0810_plain : CertifiedContract :=
  ⟨810, 808, 0, .none, s0810_plain_contract, 97, s0810_plain_checked⟩

def s0811_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, false] 0 .none⟩
theorem s0811_plain_checked : check 88 s0811_plain_contract = true := by decide +kernel
def s0811_plain : CertifiedContract :=
  ⟨811, 804, 0, .none, s0811_plain_contract, 88, s0811_plain_checked⟩

def s0812_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s0812_zero_checked : check 311 s0812_zero_contract = true := by decide +kernel
def s0812_zero : CertifiedContract :=
  ⟨812, 815, 0, .none, s0812_zero_contract, 311, s0812_zero_checked⟩

def s0812_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, true, true, false] 1 (.dec 5)⟩
theorem s0812_positive_checked : check 314 s0812_positive_contract = true := by decide +kernel
def s0812_positive : CertifiedContract :=
  ⟨812, 813, 1, (.dec 5), s0812_positive_contract, 314, s0812_positive_checked⟩

def s0813_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, true, true, true] 0 (.inc 0)⟩
theorem s0813_plain_checked : check 327 s0813_plain_contract = true := by decide +kernel
def s0813_plain : CertifiedContract :=
  ⟨813, 814, 0, (.inc 0), s0813_plain_contract, 327, s0813_plain_checked⟩

def s0814_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, true, false] 0 .none⟩
theorem s0814_plain_checked : check 82 s0814_plain_contract = true := by decide +kernel
def s0814_plain : CertifiedContract :=
  ⟨814, 812, 0, .none, s0814_plain_contract, 82, s0814_plain_checked⟩

def s0815_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, false] 0 .none⟩
theorem s0815_zero_checked : check 308 s0815_zero_contract = true := by decide +kernel
def s0815_zero : CertifiedContract :=
  ⟨815, 819, 0, .none, s0815_zero_contract, 308, s0815_zero_checked⟩

def s0815_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0815_positive_checked : check 314 s0815_positive_contract = true := by decide +kernel
def s0815_positive : CertifiedContract :=
  ⟨815, 816, 1, (.dec 2), s0815_positive_contract, 314, s0815_positive_checked⟩

def s0816_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0816_plain_checked : check 327 s0816_plain_contract = true := by decide +kernel
def s0816_plain : CertifiedContract :=
  ⟨816, 817, 0, (.inc 5), s0816_plain_contract, 327, s0816_plain_checked⟩

def s0817_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0817_plain_checked : check 354 s0817_plain_contract = true := by decide +kernel
def s0817_plain : CertifiedContract :=
  ⟨817, 818, 0, (.inc 8), s0817_plain_contract, 354, s0817_plain_checked⟩

def s0818_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s0818_plain_checked : check 91 s0818_plain_contract = true := by decide +kernel
def s0818_plain : CertifiedContract :=
  ⟨818, 815, 0, .none, s0818_plain_contract, 91, s0818_plain_checked⟩

def s0819_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, false] 0 .none⟩
theorem s0819_zero_checked : check 329 s0819_zero_contract = true := by decide +kernel
def s0819_zero : CertifiedContract :=
  ⟨819, 825, 0, .none, s0819_zero_contract, 329, s0819_zero_checked⟩

def s0819_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0819_positive_checked : check 332 s0819_positive_contract = true := by decide +kernel
def s0819_positive : CertifiedContract :=
  ⟨819, 820, 1, (.dec 8), s0819_positive_contract, 332, s0819_positive_checked⟩

def s0820_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0820_plain_checked : check 327 s0820_plain_contract = true := by decide +kernel
def s0820_plain : CertifiedContract :=
  ⟨820, 821, 0, (.inc 5), s0820_plain_contract, 327, s0820_plain_checked⟩

def s0821_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, true, true] 0 .none⟩
theorem s0821_zero_checked : check 347 s0821_zero_contract = true := by decide +kernel
def s0821_zero : CertifiedContract :=
  ⟨821, 824, 0, .none, s0821_zero_contract, 347, s0821_zero_checked⟩

def s0821_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0821_positive_checked : check 350 s0821_positive_contract = true := by decide +kernel
def s0821_positive : CertifiedContract :=
  ⟨821, 822, 1, (.dec 8), s0821_positive_contract, 350, s0821_positive_checked⟩

def s0822_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0822_plain_checked : check 345 s0822_plain_contract = true := by decide +kernel
def s0822_plain : CertifiedContract :=
  ⟨822, 823, 0, (.inc 2), s0822_plain_contract, 345, s0822_plain_checked⟩

def s0823_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0823_plain_checked : check 91 s0823_plain_contract = true := by decide +kernel
def s0823_plain : CertifiedContract :=
  ⟨823, 821, 0, .none, s0823_plain_contract, 91, s0823_plain_checked⟩

def s0824_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s0824_plain_checked : check 94 s0824_plain_contract = true := by decide +kernel
def s0824_plain : CertifiedContract :=
  ⟨824, 815, 0, .none, s0824_plain_contract, 94, s0824_plain_checked⟩

def s0825_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, true, false] 0 .none⟩
theorem s0825_zero_checked : check 314 s0825_zero_contract = true := by decide +kernel
def s0825_zero : CertifiedContract :=
  ⟨825, 831, 0, .none, s0825_zero_contract, 314, s0825_zero_checked⟩

def s0825_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s0825_positive_checked : check 314 s0825_positive_contract = true := by decide +kernel
def s0825_positive : CertifiedContract :=
  ⟨825, 826, 1, (.dec 5), s0825_positive_contract, 314, s0825_positive_checked⟩

def s0826_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s0826_plain_checked : check 327 s0826_plain_contract = true := by decide +kernel
def s0826_plain : CertifiedContract :=
  ⟨826, 827, 0, (.inc 2), s0826_plain_contract, 327, s0826_plain_checked⟩

def s0827_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s0827_plain_checked : check 330 s0827_plain_contract = true := by decide +kernel
def s0827_plain : CertifiedContract :=
  ⟨827, 828, 0, (.inc 2), s0827_plain_contract, 330, s0827_plain_checked⟩

def s0828_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s0828_plain_checked : check 327 s0828_plain_contract = true := by decide +kernel
def s0828_plain : CertifiedContract :=
  ⟨828, 829, 0, (.inc 2), s0828_plain_contract, 327, s0828_plain_checked⟩

def s0829_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, true, true] 0 (.inc 2)⟩
theorem s0829_plain_checked : check 333 s0829_plain_contract = true := by decide +kernel
def s0829_plain : CertifiedContract :=
  ⟨829, 830, 0, (.inc 2), s0829_plain_contract, 333, s0829_plain_checked⟩

def s0830_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, false] 0 .none⟩
theorem s0830_plain_checked : check 79 s0830_plain_contract = true := by decide +kernel
def s0830_plain : CertifiedContract :=
  ⟨830, 825, 0, .none, s0830_plain_contract, 79, s0830_plain_checked⟩

def s0831_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0831_plain_checked : check 282 s0831_plain_contract = true := by decide +kernel
def s0831_plain : CertifiedContract :=
  ⟨831, 832, 0, (.inc 2), s0831_plain_contract, 282, s0831_plain_checked⟩

def s0832_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, false] 0 (.inc 2)⟩
theorem s0832_plain_checked : check 288 s0832_plain_contract = true := by decide +kernel
def s0832_plain : CertifiedContract :=
  ⟨832, 833, 0, (.inc 2), s0832_plain_contract, 288, s0832_plain_checked⟩

def s0833_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, true, false] 0 .none⟩
theorem s0833_zero_checked : check 338 s0833_zero_contract = true := by decide +kernel
def s0833_zero : CertifiedContract :=
  ⟨833, 841, 0, .none, s0833_zero_contract, 338, s0833_zero_checked⟩

def s0833_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, true, false] 1 (.dec 0)⟩
theorem s0833_positive_checked : check 344 s0833_positive_contract = true := by decide +kernel
def s0833_positive : CertifiedContract :=
  ⟨833, 834, 1, (.dec 0), s0833_positive_contract, 344, s0833_positive_checked⟩

def s0834_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s0834_plain_checked : check 354 s0834_plain_contract = true := by decide +kernel
def s0834_plain : CertifiedContract :=
  ⟨834, 835, 0, (.inc 5), s0834_plain_contract, 354, s0834_plain_checked⟩

def nonterminal : Array CertifiedContract := #[
  s0784_plain,
  s0785_zero,
  s0785_positive,
  s0786_plain,
  s0787_plain,
  s0788_plain,
  s0789_zero,
  s0789_positive,
  s0790_plain,
  s0791_zero,
  s0791_positive,
  s0792_plain,
  s0793_plain,
  s0794_plain,
  s0795_zero,
  s0795_positive,
  s0796_plain,
  s0797_plain,
  s0798_plain,
  s0799_plain,
  s0800_plain,
  s0801_plain,
  s0802_plain,
  s0803_plain,
  s0804_zero,
  s0804_positive,
  s0805_plain,
  s0806_zero,
  s0806_positive,
  s0807_plain,
  s0808_zero,
  s0808_positive,
  s0809_plain,
  s0810_plain,
  s0811_plain,
  s0812_zero,
  s0812_positive,
  s0813_plain,
  s0814_plain,
  s0815_zero,
  s0815_positive,
  s0816_plain,
  s0817_plain,
  s0818_plain,
  s0819_zero,
  s0819_positive,
  s0820_plain,
  s0821_zero,
  s0821_positive,
  s0822_plain,
  s0823_plain,
  s0824_plain,
  s0825_zero,
  s0825_positive,
  s0826_plain,
  s0827_plain,
  s0828_plain,
  s0829_plain,
  s0830_plain,
  s0831_plain,
  s0832_plain,
  s0833_zero,
  s0833_positive,
  s0834_plain
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S016
