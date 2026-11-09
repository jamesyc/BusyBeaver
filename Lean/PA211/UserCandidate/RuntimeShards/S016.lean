import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S016
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s0784_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, false, true, false] 0 .none⟩
theorem s0784_plain_checked : check 98 s0784_plain_contract = true := by decide +kernel
def s0784_plain : CertifiedContract :=
  ⟨784, 782, 0, .none, s0784_plain_contract, 98, s0784_plain_checked⟩

def s0785_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s0785_zero_checked : check 354 s0785_zero_contract = true := by decide +kernel
def s0785_zero : CertifiedContract :=
  ⟨785, 789, 0, .none, s0785_zero_contract, 354, s0785_zero_checked⟩

def s0785_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0785_positive_checked : check 360 s0785_positive_contract = true := by decide +kernel
def s0785_positive : CertifiedContract :=
  ⟨785, 786, 1, (.dec 2), s0785_positive_contract, 360, s0785_positive_checked⟩

def s0786_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0786_plain_checked : check 373 s0786_plain_contract = true := by decide +kernel
def s0786_plain : CertifiedContract :=
  ⟨786, 787, 0, (.inc 5), s0786_plain_contract, 373, s0786_plain_checked⟩

def s0787_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0787_plain_checked : check 400 s0787_plain_contract = true := by decide +kernel
def s0787_plain : CertifiedContract :=
  ⟨787, 788, 0, (.inc 8), s0787_plain_contract, 400, s0787_plain_checked⟩

def s0788_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0788_plain_checked : check 107 s0788_plain_contract = true := by decide +kernel
def s0788_plain : CertifiedContract :=
  ⟨788, 785, 0, .none, s0788_plain_contract, 107, s0788_plain_checked⟩

def s0789_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s0789_zero_checked : check 375 s0789_zero_contract = true := by decide +kernel
def s0789_zero : CertifiedContract :=
  ⟨789, 795, 0, .none, s0789_zero_contract, 375, s0789_zero_checked⟩

def s0789_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0789_positive_checked : check 378 s0789_positive_contract = true := by decide +kernel
def s0789_positive : CertifiedContract :=
  ⟨789, 790, 1, (.dec 8), s0789_positive_contract, 378, s0789_positive_checked⟩

def s0790_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0790_plain_checked : check 373 s0790_plain_contract = true := by decide +kernel
def s0790_plain : CertifiedContract :=
  ⟨790, 791, 0, (.inc 5), s0790_plain_contract, 373, s0790_plain_checked⟩

def s0791_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s0791_zero_checked : check 393 s0791_zero_contract = true := by decide +kernel
def s0791_zero : CertifiedContract :=
  ⟨791, 794, 0, .none, s0791_zero_contract, 393, s0791_zero_checked⟩

def s0791_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0791_positive_checked : check 396 s0791_positive_contract = true := by decide +kernel
def s0791_positive : CertifiedContract :=
  ⟨791, 792, 1, (.dec 8), s0791_positive_contract, 396, s0791_positive_checked⟩

def s0792_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0792_plain_checked : check 391 s0792_plain_contract = true := by decide +kernel
def s0792_plain : CertifiedContract :=
  ⟨792, 793, 0, (.inc 2), s0792_plain_contract, 391, s0792_plain_checked⟩

def s0793_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0793_plain_checked : check 107 s0793_plain_contract = true := by decide +kernel
def s0793_plain : CertifiedContract :=
  ⟨793, 791, 0, .none, s0793_plain_contract, 107, s0793_plain_checked⟩

def s0794_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s0794_plain_checked : check 110 s0794_plain_contract = true := by decide +kernel
def s0794_plain : CertifiedContract :=
  ⟨794, 785, 0, .none, s0794_plain_contract, 110, s0794_plain_checked⟩

def s0795_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, true, false] 0 .none⟩
theorem s0795_zero_checked : check 360 s0795_zero_contract = true := by decide +kernel
def s0795_zero : CertifiedContract :=
  ⟨795, 801, 0, .none, s0795_zero_contract, 360, s0795_zero_checked⟩

def s0795_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s0795_positive_checked : check 360 s0795_positive_contract = true := by decide +kernel
def s0795_positive : CertifiedContract :=
  ⟨795, 796, 1, (.dec 5), s0795_positive_contract, 360, s0795_positive_checked⟩

def s0796_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s0796_plain_checked : check 373 s0796_plain_contract = true := by decide +kernel
def s0796_plain : CertifiedContract :=
  ⟨796, 797, 0, (.inc 2), s0796_plain_contract, 373, s0796_plain_checked⟩

def s0797_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s0797_plain_checked : check 376 s0797_plain_contract = true := by decide +kernel
def s0797_plain : CertifiedContract :=
  ⟨797, 798, 0, (.inc 2), s0797_plain_contract, 376, s0797_plain_checked⟩

def s0798_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s0798_plain_checked : check 382 s0798_plain_contract = true := by decide +kernel
def s0798_plain : CertifiedContract :=
  ⟨798, 799, 0, (.inc 2), s0798_plain_contract, 382, s0798_plain_checked⟩

def s0799_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s0799_plain_checked : check 388 s0799_plain_contract = true := by decide +kernel
def s0799_plain : CertifiedContract :=
  ⟨799, 800, 0, (.inc 2), s0799_plain_contract, 388, s0799_plain_checked⟩

def s0800_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s0800_plain_checked : check 95 s0800_plain_contract = true := by decide +kernel
def s0800_plain : CertifiedContract :=
  ⟨800, 795, 0, .none, s0800_plain_contract, 95, s0800_plain_checked⟩

def s0801_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0801_plain_checked : check 328 s0801_plain_contract = true := by decide +kernel
def s0801_plain : CertifiedContract :=
  ⟨801, 802, 0, (.inc 2), s0801_plain_contract, 328, s0801_plain_checked⟩

def s0802_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, true] 0 (.inc 2)⟩
theorem s0802_plain_checked : check 337 s0802_plain_contract = true := by decide +kernel
def s0802_plain : CertifiedContract :=
  ⟨802, 803, 0, (.inc 2), s0802_plain_contract, 337, s0802_plain_checked⟩

def s0803_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, false] 0 (.inc 2)⟩
theorem s0803_plain_checked : check 301 s0803_plain_contract = true := by decide +kernel
def s0803_plain : CertifiedContract :=
  ⟨803, 804, 0, (.inc 2), s0803_plain_contract, 301, s0803_plain_checked⟩

def s0804_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, true, false] 0 .none⟩
theorem s0804_zero_checked : check 312 s0804_zero_contract = true := by decide +kernel
def s0804_zero : CertifiedContract :=
  ⟨804, 812, 0, .none, s0804_zero_contract, 312, s0804_zero_checked⟩

def s0804_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, false] 1 (.dec 0)⟩
theorem s0804_positive_checked : check 318 s0804_positive_contract = true := by decide +kernel
def s0804_positive : CertifiedContract :=
  ⟨804, 805, 1, (.dec 0), s0804_positive_contract, 318, s0804_positive_checked⟩

def s0805_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s0805_plain_checked : check 328 s0805_plain_contract = true := by decide +kernel
def s0805_plain : CertifiedContract :=
  ⟨805, 806, 0, (.inc 5), s0805_plain_contract, 328, s0805_plain_checked⟩

def s0806_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0806_zero_checked : check 354 s0806_zero_contract = true := by decide +kernel
def s0806_zero : CertifiedContract :=
  ⟨806, 808, 0, .none, s0806_zero_contract, 354, s0806_zero_checked⟩

def s0806_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s0806_positive_checked : check 360 s0806_positive_contract = true := by decide +kernel
def s0806_positive : CertifiedContract :=
  ⟨806, 807, 1, (.dec 8), s0806_positive_contract, 360, s0806_positive_checked⟩

def s0807_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s0807_plain_checked : check 95 s0807_plain_contract = true := by decide +kernel
def s0807_plain : CertifiedContract :=
  ⟨807, 811, 0, .none, s0807_plain_contract, 95, s0807_plain_checked⟩

def s0808_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, true] 0 .none⟩
theorem s0808_zero_checked : check 366 s0808_zero_contract = true := by decide +kernel
def s0808_zero : CertifiedContract :=
  ⟨808, 811, 0, .none, s0808_zero_contract, 366, s0808_zero_checked⟩

def s0808_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0808_positive_checked : check 369 s0808_positive_contract = true := by decide +kernel
def s0808_positive : CertifiedContract :=
  ⟨808, 809, 1, (.dec 5), s0808_positive_contract, 369, s0808_positive_checked⟩

def s0809_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0809_plain_checked : check 373 s0809_plain_contract = true := by decide +kernel
def s0809_plain : CertifiedContract :=
  ⟨809, 810, 0, (.inc 8), s0809_plain_contract, 373, s0809_plain_checked⟩

def s0810_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0810_plain_checked : check 98 s0810_plain_contract = true := by decide +kernel
def s0810_plain : CertifiedContract :=
  ⟨810, 808, 0, .none, s0810_plain_contract, 98, s0810_plain_checked⟩

def s0811_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, false, false] 0 .none⟩
theorem s0811_plain_checked : check 89 s0811_plain_contract = true := by decide +kernel
def s0811_plain : CertifiedContract :=
  ⟨811, 804, 0, .none, s0811_plain_contract, 89, s0811_plain_checked⟩

def s0812_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s0812_zero_checked : check 312 s0812_zero_contract = true := by decide +kernel
def s0812_zero : CertifiedContract :=
  ⟨812, 815, 0, .none, s0812_zero_contract, 312, s0812_zero_checked⟩

def s0812_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, true, true, false] 1 (.dec 5)⟩
theorem s0812_positive_checked : check 315 s0812_positive_contract = true := by decide +kernel
def s0812_positive : CertifiedContract :=
  ⟨812, 813, 1, (.dec 5), s0812_positive_contract, 315, s0812_positive_checked⟩

def s0813_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, true, true, true] 0 (.inc 0)⟩
theorem s0813_plain_checked : check 328 s0813_plain_contract = true := by decide +kernel
def s0813_plain : CertifiedContract :=
  ⟨813, 814, 0, (.inc 0), s0813_plain_contract, 328, s0813_plain_checked⟩

def s0814_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, false, true, false] 0 .none⟩
theorem s0814_plain_checked : check 83 s0814_plain_contract = true := by decide +kernel
def s0814_plain : CertifiedContract :=
  ⟨814, 812, 0, .none, s0814_plain_contract, 83, s0814_plain_checked⟩

def s0815_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, false] 0 .none⟩
theorem s0815_zero_checked : check 309 s0815_zero_contract = true := by decide +kernel
def s0815_zero : CertifiedContract :=
  ⟨815, 819, 0, .none, s0815_zero_contract, 309, s0815_zero_checked⟩

def s0815_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0815_positive_checked : check 315 s0815_positive_contract = true := by decide +kernel
def s0815_positive : CertifiedContract :=
  ⟨815, 816, 1, (.dec 2), s0815_positive_contract, 315, s0815_positive_checked⟩

def s0816_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0816_plain_checked : check 328 s0816_plain_contract = true := by decide +kernel
def s0816_plain : CertifiedContract :=
  ⟨816, 817, 0, (.inc 5), s0816_plain_contract, 328, s0816_plain_checked⟩

def s0817_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0817_plain_checked : check 355 s0817_plain_contract = true := by decide +kernel
def s0817_plain : CertifiedContract :=
  ⟨817, 818, 0, (.inc 8), s0817_plain_contract, 355, s0817_plain_checked⟩

def s0818_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s0818_plain_checked : check 92 s0818_plain_contract = true := by decide +kernel
def s0818_plain : CertifiedContract :=
  ⟨818, 815, 0, .none, s0818_plain_contract, 92, s0818_plain_checked⟩

def s0819_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, false] 0 .none⟩
theorem s0819_zero_checked : check 330 s0819_zero_contract = true := by decide +kernel
def s0819_zero : CertifiedContract :=
  ⟨819, 825, 0, .none, s0819_zero_contract, 330, s0819_zero_checked⟩

def s0819_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0819_positive_checked : check 333 s0819_positive_contract = true := by decide +kernel
def s0819_positive : CertifiedContract :=
  ⟨819, 820, 1, (.dec 8), s0819_positive_contract, 333, s0819_positive_checked⟩

def s0820_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0820_plain_checked : check 328 s0820_plain_contract = true := by decide +kernel
def s0820_plain : CertifiedContract :=
  ⟨820, 821, 0, (.inc 5), s0820_plain_contract, 328, s0820_plain_checked⟩

def s0821_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, true, true] 0 .none⟩
theorem s0821_zero_checked : check 348 s0821_zero_contract = true := by decide +kernel
def s0821_zero : CertifiedContract :=
  ⟨821, 824, 0, .none, s0821_zero_contract, 348, s0821_zero_checked⟩

def s0821_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0821_positive_checked : check 351 s0821_positive_contract = true := by decide +kernel
def s0821_positive : CertifiedContract :=
  ⟨821, 822, 1, (.dec 8), s0821_positive_contract, 351, s0821_positive_checked⟩

def s0822_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0822_plain_checked : check 346 s0822_plain_contract = true := by decide +kernel
def s0822_plain : CertifiedContract :=
  ⟨822, 823, 0, (.inc 2), s0822_plain_contract, 346, s0822_plain_checked⟩

def s0823_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0823_plain_checked : check 92 s0823_plain_contract = true := by decide +kernel
def s0823_plain : CertifiedContract :=
  ⟨823, 821, 0, .none, s0823_plain_contract, 92, s0823_plain_checked⟩

def s0824_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s0824_plain_checked : check 95 s0824_plain_contract = true := by decide +kernel
def s0824_plain : CertifiedContract :=
  ⟨824, 815, 0, .none, s0824_plain_contract, 95, s0824_plain_checked⟩

def s0825_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, true, false] 0 .none⟩
theorem s0825_zero_checked : check 315 s0825_zero_contract = true := by decide +kernel
def s0825_zero : CertifiedContract :=
  ⟨825, 831, 0, .none, s0825_zero_contract, 315, s0825_zero_checked⟩

def s0825_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s0825_positive_checked : check 315 s0825_positive_contract = true := by decide +kernel
def s0825_positive : CertifiedContract :=
  ⟨825, 826, 1, (.dec 5), s0825_positive_contract, 315, s0825_positive_checked⟩

def s0826_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s0826_plain_checked : check 328 s0826_plain_contract = true := by decide +kernel
def s0826_plain : CertifiedContract :=
  ⟨826, 827, 0, (.inc 2), s0826_plain_contract, 328, s0826_plain_checked⟩

def s0827_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s0827_plain_checked : check 331 s0827_plain_contract = true := by decide +kernel
def s0827_plain : CertifiedContract :=
  ⟨827, 828, 0, (.inc 2), s0827_plain_contract, 331, s0827_plain_checked⟩

def s0828_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s0828_plain_checked : check 337 s0828_plain_contract = true := by decide +kernel
def s0828_plain : CertifiedContract :=
  ⟨828, 829, 0, (.inc 2), s0828_plain_contract, 337, s0828_plain_checked⟩

def s0829_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, true, true] 0 (.inc 2)⟩
theorem s0829_plain_checked : check 343 s0829_plain_contract = true := by decide +kernel
def s0829_plain : CertifiedContract :=
  ⟨829, 830, 0, (.inc 2), s0829_plain_contract, 343, s0829_plain_checked⟩

def s0830_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, false, true, true, false] 0 .none⟩
theorem s0830_plain_checked : check 80 s0830_plain_contract = true := by decide +kernel
def s0830_plain : CertifiedContract :=
  ⟨830, 825, 0, .none, s0830_plain_contract, 80, s0830_plain_checked⟩

def s0831_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0831_plain_checked : check 283 s0831_plain_contract = true := by decide +kernel
def s0831_plain : CertifiedContract :=
  ⟨831, 832, 0, (.inc 2), s0831_plain_contract, 283, s0831_plain_checked⟩

def s0832_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, false] 0 (.inc 2)⟩
theorem s0832_plain_checked : check 289 s0832_plain_contract = true := by decide +kernel
def s0832_plain : CertifiedContract :=
  ⟨832, 833, 0, (.inc 2), s0832_plain_contract, 289, s0832_plain_checked⟩

def s0833_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, true, false] 0 .none⟩
theorem s0833_zero_checked : check 339 s0833_zero_contract = true := by decide +kernel
def s0833_zero : CertifiedContract :=
  ⟨833, 841, 0, .none, s0833_zero_contract, 339, s0833_zero_checked⟩

def s0833_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, true, false] 1 (.dec 0)⟩
theorem s0833_positive_checked : check 345 s0833_positive_contract = true := by decide +kernel
def s0833_positive : CertifiedContract :=
  ⟨833, 834, 1, (.dec 0), s0833_positive_contract, 345, s0833_positive_checked⟩

def s0834_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s0834_plain_checked : check 355 s0834_plain_contract = true := by decide +kernel
def s0834_plain : CertifiedContract :=
  ⟨834, 835, 0, (.inc 5), s0834_plain_contract, 355, s0834_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S016
