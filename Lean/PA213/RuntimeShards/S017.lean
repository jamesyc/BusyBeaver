import PA213.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S017
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s0835_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0835_zero_checked : check 380 s0835_zero_contract = true := by decide +kernel
def s0835_zero : CertifiedContract :=
  ⟨835, 837, 0, .none, s0835_zero_contract, 380, s0835_zero_checked⟩

def s0835_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s0835_positive_checked : check 386 s0835_positive_contract = true := by decide +kernel
def s0835_positive : CertifiedContract :=
  ⟨835, 836, 1, (.dec 8), s0835_positive_contract, 386, s0835_positive_checked⟩

def s0836_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, true, true, true] 0 .none⟩
theorem s0836_plain_checked : check 103 s0836_plain_contract = true := by decide +kernel
def s0836_plain : CertifiedContract :=
  ⟨836, 840, 0, .none, s0836_plain_contract, 103, s0836_plain_checked⟩

def s0837_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, true, true, true] 0 .none⟩
theorem s0837_zero_checked : check 392 s0837_zero_contract = true := by decide +kernel
def s0837_zero : CertifiedContract :=
  ⟨837, 840, 0, .none, s0837_zero_contract, 392, s0837_zero_checked⟩

def s0837_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0837_positive_checked : check 395 s0837_positive_contract = true := by decide +kernel
def s0837_positive : CertifiedContract :=
  ⟨837, 838, 1, (.dec 5), s0837_positive_contract, 395, s0837_positive_checked⟩

def s0838_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0838_plain_checked : check 399 s0838_plain_contract = true := by decide +kernel
def s0838_plain : CertifiedContract :=
  ⟨838, 839, 0, (.inc 8), s0838_plain_contract, 399, s0838_plain_checked⟩

def s0839_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0839_plain_checked : check 106 s0839_plain_contract = true := by decide +kernel
def s0839_plain : CertifiedContract :=
  ⟨839, 837, 0, .none, s0839_plain_contract, 106, s0839_plain_checked⟩

def s0840_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s0840_plain_checked : check 97 s0840_plain_contract = true := by decide +kernel
def s0840_plain : CertifiedContract :=
  ⟨840, 833, 0, .none, s0840_plain_contract, 97, s0840_plain_checked⟩

def s0841_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, false, false, false] 0 .none⟩
theorem s0841_zero_checked : check 338 s0841_zero_contract = true := by decide +kernel
def s0841_zero : CertifiedContract :=
  ⟨841, 844, 0, .none, s0841_zero_contract, 338, s0841_zero_checked⟩

def s0841_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, true, true, false] 1 (.dec 5)⟩
theorem s0841_positive_checked : check 341 s0841_positive_contract = true := by decide +kernel
def s0841_positive : CertifiedContract :=
  ⟨841, 842, 1, (.dec 5), s0841_positive_contract, 341, s0841_positive_checked⟩

def s0842_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, true, true, true] 0 (.inc 0)⟩
theorem s0842_plain_checked : check 354 s0842_plain_contract = true := by decide +kernel
def s0842_plain : CertifiedContract :=
  ⟨842, 843, 0, (.inc 0), s0842_plain_contract, 354, s0842_plain_checked⟩

def s0843_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, false, true, false] 0 .none⟩
theorem s0843_plain_checked : check 91 s0843_plain_contract = true := by decide +kernel
def s0843_plain : CertifiedContract :=
  ⟨843, 841, 0, .none, s0843_plain_contract, 91, s0843_plain_checked⟩

def s0844_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, false, true, false] 0 .none⟩
theorem s0844_zero_checked : check 335 s0844_zero_contract = true := by decide +kernel
def s0844_zero : CertifiedContract :=
  ⟨844, 848, 0, .none, s0844_zero_contract, 335, s0844_zero_checked⟩

def s0844_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0844_positive_checked : check 341 s0844_positive_contract = true := by decide +kernel
def s0844_positive : CertifiedContract :=
  ⟨844, 845, 1, (.dec 2), s0844_positive_contract, 341, s0844_positive_checked⟩

def s0845_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0845_plain_checked : check 354 s0845_plain_contract = true := by decide +kernel
def s0845_plain : CertifiedContract :=
  ⟨845, 846, 0, (.inc 5), s0845_plain_contract, 354, s0845_plain_checked⟩

def s0846_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0846_plain_checked : check 381 s0846_plain_contract = true := by decide +kernel
def s0846_plain : CertifiedContract :=
  ⟨846, 847, 0, (.inc 8), s0846_plain_contract, 381, s0846_plain_checked⟩

def s0847_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, false, false, false] 0 .none⟩
theorem s0847_plain_checked : check 100 s0847_plain_contract = true := by decide +kernel
def s0847_plain : CertifiedContract :=
  ⟨847, 844, 0, .none, s0847_plain_contract, 100, s0847_plain_checked⟩

def s0848_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s0848_zero_checked : check 356 s0848_zero_contract = true := by decide +kernel
def s0848_zero : CertifiedContract :=
  ⟨848, 854, 0, .none, s0848_zero_contract, 356, s0848_zero_checked⟩

def s0848_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0848_positive_checked : check 359 s0848_positive_contract = true := by decide +kernel
def s0848_positive : CertifiedContract :=
  ⟨848, 849, 1, (.dec 8), s0848_positive_contract, 359, s0848_positive_checked⟩

def s0849_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0849_plain_checked : check 354 s0849_plain_contract = true := by decide +kernel
def s0849_plain : CertifiedContract :=
  ⟨849, 850, 0, (.inc 5), s0849_plain_contract, 354, s0849_plain_checked⟩

def s0850_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, false, true, true, true] 0 .none⟩
theorem s0850_zero_checked : check 374 s0850_zero_contract = true := by decide +kernel
def s0850_zero : CertifiedContract :=
  ⟨850, 853, 0, .none, s0850_zero_contract, 374, s0850_zero_checked⟩

def s0850_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0850_positive_checked : check 377 s0850_positive_contract = true := by decide +kernel
def s0850_positive : CertifiedContract :=
  ⟨850, 851, 1, (.dec 8), s0850_positive_contract, 377, s0850_positive_checked⟩

def s0851_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0851_plain_checked : check 372 s0851_plain_contract = true := by decide +kernel
def s0851_plain : CertifiedContract :=
  ⟨851, 852, 0, (.inc 2), s0851_plain_contract, 372, s0851_plain_checked⟩

def s0852_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0852_plain_checked : check 100 s0852_plain_contract = true := by decide +kernel
def s0852_plain : CertifiedContract :=
  ⟨852, 850, 0, .none, s0852_plain_contract, 100, s0852_plain_checked⟩

def s0853_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, false, false, false] 0 .none⟩
theorem s0853_plain_checked : check 103 s0853_plain_contract = true := by decide +kernel
def s0853_plain : CertifiedContract :=
  ⟨853, 844, 0, .none, s0853_plain_contract, 103, s0853_plain_checked⟩

def s0854_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s0854_zero_checked : check 341 s0854_zero_contract = true := by decide +kernel
def s0854_zero : CertifiedContract :=
  ⟨854, 860, 0, .none, s0854_zero_contract, 341, s0854_zero_checked⟩

def s0854_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s0854_positive_checked : check 341 s0854_positive_contract = true := by decide +kernel
def s0854_positive : CertifiedContract :=
  ⟨854, 855, 1, (.dec 5), s0854_positive_contract, 341, s0854_positive_checked⟩

def s0855_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s0855_plain_checked : check 354 s0855_plain_contract = true := by decide +kernel
def s0855_plain : CertifiedContract :=
  ⟨855, 856, 0, (.inc 2), s0855_plain_contract, 354, s0855_plain_checked⟩

def s0856_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s0856_plain_checked : check 357 s0856_plain_contract = true := by decide +kernel
def s0856_plain : CertifiedContract :=
  ⟨856, 857, 0, (.inc 2), s0856_plain_contract, 357, s0856_plain_checked⟩

def s0857_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s0857_plain_checked : check 354 s0857_plain_contract = true := by decide +kernel
def s0857_plain : CertifiedContract :=
  ⟨857, 858, 0, (.inc 2), s0857_plain_contract, 354, s0857_plain_checked⟩

def s0858_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, true, true, true] 0 (.inc 2)⟩
theorem s0858_plain_checked : check 360 s0858_plain_contract = true := by decide +kernel
def s0858_plain : CertifiedContract :=
  ⟨858, 859, 0, (.inc 2), s0858_plain_contract, 360, s0858_plain_checked⟩

def s0859_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s0859_plain_checked : check 88 s0859_plain_contract = true := by decide +kernel
def s0859_plain : CertifiedContract :=
  ⟨859, 854, 0, .none, s0859_plain_contract, 88, s0859_plain_checked⟩

def s0860_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, true, false] 0 .none⟩
theorem s0860_zero_checked : check 347 s0860_zero_contract = true := by decide +kernel
def s0860_zero : CertifiedContract :=
  ⟨860, 868, 0, .none, s0860_zero_contract, 347, s0860_zero_checked⟩

def s0860_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, false, true, false] 1 (.dec 0)⟩
theorem s0860_positive_checked : check 353 s0860_positive_contract = true := by decide +kernel
def s0860_positive : CertifiedContract :=
  ⟨860, 861, 1, (.dec 0), s0860_positive_contract, 353, s0860_positive_checked⟩

def s0861_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s0861_plain_checked : check 363 s0861_plain_contract = true := by decide +kernel
def s0861_plain : CertifiedContract :=
  ⟨861, 862, 0, (.inc 5), s0861_plain_contract, 363, s0861_plain_checked⟩

def s0862_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s0862_zero_checked : check 389 s0862_zero_contract = true := by decide +kernel
def s0862_zero : CertifiedContract :=
  ⟨862, 864, 0, .none, s0862_zero_contract, 389, s0862_zero_checked⟩

def s0862_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s0862_positive_checked : check 395 s0862_positive_contract = true := by decide +kernel
def s0862_positive : CertifiedContract :=
  ⟨862, 863, 1, (.dec 8), s0862_positive_contract, 395, s0862_positive_checked⟩

def s0863_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, false, true, true, true] 0 .none⟩
theorem s0863_plain_checked : check 106 s0863_plain_contract = true := by decide +kernel
def s0863_plain : CertifiedContract :=
  ⟨863, 867, 0, .none, s0863_plain_contract, 106, s0863_plain_checked⟩

def s0864_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, false, true, true, true] 0 .none⟩
theorem s0864_zero_checked : check 401 s0864_zero_contract = true := by decide +kernel
def s0864_zero : CertifiedContract :=
  ⟨864, 867, 0, .none, s0864_zero_contract, 401, s0864_zero_checked⟩

def s0864_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0864_positive_checked : check 404 s0864_positive_contract = true := by decide +kernel
def s0864_positive : CertifiedContract :=
  ⟨864, 865, 1, (.dec 5), s0864_positive_contract, 404, s0864_positive_checked⟩

def s0865_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0865_plain_checked : check 408 s0865_plain_contract = true := by decide +kernel
def s0865_plain : CertifiedContract :=
  ⟨865, 866, 0, (.inc 8), s0865_plain_contract, 408, s0865_plain_checked⟩

def s0866_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s0866_plain_checked : check 109 s0866_plain_contract = true := by decide +kernel
def s0866_plain : CertifiedContract :=
  ⟨866, 864, 0, .none, s0866_plain_contract, 109, s0866_plain_checked⟩

def s0867_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s0867_plain_checked : check 100 s0867_plain_contract = true := by decide +kernel
def s0867_plain : CertifiedContract :=
  ⟨867, 860, 0, .none, s0867_plain_contract, 100, s0867_plain_checked⟩

def s0868_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s0868_zero_checked : check 347 s0868_zero_contract = true := by decide +kernel
def s0868_zero : CertifiedContract :=
  ⟨868, 871, 0, .none, s0868_zero_contract, 347, s0868_zero_checked⟩

def s0868_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0868_positive_checked : check 350 s0868_positive_contract = true := by decide +kernel
def s0868_positive : CertifiedContract :=
  ⟨868, 869, 1, (.dec 5), s0868_positive_contract, 350, s0868_positive_checked⟩

def s0869_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, true, true, true] 0 (.inc 0)⟩
theorem s0869_plain_checked : check 363 s0869_plain_contract = true := by decide +kernel
def s0869_plain : CertifiedContract :=
  ⟨869, 870, 0, (.inc 0), s0869_plain_contract, 363, s0869_plain_checked⟩

def s0870_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, false, true, false] 0 .none⟩
theorem s0870_plain_checked : check 94 s0870_plain_contract = true := by decide +kernel
def s0870_plain : CertifiedContract :=
  ⟨870, 868, 0, .none, s0870_plain_contract, 94, s0870_plain_checked⟩

def s0871_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s0871_zero_checked : check 344 s0871_zero_contract = true := by decide +kernel
def s0871_zero : CertifiedContract :=
  ⟨871, 875, 0, .none, s0871_zero_contract, 344, s0871_zero_checked⟩

def s0871_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0871_positive_checked : check 350 s0871_positive_contract = true := by decide +kernel
def s0871_positive : CertifiedContract :=
  ⟨871, 872, 1, (.dec 2), s0871_positive_contract, 350, s0871_positive_checked⟩

def s0872_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0872_plain_checked : check 363 s0872_plain_contract = true := by decide +kernel
def s0872_plain : CertifiedContract :=
  ⟨872, 873, 0, (.inc 5), s0872_plain_contract, 363, s0872_plain_checked⟩

def s0873_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0873_plain_checked : check 390 s0873_plain_contract = true := by decide +kernel
def s0873_plain : CertifiedContract :=
  ⟨873, 874, 0, (.inc 8), s0873_plain_contract, 390, s0873_plain_checked⟩

def s0874_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s0874_plain_checked : check 103 s0874_plain_contract = true := by decide +kernel
def s0874_plain : CertifiedContract :=
  ⟨874, 871, 0, .none, s0874_plain_contract, 103, s0874_plain_checked⟩

def s0875_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s0875_zero_checked : check 365 s0875_zero_contract = true := by decide +kernel
def s0875_zero : CertifiedContract :=
  ⟨875, 881, 0, .none, s0875_zero_contract, 365, s0875_zero_checked⟩

def s0875_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0875_positive_checked : check 368 s0875_positive_contract = true := by decide +kernel
def s0875_positive : CertifiedContract :=
  ⟨875, 876, 1, (.dec 8), s0875_positive_contract, 368, s0875_positive_checked⟩

def s0876_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0876_plain_checked : check 363 s0876_plain_contract = true := by decide +kernel
def s0876_plain : CertifiedContract :=
  ⟨876, 877, 0, (.inc 5), s0876_plain_contract, 363, s0876_plain_checked⟩

def s0877_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s0877_zero_checked : check 383 s0877_zero_contract = true := by decide +kernel
def s0877_zero : CertifiedContract :=
  ⟨877, 880, 0, .none, s0877_zero_contract, 383, s0877_zero_checked⟩

def s0877_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0877_positive_checked : check 386 s0877_positive_contract = true := by decide +kernel
def s0877_positive : CertifiedContract :=
  ⟨877, 878, 1, (.dec 8), s0877_positive_contract, 386, s0877_positive_checked⟩

def s0878_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0878_plain_checked : check 381 s0878_plain_contract = true := by decide +kernel
def s0878_plain : CertifiedContract :=
  ⟨878, 879, 0, (.inc 2), s0878_plain_contract, 381, s0878_plain_checked⟩

def s0879_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0879_plain_checked : check 103 s0879_plain_contract = true := by decide +kernel
def s0879_plain : CertifiedContract :=
  ⟨879, 877, 0, .none, s0879_plain_contract, 103, s0879_plain_checked⟩

def s0880_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s0880_plain_checked : check 106 s0880_plain_contract = true := by decide +kernel
def s0880_plain : CertifiedContract :=
  ⟨880, 871, 0, .none, s0880_plain_contract, 106, s0880_plain_checked⟩

def s0881_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, true, false, false, false] 0 .none⟩
theorem s0881_zero_checked : check 353 s0881_zero_contract = true := by decide +kernel
def s0881_zero : CertifiedContract :=
  ⟨881, 887, 0, .none, s0881_zero_contract, 353, s0881_zero_checked⟩

def s0881_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s0881_positive_checked : check 350 s0881_positive_contract = true := by decide +kernel
def s0881_positive : CertifiedContract :=
  ⟨881, 882, 1, (.dec 5), s0881_positive_contract, 350, s0881_positive_checked⟩

def s0882_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s0882_plain_checked : check 363 s0882_plain_contract = true := by decide +kernel
def s0882_plain : CertifiedContract :=
  ⟨882, 883, 0, (.inc 2), s0882_plain_contract, 363, s0882_plain_checked⟩

def s0883_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, false, true, true, false, false, true, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s0883_plain_checked : check 366 s0883_plain_contract = true := by decide +kernel
def s0883_plain : CertifiedContract :=
  ⟨883, 884, 0, (.inc 2), s0883_plain_contract, 366, s0883_plain_checked⟩

def nonterminal : Array CertifiedContract := #[
  s0835_zero,
  s0835_positive,
  s0836_plain,
  s0837_zero,
  s0837_positive,
  s0838_plain,
  s0839_plain,
  s0840_plain,
  s0841_zero,
  s0841_positive,
  s0842_plain,
  s0843_plain,
  s0844_zero,
  s0844_positive,
  s0845_plain,
  s0846_plain,
  s0847_plain,
  s0848_zero,
  s0848_positive,
  s0849_plain,
  s0850_zero,
  s0850_positive,
  s0851_plain,
  s0852_plain,
  s0853_plain,
  s0854_zero,
  s0854_positive,
  s0855_plain,
  s0856_plain,
  s0857_plain,
  s0858_plain,
  s0859_plain,
  s0860_zero,
  s0860_positive,
  s0861_plain,
  s0862_zero,
  s0862_positive,
  s0863_plain,
  s0864_zero,
  s0864_positive,
  s0865_plain,
  s0866_plain,
  s0867_plain,
  s0868_zero,
  s0868_positive,
  s0869_plain,
  s0870_plain,
  s0871_zero,
  s0871_positive,
  s0872_plain,
  s0873_plain,
  s0874_plain,
  s0875_zero,
  s0875_positive,
  s0876_plain,
  s0877_zero,
  s0877_positive,
  s0878_plain,
  s0879_plain,
  s0880_plain,
  s0881_zero,
  s0881_positive,
  s0882_plain,
  s0883_plain
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S017
