import PA213.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S049
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s2414_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s2414_positive_checked : check 398 s2414_positive_contract = true := by decide +kernel
def s2414_positive : CertifiedContract :=
  ⟨2414, 2415, 1, (.dec 0), s2414_positive_contract, 398, s2414_positive_checked⟩

def s2415_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s2415_plain_checked : check 390 s2415_plain_contract = true := by decide +kernel
def s2415_plain : CertifiedContract :=
  ⟨2415, 2416, 0, (.inc 2), s2415_plain_contract, 390, s2415_plain_checked⟩

def s2416_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s2416_plain_checked : check 106 s2416_plain_contract = true := by decide +kernel
def s2416_plain : CertifiedContract :=
  ⟨2416, 2414, 0, .none, s2416_plain_contract, 106, s2416_plain_checked⟩

def s2417_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s2417_zero_checked : check 398 s2417_zero_contract = true := by decide +kernel
def s2417_zero : CertifiedContract :=
  ⟨2417, 2421, 0, .none, s2417_zero_contract, 398, s2417_zero_checked⟩

def s2417_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2417_positive_checked : check 404 s2417_positive_contract = true := by decide +kernel
def s2417_positive : CertifiedContract :=
  ⟨2417, 2418, 1, (.dec 2), s2417_positive_contract, 404, s2417_positive_checked⟩

def s2418_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2418_plain_checked : check 417 s2418_plain_contract = true := by decide +kernel
def s2418_plain : CertifiedContract :=
  ⟨2418, 2419, 0, (.inc 5), s2418_plain_contract, 417, s2418_plain_checked⟩

def s2419_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2419_plain_checked : check 444 s2419_plain_contract = true := by decide +kernel
def s2419_plain : CertifiedContract :=
  ⟨2419, 2420, 0, (.inc 8), s2419_plain_contract, 444, s2419_plain_checked⟩

def s2420_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2420_plain_checked : check 121 s2420_plain_contract = true := by decide +kernel
def s2420_plain : CertifiedContract :=
  ⟨2420, 2417, 0, .none, s2420_plain_contract, 121, s2420_plain_checked⟩

def s2421_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, true, false] 0 .none⟩
theorem s2421_zero_checked : check 419 s2421_zero_contract = true := by decide +kernel
def s2421_zero : CertifiedContract :=
  ⟨2421, 2427, 0, .none, s2421_zero_contract, 419, s2421_zero_checked⟩

def s2421_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2421_positive_checked : check 422 s2421_positive_contract = true := by decide +kernel
def s2421_positive : CertifiedContract :=
  ⟨2421, 2422, 1, (.dec 8), s2421_positive_contract, 422, s2421_positive_checked⟩

def s2422_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2422_plain_checked : check 417 s2422_plain_contract = true := by decide +kernel
def s2422_plain : CertifiedContract :=
  ⟨2422, 2423, 0, (.inc 5), s2422_plain_contract, 417, s2422_plain_checked⟩

def s2423_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s2423_zero_checked : check 437 s2423_zero_contract = true := by decide +kernel
def s2423_zero : CertifiedContract :=
  ⟨2423, 2426, 0, .none, s2423_zero_contract, 437, s2423_zero_checked⟩

def s2423_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2423_positive_checked : check 440 s2423_positive_contract = true := by decide +kernel
def s2423_positive : CertifiedContract :=
  ⟨2423, 2424, 1, (.dec 8), s2423_positive_contract, 440, s2423_positive_checked⟩

def s2424_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2424_plain_checked : check 435 s2424_plain_contract = true := by decide +kernel
def s2424_plain : CertifiedContract :=
  ⟨2424, 2425, 0, (.inc 2), s2424_plain_contract, 435, s2424_plain_checked⟩

def s2425_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2425_plain_checked : check 121 s2425_plain_contract = true := by decide +kernel
def s2425_plain : CertifiedContract :=
  ⟨2425, 2423, 0, .none, s2425_plain_contract, 121, s2425_plain_checked⟩

def s2426_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2426_plain_checked : check 124 s2426_plain_contract = true := by decide +kernel
def s2426_plain : CertifiedContract :=
  ⟨2426, 2417, 0, .none, s2426_plain_contract, 124, s2426_plain_checked⟩

def s2427_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, true, false, false] 0 .none⟩
theorem s2427_zero_checked : check 407 s2427_zero_contract = true := by decide +kernel
def s2427_zero : CertifiedContract :=
  ⟨2427, 2430, 0, .none, s2427_zero_contract, 407, s2427_zero_checked⟩

def s2427_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s2427_positive_checked : check 404 s2427_positive_contract = true := by decide +kernel
def s2427_positive : CertifiedContract :=
  ⟨2427, 2428, 1, (.dec 5), s2427_positive_contract, 404, s2427_positive_checked⟩

def s2428_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s2428_plain_checked : check 417 s2428_plain_contract = true := by decide +kernel
def s2428_plain : CertifiedContract :=
  ⟨2428, 2429, 0, (.inc 0), s2428_plain_contract, 417, s2428_plain_checked⟩

def s2429_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, true, false] 0 .none⟩
theorem s2429_plain_checked : check 112 s2429_plain_contract = true := by decide +kernel
def s2429_plain : CertifiedContract :=
  ⟨2429, 2427, 0, .none, s2429_plain_contract, 112, s2429_plain_checked⟩

def s2430_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, true, true, false] 0 .none⟩
theorem s2430_zero_checked : check 371 s2430_zero_contract = true := by decide +kernel
def s2430_zero : CertifiedContract :=
  ⟨2430, 2434, 0, .none, s2430_zero_contract, 371, s2430_zero_checked⟩

def s2430_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, true, false, true, false] 1 (.dec 3)⟩
theorem s2430_positive_checked : check 377 s2430_positive_contract = true := by decide +kernel
def s2430_positive : CertifiedContract :=
  ⟨2430, 2431, 1, (.dec 3), s2430_positive_contract, 377, s2430_positive_checked⟩

def s2431_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s2431_plain_checked : check 390 s2431_plain_contract = true := by decide +kernel
def s2431_plain : CertifiedContract :=
  ⟨2431, 2432, 0, (.inc 2), s2431_plain_contract, 390, s2431_plain_checked⟩

def s2432_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2432_plain_checked : check 417 s2432_plain_contract = true := by decide +kernel
def s2432_plain : CertifiedContract :=
  ⟨2432, 2433, 0, (.inc 8), s2432_plain_contract, 417, s2432_plain_checked⟩

def s2433_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, true, false, false] 0 .none⟩
theorem s2433_plain_checked : check 112 s2433_plain_contract = true := by decide +kernel
def s2433_plain : CertifiedContract :=
  ⟨2433, 2430, 0, .none, s2433_plain_contract, 112, s2433_plain_checked⟩

def s2434_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s2434_zero_checked : check 380 s2434_zero_contract = true := by decide +kernel
def s2434_zero : CertifiedContract :=
  ⟨2434, 2437, 0, .none, s2434_zero_contract, 380, s2434_zero_checked⟩

def s2434_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s2434_positive_checked : check 377 s2434_positive_contract = true := by decide +kernel
def s2434_positive : CertifiedContract :=
  ⟨2434, 2435, 1, (.dec 8), s2434_positive_contract, 377, s2434_positive_checked⟩

def s2435_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, true, true, true, true] 0 (.inc 3)⟩
theorem s2435_plain_checked : check 393 s2435_plain_contract = true := by decide +kernel
def s2435_plain : CertifiedContract :=
  ⟨2435, 2436, 0, (.inc 3), s2435_plain_contract, 393, s2435_plain_checked⟩

def s2436_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, true, true, false] 0 .none⟩
theorem s2436_plain_checked : check 103 s2436_plain_contract = true := by decide +kernel
def s2436_plain : CertifiedContract :=
  ⟨2436, 2434, 0, .none, s2436_plain_contract, 103, s2436_plain_checked⟩

def s2437_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s2437_zero_checked : check 389 s2437_zero_contract = true := by decide +kernel
def s2437_zero : CertifiedContract :=
  ⟨2437, 2440, 0, .none, s2437_zero_contract, 389, s2437_zero_checked⟩

def s2437_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s2437_positive_checked : check 395 s2437_positive_contract = true := by decide +kernel
def s2437_positive : CertifiedContract :=
  ⟨2437, 2438, 1, (.dec 2), s2437_positive_contract, 395, s2437_positive_checked⟩

def s2438_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s2438_plain_checked : check 408 s2438_plain_contract = true := by decide +kernel
def s2438_plain : CertifiedContract :=
  ⟨2438, 2439, 0, (.inc 8), s2438_plain_contract, 408, s2438_plain_checked⟩

def s2439_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s2439_plain_checked : check 109 s2439_plain_contract = true := by decide +kernel
def s2439_plain : CertifiedContract :=
  ⟨2439, 2437, 0, .none, s2439_plain_contract, 109, s2439_plain_checked⟩

def s2440_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s2440_zero_checked : check 410 s2440_zero_contract = true := by decide +kernel
def s2440_zero : CertifiedContract :=
  ⟨2440, 2443, 0, .none, s2440_zero_contract, 410, s2440_zero_checked⟩

def s2440_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s2440_positive_checked : check 416 s2440_positive_contract = true := by decide +kernel
def s2440_positive : CertifiedContract :=
  ⟨2440, 2441, 1, (.dec 0), s2440_positive_contract, 416, s2440_positive_checked⟩

def s2441_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s2441_plain_checked : check 408 s2441_plain_contract = true := by decide +kernel
def s2441_plain : CertifiedContract :=
  ⟨2441, 2442, 0, (.inc 2), s2441_plain_contract, 408, s2441_plain_checked⟩

def s2442_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s2442_plain_checked : check 112 s2442_plain_contract = true := by decide +kernel
def s2442_plain : CertifiedContract :=
  ⟨2442, 2440, 0, .none, s2442_plain_contract, 112, s2442_plain_checked⟩

def s2443_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2443_zero_checked : check 416 s2443_zero_contract = true := by decide +kernel
def s2443_zero : CertifiedContract :=
  ⟨2443, 2447, 0, .none, s2443_zero_contract, 416, s2443_zero_checked⟩

def s2443_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2443_positive_checked : check 422 s2443_positive_contract = true := by decide +kernel
def s2443_positive : CertifiedContract :=
  ⟨2443, 2444, 1, (.dec 2), s2443_positive_contract, 422, s2443_positive_checked⟩

def s2444_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2444_plain_checked : check 435 s2444_plain_contract = true := by decide +kernel
def s2444_plain : CertifiedContract :=
  ⟨2444, 2445, 0, (.inc 5), s2444_plain_contract, 435, s2444_plain_checked⟩

def s2445_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2445_plain_checked : check 462 s2445_plain_contract = true := by decide +kernel
def s2445_plain : CertifiedContract :=
  ⟨2445, 2446, 0, (.inc 8), s2445_plain_contract, 462, s2445_plain_checked⟩

def s2446_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s2446_plain_checked : check 127 s2446_plain_contract = true := by decide +kernel
def s2446_plain : CertifiedContract :=
  ⟨2446, 2443, 0, .none, s2446_plain_contract, 127, s2446_plain_checked⟩

def s2447_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s2447_zero_checked : check 437 s2447_zero_contract = true := by decide +kernel
def s2447_zero : CertifiedContract :=
  ⟨2447, 2453, 0, .none, s2447_zero_contract, 437, s2447_zero_checked⟩

def s2447_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2447_positive_checked : check 440 s2447_positive_contract = true := by decide +kernel
def s2447_positive : CertifiedContract :=
  ⟨2447, 2448, 1, (.dec 8), s2447_positive_contract, 440, s2447_positive_checked⟩

def s2448_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2448_plain_checked : check 435 s2448_plain_contract = true := by decide +kernel
def s2448_plain : CertifiedContract :=
  ⟨2448, 2449, 0, (.inc 5), s2448_plain_contract, 435, s2448_plain_checked⟩

def s2449_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s2449_zero_checked : check 455 s2449_zero_contract = true := by decide +kernel
def s2449_zero : CertifiedContract :=
  ⟨2449, 2452, 0, .none, s2449_zero_contract, 455, s2449_zero_checked⟩

def s2449_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2449_positive_checked : check 458 s2449_positive_contract = true := by decide +kernel
def s2449_positive : CertifiedContract :=
  ⟨2449, 2450, 1, (.dec 8), s2449_positive_contract, 458, s2449_positive_checked⟩

def s2450_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2450_plain_checked : check 453 s2450_plain_contract = true := by decide +kernel
def s2450_plain : CertifiedContract :=
  ⟨2450, 2451, 0, (.inc 2), s2450_plain_contract, 453, s2450_plain_checked⟩

def s2451_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2451_plain_checked : check 127 s2451_plain_contract = true := by decide +kernel
def s2451_plain : CertifiedContract :=
  ⟨2451, 2449, 0, .none, s2451_plain_contract, 127, s2451_plain_checked⟩

def s2452_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s2452_plain_checked : check 130 s2452_plain_contract = true := by decide +kernel
def s2452_plain : CertifiedContract :=
  ⟨2452, 2443, 0, .none, s2452_plain_contract, 130, s2452_plain_checked⟩

def s2453_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s2453_zero_checked : check 425 s2453_zero_contract = true := by decide +kernel
def s2453_zero : CertifiedContract :=
  ⟨2453, 2456, 0, .none, s2453_zero_contract, 425, s2453_zero_checked⟩

def s2453_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s2453_positive_checked : check 422 s2453_positive_contract = true := by decide +kernel
def s2453_positive : CertifiedContract :=
  ⟨2453, 2454, 1, (.dec 5), s2453_positive_contract, 422, s2453_positive_checked⟩

def s2454_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s2454_plain_checked : check 435 s2454_plain_contract = true := by decide +kernel
def s2454_plain : CertifiedContract :=
  ⟨2454, 2455, 0, (.inc 0), s2454_plain_contract, 435, s2454_plain_checked⟩

def s2455_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s2455_plain_checked : check 118 s2455_plain_contract = true := by decide +kernel
def s2455_plain : CertifiedContract :=
  ⟨2455, 2453, 0, .none, s2455_plain_contract, 118, s2455_plain_checked⟩

def s2456_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s2456_zero_checked : check 389 s2456_zero_contract = true := by decide +kernel
def s2456_zero : CertifiedContract :=
  ⟨2456, 2460, 0, .none, s2456_zero_contract, 389, s2456_zero_checked⟩

def s2456_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, true, false, true, false] 1 (.dec 3)⟩
theorem s2456_positive_checked : check 395 s2456_positive_contract = true := by decide +kernel
def s2456_positive : CertifiedContract :=
  ⟨2456, 2457, 1, (.dec 3), s2456_positive_contract, 395, s2456_positive_checked⟩

def s2457_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s2457_plain_checked : check 408 s2457_plain_contract = true := by decide +kernel
def s2457_plain : CertifiedContract :=
  ⟨2457, 2458, 0, (.inc 2), s2457_plain_contract, 408, s2457_plain_checked⟩

def s2458_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2458_plain_checked : check 435 s2458_plain_contract = true := by decide +kernel
def s2458_plain : CertifiedContract :=
  ⟨2458, 2459, 0, (.inc 8), s2458_plain_contract, 435, s2458_plain_checked⟩

def s2459_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s2459_plain_checked : check 118 s2459_plain_contract = true := by decide +kernel
def s2459_plain : CertifiedContract :=
  ⟨2459, 2456, 0, .none, s2459_plain_contract, 118, s2459_plain_checked⟩

def s2460_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s2460_zero_checked : check 395 s2460_zero_contract = true := by decide +kernel
def s2460_zero : CertifiedContract :=
  ⟨2460, 2463, 0, .none, s2460_zero_contract, 395, s2460_zero_checked⟩

def s2460_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s2460_positive_checked : check 395 s2460_positive_contract = true := by decide +kernel
def s2460_positive : CertifiedContract :=
  ⟨2460, 2461, 1, (.dec 8), s2460_positive_contract, 395, s2460_positive_checked⟩

def s2461_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, true, true, true, true] 0 (.inc 3)⟩
theorem s2461_plain_checked : check 411 s2461_plain_contract = true := by decide +kernel
def s2461_plain : CertifiedContract :=
  ⟨2461, 2462, 0, (.inc 3), s2461_plain_contract, 411, s2461_plain_checked⟩

def s2462_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s2462_plain_checked : check 109 s2462_plain_contract = true := by decide +kernel
def s2462_plain : CertifiedContract :=
  ⟨2462, 2460, 0, .none, s2462_plain_contract, 109, s2462_plain_checked⟩

def s2463_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s2463_zero_checked : check 389 s2463_zero_contract = true := by decide +kernel
def s2463_zero : CertifiedContract :=
  ⟨2463, 2466, 0, .none, s2463_zero_contract, 389, s2463_zero_checked⟩

def nonterminal : Array CertifiedContract := #[
  s2414_positive,
  s2415_plain,
  s2416_plain,
  s2417_zero,
  s2417_positive,
  s2418_plain,
  s2419_plain,
  s2420_plain,
  s2421_zero,
  s2421_positive,
  s2422_plain,
  s2423_zero,
  s2423_positive,
  s2424_plain,
  s2425_plain,
  s2426_plain,
  s2427_zero,
  s2427_positive,
  s2428_plain,
  s2429_plain,
  s2430_zero,
  s2430_positive,
  s2431_plain,
  s2432_plain,
  s2433_plain,
  s2434_zero,
  s2434_positive,
  s2435_plain,
  s2436_plain,
  s2437_zero,
  s2437_positive,
  s2438_plain,
  s2439_plain,
  s2440_zero,
  s2440_positive,
  s2441_plain,
  s2442_plain,
  s2443_zero,
  s2443_positive,
  s2444_plain,
  s2445_plain,
  s2446_plain,
  s2447_zero,
  s2447_positive,
  s2448_plain,
  s2449_zero,
  s2449_positive,
  s2450_plain,
  s2451_plain,
  s2452_plain,
  s2453_zero,
  s2453_positive,
  s2454_plain,
  s2455_plain,
  s2456_zero,
  s2456_positive,
  s2457_plain,
  s2458_plain,
  s2459_plain,
  s2460_zero,
  s2460_positive,
  s2461_plain,
  s2462_plain,
  s2463_zero
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S049
