import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S009
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s0439_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, false] 0 .none⟩
theorem s0439_zero_checked : check 348 s0439_zero_contract = true := by decide +kernel
def s0439_zero : CertifiedContract :=
  ⟨439, 445, 0, .none, s0439_zero_contract, 348, s0439_zero_checked⟩

def s0439_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0439_positive_checked : check 351 s0439_positive_contract = true := by decide +kernel
def s0439_positive : CertifiedContract :=
  ⟨439, 440, 1, (.dec 8), s0439_positive_contract, 351, s0439_positive_checked⟩

def s0440_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0440_plain_checked : check 346 s0440_plain_contract = true := by decide +kernel
def s0440_plain : CertifiedContract :=
  ⟨440, 441, 0, (.inc 5), s0440_plain_contract, 346, s0440_plain_checked⟩

def s0441_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s0441_zero_checked : check 366 s0441_zero_contract = true := by decide +kernel
def s0441_zero : CertifiedContract :=
  ⟨441, 444, 0, .none, s0441_zero_contract, 366, s0441_zero_checked⟩

def s0441_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0441_positive_checked : check 369 s0441_positive_contract = true := by decide +kernel
def s0441_positive : CertifiedContract :=
  ⟨441, 442, 1, (.dec 8), s0441_positive_contract, 369, s0441_positive_checked⟩

def s0442_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0442_plain_checked : check 364 s0442_plain_contract = true := by decide +kernel
def s0442_plain : CertifiedContract :=
  ⟨442, 443, 0, (.inc 2), s0442_plain_contract, 364, s0442_plain_checked⟩

def s0443_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0443_plain_checked : check 98 s0443_plain_contract = true := by decide +kernel
def s0443_plain : CertifiedContract :=
  ⟨443, 441, 0, .none, s0443_plain_contract, 98, s0443_plain_checked⟩

def s0444_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s0444_plain_checked : check 101 s0444_plain_contract = true := by decide +kernel
def s0444_plain : CertifiedContract :=
  ⟨444, 435, 0, .none, s0444_plain_contract, 101, s0444_plain_checked⟩

def s0445_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, false] 0 .none⟩
theorem s0445_zero_checked : check 336 s0445_zero_contract = true := by decide +kernel
def s0445_zero : CertifiedContract :=
  ⟨445, 451, 0, .none, s0445_zero_contract, 336, s0445_zero_checked⟩

def s0445_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s0445_positive_checked : check 333 s0445_positive_contract = true := by decide +kernel
def s0445_positive : CertifiedContract :=
  ⟨445, 446, 1, (.dec 5), s0445_positive_contract, 333, s0445_positive_checked⟩

def s0446_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s0446_plain_checked : check 346 s0446_plain_contract = true := by decide +kernel
def s0446_plain : CertifiedContract :=
  ⟨446, 447, 0, (.inc 2), s0446_plain_contract, 346, s0446_plain_checked⟩

def s0447_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s0447_plain_checked : check 349 s0447_plain_contract = true := by decide +kernel
def s0447_plain : CertifiedContract :=
  ⟨447, 448, 0, (.inc 2), s0447_plain_contract, 349, s0447_plain_checked⟩

def s0448_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s0448_plain_checked : check 355 s0448_plain_contract = true := by decide +kernel
def s0448_plain : CertifiedContract :=
  ⟨448, 449, 0, (.inc 2), s0448_plain_contract, 355, s0448_plain_checked⟩

def s0449_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, true, true] 0 (.inc 2)⟩
theorem s0449_plain_checked : check 361 s0449_plain_contract = true := by decide +kernel
def s0449_plain : CertifiedContract :=
  ⟨449, 450, 0, (.inc 2), s0449_plain_contract, 361, s0449_plain_checked⟩

def s0450_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, false] 0 .none⟩
theorem s0450_plain_checked : check 86 s0450_plain_contract = true := by decide +kernel
def s0450_plain : CertifiedContract :=
  ⟨450, 445, 0, .none, s0450_plain_contract, 86, s0450_plain_checked⟩

def s0451_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, true, false] 0 .none⟩
theorem s0451_zero_checked : check 321 s0451_zero_contract = true := by decide +kernel
def s0451_zero : CertifiedContract :=
  ⟨451, 459, 0, .none, s0451_zero_contract, 321, s0451_zero_checked⟩

def s0451_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s0451_positive_checked : check 327 s0451_positive_contract = true := by decide +kernel
def s0451_positive : CertifiedContract :=
  ⟨451, 452, 1, (.dec 0), s0451_positive_contract, 327, s0451_positive_checked⟩

def s0452_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s0452_plain_checked : check 337 s0452_plain_contract = true := by decide +kernel
def s0452_plain : CertifiedContract :=
  ⟨452, 453, 0, (.inc 5), s0452_plain_contract, 337, s0452_plain_checked⟩

def s0453_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0453_zero_checked : check 363 s0453_zero_contract = true := by decide +kernel
def s0453_zero : CertifiedContract :=
  ⟨453, 455, 0, .none, s0453_zero_contract, 363, s0453_zero_checked⟩

def s0453_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s0453_positive_checked : check 369 s0453_positive_contract = true := by decide +kernel
def s0453_positive : CertifiedContract :=
  ⟨453, 454, 1, (.dec 8), s0453_positive_contract, 369, s0453_positive_checked⟩

def s0454_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, true] 0 .none⟩
theorem s0454_plain_checked : check 98 s0454_plain_contract = true := by decide +kernel
def s0454_plain : CertifiedContract :=
  ⟨454, 458, 0, .none, s0454_plain_contract, 98, s0454_plain_checked⟩

def s0455_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, true] 0 .none⟩
theorem s0455_zero_checked : check 375 s0455_zero_contract = true := by decide +kernel
def s0455_zero : CertifiedContract :=
  ⟨455, 458, 0, .none, s0455_zero_contract, 375, s0455_zero_checked⟩

def s0455_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0455_positive_checked : check 378 s0455_positive_contract = true := by decide +kernel
def s0455_positive : CertifiedContract :=
  ⟨455, 456, 1, (.dec 5), s0455_positive_contract, 378, s0455_positive_checked⟩

def s0456_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0456_plain_checked : check 382 s0456_plain_contract = true := by decide +kernel
def s0456_plain : CertifiedContract :=
  ⟨456, 457, 0, (.inc 8), s0456_plain_contract, 382, s0456_plain_checked⟩

def s0457_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0457_plain_checked : check 101 s0457_plain_contract = true := by decide +kernel
def s0457_plain : CertifiedContract :=
  ⟨457, 455, 0, .none, s0457_plain_contract, 101, s0457_plain_checked⟩

def s0458_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, false] 0 .none⟩
theorem s0458_plain_checked : check 92 s0458_plain_contract = true := by decide +kernel
def s0458_plain : CertifiedContract :=
  ⟨458, 451, 0, .none, s0458_plain_contract, 92, s0458_plain_checked⟩

def s0459_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s0459_zero_checked : check 321 s0459_zero_contract = true := by decide +kernel
def s0459_zero : CertifiedContract :=
  ⟨459, 462, 0, .none, s0459_zero_contract, 321, s0459_zero_checked⟩

def s0459_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s0459_positive_checked : check 324 s0459_positive_contract = true := by decide +kernel
def s0459_positive : CertifiedContract :=
  ⟨459, 460, 1, (.dec 5), s0459_positive_contract, 324, s0459_positive_checked⟩

def s0460_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s0460_plain_checked : check 337 s0460_plain_contract = true := by decide +kernel
def s0460_plain : CertifiedContract :=
  ⟨460, 461, 0, (.inc 0), s0460_plain_contract, 337, s0460_plain_checked⟩

def s0461_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, true, false] 0 .none⟩
theorem s0461_plain_checked : check 86 s0461_plain_contract = true := by decide +kernel
def s0461_plain : CertifiedContract :=
  ⟨461, 459, 0, .none, s0461_plain_contract, 86, s0461_plain_checked⟩

def s0462_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, false] 0 .none⟩
theorem s0462_zero_checked : check 318 s0462_zero_contract = true := by decide +kernel
def s0462_zero : CertifiedContract :=
  ⟨462, 466, 0, .none, s0462_zero_contract, 318, s0462_zero_checked⟩

def s0462_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0462_positive_checked : check 324 s0462_positive_contract = true := by decide +kernel
def s0462_positive : CertifiedContract :=
  ⟨462, 463, 1, (.dec 2), s0462_positive_contract, 324, s0462_positive_checked⟩

def s0463_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0463_plain_checked : check 337 s0463_plain_contract = true := by decide +kernel
def s0463_plain : CertifiedContract :=
  ⟨463, 464, 0, (.inc 5), s0463_plain_contract, 337, s0463_plain_checked⟩

def s0464_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0464_plain_checked : check 364 s0464_plain_contract = true := by decide +kernel
def s0464_plain : CertifiedContract :=
  ⟨464, 465, 0, (.inc 8), s0464_plain_contract, 364, s0464_plain_checked⟩

def s0465_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s0465_plain_checked : check 95 s0465_plain_contract = true := by decide +kernel
def s0465_plain : CertifiedContract :=
  ⟨465, 462, 0, .none, s0465_plain_contract, 95, s0465_plain_checked⟩

def s0466_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, false] 0 .none⟩
theorem s0466_zero_checked : check 339 s0466_zero_contract = true := by decide +kernel
def s0466_zero : CertifiedContract :=
  ⟨466, 472, 0, .none, s0466_zero_contract, 339, s0466_zero_checked⟩

def s0466_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0466_positive_checked : check 342 s0466_positive_contract = true := by decide +kernel
def s0466_positive : CertifiedContract :=
  ⟨466, 467, 1, (.dec 8), s0466_positive_contract, 342, s0466_positive_checked⟩

def s0467_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0467_plain_checked : check 337 s0467_plain_contract = true := by decide +kernel
def s0467_plain : CertifiedContract :=
  ⟨467, 468, 0, (.inc 5), s0467_plain_contract, 337, s0467_plain_checked⟩

def s0468_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, true, true] 0 .none⟩
theorem s0468_zero_checked : check 357 s0468_zero_contract = true := by decide +kernel
def s0468_zero : CertifiedContract :=
  ⟨468, 471, 0, .none, s0468_zero_contract, 357, s0468_zero_checked⟩

def s0468_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0468_positive_checked : check 360 s0468_positive_contract = true := by decide +kernel
def s0468_positive : CertifiedContract :=
  ⟨468, 469, 1, (.dec 8), s0468_positive_contract, 360, s0468_positive_checked⟩

def s0469_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0469_plain_checked : check 355 s0469_plain_contract = true := by decide +kernel
def s0469_plain : CertifiedContract :=
  ⟨469, 470, 0, (.inc 2), s0469_plain_contract, 355, s0469_plain_checked⟩

def s0470_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0470_plain_checked : check 95 s0470_plain_contract = true := by decide +kernel
def s0470_plain : CertifiedContract :=
  ⟨470, 468, 0, .none, s0470_plain_contract, 95, s0470_plain_checked⟩

def s0471_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s0471_plain_checked : check 98 s0471_plain_contract = true := by decide +kernel
def s0471_plain : CertifiedContract :=
  ⟨471, 462, 0, .none, s0471_plain_contract, 98, s0471_plain_checked⟩

def s0472_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s0472_zero_checked : check 324 s0472_zero_contract = true := by decide +kernel
def s0472_zero : CertifiedContract :=
  ⟨472, 478, 0, .none, s0472_zero_contract, 324, s0472_zero_checked⟩

def s0472_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s0472_positive_checked : check 324 s0472_positive_contract = true := by decide +kernel
def s0472_positive : CertifiedContract :=
  ⟨472, 473, 1, (.dec 5), s0472_positive_contract, 324, s0472_positive_checked⟩

def s0473_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s0473_plain_checked : check 337 s0473_plain_contract = true := by decide +kernel
def s0473_plain : CertifiedContract :=
  ⟨473, 474, 0, (.inc 2), s0473_plain_contract, 337, s0473_plain_checked⟩

def s0474_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s0474_plain_checked : check 340 s0474_plain_contract = true := by decide +kernel
def s0474_plain : CertifiedContract :=
  ⟨474, 475, 0, (.inc 2), s0474_plain_contract, 340, s0474_plain_checked⟩

def s0475_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s0475_plain_checked : check 346 s0475_plain_contract = true := by decide +kernel
def s0475_plain : CertifiedContract :=
  ⟨475, 476, 0, (.inc 2), s0475_plain_contract, 346, s0475_plain_checked⟩

def s0476_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s0476_plain_checked : check 352 s0476_plain_contract = true := by decide +kernel
def s0476_plain : CertifiedContract :=
  ⟨476, 477, 0, (.inc 2), s0476_plain_contract, 352, s0476_plain_checked⟩

def s0477_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, false] 0 .none⟩
theorem s0477_plain_checked : check 83 s0477_plain_contract = true := by decide +kernel
def s0477_plain : CertifiedContract :=
  ⟨477, 472, 0, .none, s0477_plain_contract, 83, s0477_plain_checked⟩

def s0478_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s0478_zero_checked : check 336 s0478_zero_contract = true := by decide +kernel
def s0478_zero : CertifiedContract :=
  ⟨478, 481, 0, .none, s0478_zero_contract, 336, s0478_zero_checked⟩

def s0478_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s0478_positive_checked : check 342 s0478_positive_contract = true := by decide +kernel
def s0478_positive : CertifiedContract :=
  ⟨478, 479, 1, (.dec 2), s0478_positive_contract, 342, s0478_positive_checked⟩

def s0479_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s0479_plain_checked : check 355 s0479_plain_contract = true := by decide +kernel
def s0479_plain : CertifiedContract :=
  ⟨479, 480, 0, (.inc 8), s0479_plain_contract, 355, s0479_plain_checked⟩

def s0480_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s0480_plain_checked : check 92 s0480_plain_contract = true := by decide +kernel
def s0480_plain : CertifiedContract :=
  ⟨480, 478, 0, .none, s0480_plain_contract, 92, s0480_plain_checked⟩

def s0481_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0481_zero_checked : check 357 s0481_zero_contract = true := by decide +kernel
def s0481_zero : CertifiedContract :=
  ⟨481, 484, 0, .none, s0481_zero_contract, 357, s0481_zero_checked⟩

def s0481_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0481_positive_checked : check 363 s0481_positive_contract = true := by decide +kernel
def s0481_positive : CertifiedContract :=
  ⟨481, 482, 1, (.dec 0), s0481_positive_contract, 363, s0481_positive_checked⟩

def s0482_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0482_plain_checked : check 355 s0482_plain_contract = true := by decide +kernel
def s0482_plain : CertifiedContract :=
  ⟨482, 483, 0, (.inc 2), s0482_plain_contract, 355, s0482_plain_checked⟩

def s0483_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s0483_plain_checked : check 95 s0483_plain_contract = true := by decide +kernel
def s0483_plain : CertifiedContract :=
  ⟨483, 481, 0, .none, s0483_plain_contract, 95, s0483_plain_checked⟩

def s0484_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0484_zero_checked : check 363 s0484_zero_contract = true := by decide +kernel
def s0484_zero : CertifiedContract :=
  ⟨484, 488, 0, .none, s0484_zero_contract, 363, s0484_zero_checked⟩

def s0484_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0484_positive_checked : check 369 s0484_positive_contract = true := by decide +kernel
def s0484_positive : CertifiedContract :=
  ⟨484, 485, 1, (.dec 2), s0484_positive_contract, 369, s0484_positive_checked⟩

def s0485_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0485_plain_checked : check 382 s0485_plain_contract = true := by decide +kernel
def s0485_plain : CertifiedContract :=
  ⟨485, 486, 0, (.inc 5), s0485_plain_contract, 382, s0485_plain_checked⟩

def s0486_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0486_plain_checked : check 409 s0486_plain_contract = true := by decide +kernel
def s0486_plain : CertifiedContract :=
  ⟨486, 487, 0, (.inc 8), s0486_plain_contract, 409, s0486_plain_checked⟩

def s0487_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0487_plain_checked : check 110 s0487_plain_contract = true := by decide +kernel
def s0487_plain : CertifiedContract :=
  ⟨487, 484, 0, .none, s0487_plain_contract, 110, s0487_plain_checked⟩

def s0488_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s0488_zero_checked : check 384 s0488_zero_contract = true := by decide +kernel
def s0488_zero : CertifiedContract :=
  ⟨488, 494, 0, .none, s0488_zero_contract, 384, s0488_zero_checked⟩

end PA211.UserCandidate.RuntimeShards.S009
