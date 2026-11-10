import PA213.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S009
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s0439_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, false] 0 .none⟩
theorem s0439_zero_checked : check 347 s0439_zero_contract = true := by decide +kernel
def s0439_zero : CertifiedContract :=
  ⟨439, 445, 0, .none, s0439_zero_contract, 347, s0439_zero_checked⟩

def s0439_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0439_positive_checked : check 350 s0439_positive_contract = true := by decide +kernel
def s0439_positive : CertifiedContract :=
  ⟨439, 440, 1, (.dec 8), s0439_positive_contract, 350, s0439_positive_checked⟩

def s0440_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0440_plain_checked : check 345 s0440_plain_contract = true := by decide +kernel
def s0440_plain : CertifiedContract :=
  ⟨440, 441, 0, (.inc 5), s0440_plain_contract, 345, s0440_plain_checked⟩

def s0441_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s0441_zero_checked : check 365 s0441_zero_contract = true := by decide +kernel
def s0441_zero : CertifiedContract :=
  ⟨441, 444, 0, .none, s0441_zero_contract, 365, s0441_zero_checked⟩

def s0441_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0441_positive_checked : check 368 s0441_positive_contract = true := by decide +kernel
def s0441_positive : CertifiedContract :=
  ⟨441, 442, 1, (.dec 8), s0441_positive_contract, 368, s0441_positive_checked⟩

def s0442_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0442_plain_checked : check 363 s0442_plain_contract = true := by decide +kernel
def s0442_plain : CertifiedContract :=
  ⟨442, 443, 0, (.inc 2), s0442_plain_contract, 363, s0442_plain_checked⟩

def s0443_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s0443_plain_checked : check 97 s0443_plain_contract = true := by decide +kernel
def s0443_plain : CertifiedContract :=
  ⟨443, 441, 0, .none, s0443_plain_contract, 97, s0443_plain_checked⟩

def s0444_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, false, false, false] 0 .none⟩
theorem s0444_plain_checked : check 100 s0444_plain_contract = true := by decide +kernel
def s0444_plain : CertifiedContract :=
  ⟨444, 435, 0, .none, s0444_plain_contract, 100, s0444_plain_checked⟩

def s0445_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, false] 0 .none⟩
theorem s0445_zero_checked : check 335 s0445_zero_contract = true := by decide +kernel
def s0445_zero : CertifiedContract :=
  ⟨445, 451, 0, .none, s0445_zero_contract, 335, s0445_zero_checked⟩

def s0445_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s0445_positive_checked : check 332 s0445_positive_contract = true := by decide +kernel
def s0445_positive : CertifiedContract :=
  ⟨445, 446, 1, (.dec 5), s0445_positive_contract, 332, s0445_positive_checked⟩

def s0446_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s0446_plain_checked : check 345 s0446_plain_contract = true := by decide +kernel
def s0446_plain : CertifiedContract :=
  ⟨446, 447, 0, (.inc 2), s0446_plain_contract, 345, s0446_plain_checked⟩

def s0447_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s0447_plain_checked : check 348 s0447_plain_contract = true := by decide +kernel
def s0447_plain : CertifiedContract :=
  ⟨447, 448, 0, (.inc 2), s0447_plain_contract, 348, s0447_plain_checked⟩

def s0448_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s0448_plain_checked : check 345 s0448_plain_contract = true := by decide +kernel
def s0448_plain : CertifiedContract :=
  ⟨448, 449, 0, (.inc 2), s0448_plain_contract, 345, s0448_plain_checked⟩

def s0449_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, true, true] 0 (.inc 2)⟩
theorem s0449_plain_checked : check 351 s0449_plain_contract = true := by decide +kernel
def s0449_plain : CertifiedContract :=
  ⟨449, 450, 0, (.inc 2), s0449_plain_contract, 351, s0449_plain_checked⟩

def s0450_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, false, true, true, true, false] 0 .none⟩
theorem s0450_plain_checked : check 85 s0450_plain_contract = true := by decide +kernel
def s0450_plain : CertifiedContract :=
  ⟨450, 445, 0, .none, s0450_plain_contract, 85, s0450_plain_checked⟩

def s0451_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, true, false] 0 .none⟩
theorem s0451_zero_checked : check 320 s0451_zero_contract = true := by decide +kernel
def s0451_zero : CertifiedContract :=
  ⟨451, 459, 0, .none, s0451_zero_contract, 320, s0451_zero_checked⟩

def s0451_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s0451_positive_checked : check 326 s0451_positive_contract = true := by decide +kernel
def s0451_positive : CertifiedContract :=
  ⟨451, 452, 1, (.dec 0), s0451_positive_contract, 326, s0451_positive_checked⟩

def s0452_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s0452_plain_checked : check 336 s0452_plain_contract = true := by decide +kernel
def s0452_plain : CertifiedContract :=
  ⟨452, 453, 0, (.inc 5), s0452_plain_contract, 336, s0452_plain_checked⟩

def s0453_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0453_zero_checked : check 362 s0453_zero_contract = true := by decide +kernel
def s0453_zero : CertifiedContract :=
  ⟨453, 455, 0, .none, s0453_zero_contract, 362, s0453_zero_checked⟩

def s0453_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s0453_positive_checked : check 368 s0453_positive_contract = true := by decide +kernel
def s0453_positive : CertifiedContract :=
  ⟨453, 454, 1, (.dec 8), s0453_positive_contract, 368, s0453_positive_checked⟩

def s0454_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, true] 0 .none⟩
theorem s0454_plain_checked : check 97 s0454_plain_contract = true := by decide +kernel
def s0454_plain : CertifiedContract :=
  ⟨454, 458, 0, .none, s0454_plain_contract, 97, s0454_plain_checked⟩

def s0455_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, true] 0 .none⟩
theorem s0455_zero_checked : check 374 s0455_zero_contract = true := by decide +kernel
def s0455_zero : CertifiedContract :=
  ⟨455, 458, 0, .none, s0455_zero_contract, 374, s0455_zero_checked⟩

def s0455_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s0455_positive_checked : check 377 s0455_positive_contract = true := by decide +kernel
def s0455_positive : CertifiedContract :=
  ⟨455, 456, 1, (.dec 5), s0455_positive_contract, 377, s0455_positive_checked⟩

def s0456_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s0456_plain_checked : check 381 s0456_plain_contract = true := by decide +kernel
def s0456_plain : CertifiedContract :=
  ⟨456, 457, 0, (.inc 8), s0456_plain_contract, 381, s0456_plain_checked⟩

def s0457_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0457_plain_checked : check 100 s0457_plain_contract = true := by decide +kernel
def s0457_plain : CertifiedContract :=
  ⟨457, 455, 0, .none, s0457_plain_contract, 100, s0457_plain_checked⟩

def s0458_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, false, false] 0 .none⟩
theorem s0458_plain_checked : check 91 s0458_plain_contract = true := by decide +kernel
def s0458_plain : CertifiedContract :=
  ⟨458, 451, 0, .none, s0458_plain_contract, 91, s0458_plain_checked⟩

def s0459_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s0459_zero_checked : check 320 s0459_zero_contract = true := by decide +kernel
def s0459_zero : CertifiedContract :=
  ⟨459, 462, 0, .none, s0459_zero_contract, 320, s0459_zero_checked⟩

def s0459_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s0459_positive_checked : check 323 s0459_positive_contract = true := by decide +kernel
def s0459_positive : CertifiedContract :=
  ⟨459, 460, 1, (.dec 5), s0459_positive_contract, 323, s0459_positive_checked⟩

def s0460_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s0460_plain_checked : check 336 s0460_plain_contract = true := by decide +kernel
def s0460_plain : CertifiedContract :=
  ⟨460, 461, 0, (.inc 0), s0460_plain_contract, 336, s0460_plain_checked⟩

def s0461_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, false, true, false] 0 .none⟩
theorem s0461_plain_checked : check 85 s0461_plain_contract = true := by decide +kernel
def s0461_plain : CertifiedContract :=
  ⟨461, 459, 0, .none, s0461_plain_contract, 85, s0461_plain_checked⟩

def s0462_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, false] 0 .none⟩
theorem s0462_zero_checked : check 317 s0462_zero_contract = true := by decide +kernel
def s0462_zero : CertifiedContract :=
  ⟨462, 466, 0, .none, s0462_zero_contract, 317, s0462_zero_checked⟩

def s0462_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0462_positive_checked : check 323 s0462_positive_contract = true := by decide +kernel
def s0462_positive : CertifiedContract :=
  ⟨462, 463, 1, (.dec 2), s0462_positive_contract, 323, s0462_positive_checked⟩

def s0463_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0463_plain_checked : check 336 s0463_plain_contract = true := by decide +kernel
def s0463_plain : CertifiedContract :=
  ⟨463, 464, 0, (.inc 5), s0463_plain_contract, 336, s0463_plain_checked⟩

def s0464_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0464_plain_checked : check 363 s0464_plain_contract = true := by decide +kernel
def s0464_plain : CertifiedContract :=
  ⟨464, 465, 0, (.inc 8), s0464_plain_contract, 363, s0464_plain_checked⟩

def s0465_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s0465_plain_checked : check 94 s0465_plain_contract = true := by decide +kernel
def s0465_plain : CertifiedContract :=
  ⟨465, 462, 0, .none, s0465_plain_contract, 94, s0465_plain_checked⟩

def s0466_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, false] 0 .none⟩
theorem s0466_zero_checked : check 338 s0466_zero_contract = true := by decide +kernel
def s0466_zero : CertifiedContract :=
  ⟨466, 472, 0, .none, s0466_zero_contract, 338, s0466_zero_checked⟩

def s0466_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s0466_positive_checked : check 341 s0466_positive_contract = true := by decide +kernel
def s0466_positive : CertifiedContract :=
  ⟨466, 467, 1, (.dec 8), s0466_positive_contract, 341, s0466_positive_checked⟩

def s0467_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s0467_plain_checked : check 336 s0467_plain_contract = true := by decide +kernel
def s0467_plain : CertifiedContract :=
  ⟨467, 468, 0, (.inc 5), s0467_plain_contract, 336, s0467_plain_checked⟩

def s0468_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, true, true] 0 .none⟩
theorem s0468_zero_checked : check 356 s0468_zero_contract = true := by decide +kernel
def s0468_zero : CertifiedContract :=
  ⟨468, 471, 0, .none, s0468_zero_contract, 356, s0468_zero_checked⟩

def s0468_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s0468_positive_checked : check 359 s0468_positive_contract = true := by decide +kernel
def s0468_positive : CertifiedContract :=
  ⟨468, 469, 1, (.dec 8), s0468_positive_contract, 359, s0468_positive_checked⟩

def s0469_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s0469_plain_checked : check 354 s0469_plain_contract = true := by decide +kernel
def s0469_plain : CertifiedContract :=
  ⟨469, 470, 0, (.inc 2), s0469_plain_contract, 354, s0469_plain_checked⟩

def s0470_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s0470_plain_checked : check 94 s0470_plain_contract = true := by decide +kernel
def s0470_plain : CertifiedContract :=
  ⟨470, 468, 0, .none, s0470_plain_contract, 94, s0470_plain_checked⟩

def s0471_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s0471_plain_checked : check 97 s0471_plain_contract = true := by decide +kernel
def s0471_plain : CertifiedContract :=
  ⟨471, 462, 0, .none, s0471_plain_contract, 97, s0471_plain_checked⟩

def s0472_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s0472_zero_checked : check 323 s0472_zero_contract = true := by decide +kernel
def s0472_zero : CertifiedContract :=
  ⟨472, 478, 0, .none, s0472_zero_contract, 323, s0472_zero_checked⟩

def s0472_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s0472_positive_checked : check 323 s0472_positive_contract = true := by decide +kernel
def s0472_positive : CertifiedContract :=
  ⟨472, 473, 1, (.dec 5), s0472_positive_contract, 323, s0472_positive_checked⟩

def s0473_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s0473_plain_checked : check 336 s0473_plain_contract = true := by decide +kernel
def s0473_plain : CertifiedContract :=
  ⟨473, 474, 0, (.inc 2), s0473_plain_contract, 336, s0473_plain_checked⟩

def s0474_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s0474_plain_checked : check 339 s0474_plain_contract = true := by decide +kernel
def s0474_plain : CertifiedContract :=
  ⟨474, 475, 0, (.inc 2), s0474_plain_contract, 339, s0474_plain_checked⟩

def s0475_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s0475_plain_checked : check 336 s0475_plain_contract = true := by decide +kernel
def s0475_plain : CertifiedContract :=
  ⟨475, 476, 0, (.inc 2), s0475_plain_contract, 336, s0475_plain_checked⟩

def s0476_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s0476_plain_checked : check 342 s0476_plain_contract = true := by decide +kernel
def s0476_plain : CertifiedContract :=
  ⟨476, 477, 0, (.inc 2), s0476_plain_contract, 342, s0476_plain_checked⟩

def s0477_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, false, true, true, false] 0 .none⟩
theorem s0477_plain_checked : check 82 s0477_plain_contract = true := by decide +kernel
def s0477_plain : CertifiedContract :=
  ⟨477, 472, 0, .none, s0477_plain_contract, 82, s0477_plain_checked⟩

def s0478_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s0478_zero_checked : check 335 s0478_zero_contract = true := by decide +kernel
def s0478_zero : CertifiedContract :=
  ⟨478, 481, 0, .none, s0478_zero_contract, 335, s0478_zero_checked⟩

def s0478_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s0478_positive_checked : check 341 s0478_positive_contract = true := by decide +kernel
def s0478_positive : CertifiedContract :=
  ⟨478, 479, 1, (.dec 2), s0478_positive_contract, 341, s0478_positive_checked⟩

def s0479_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s0479_plain_checked : check 354 s0479_plain_contract = true := by decide +kernel
def s0479_plain : CertifiedContract :=
  ⟨479, 480, 0, (.inc 8), s0479_plain_contract, 354, s0479_plain_checked⟩

def s0480_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s0480_plain_checked : check 91 s0480_plain_contract = true := by decide +kernel
def s0480_plain : CertifiedContract :=
  ⟨480, 478, 0, .none, s0480_plain_contract, 91, s0480_plain_checked⟩

def s0481_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0481_zero_checked : check 356 s0481_zero_contract = true := by decide +kernel
def s0481_zero : CertifiedContract :=
  ⟨481, 484, 0, .none, s0481_zero_contract, 356, s0481_zero_checked⟩

def s0481_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s0481_positive_checked : check 362 s0481_positive_contract = true := by decide +kernel
def s0481_positive : CertifiedContract :=
  ⟨481, 482, 1, (.dec 0), s0481_positive_contract, 362, s0481_positive_checked⟩

def s0482_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s0482_plain_checked : check 354 s0482_plain_contract = true := by decide +kernel
def s0482_plain : CertifiedContract :=
  ⟨482, 483, 0, (.inc 2), s0482_plain_contract, 354, s0482_plain_checked⟩

def s0483_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s0483_plain_checked : check 94 s0483_plain_contract = true := by decide +kernel
def s0483_plain : CertifiedContract :=
  ⟨483, 481, 0, .none, s0483_plain_contract, 94, s0483_plain_checked⟩

def s0484_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s0484_zero_checked : check 362 s0484_zero_contract = true := by decide +kernel
def s0484_zero : CertifiedContract :=
  ⟨484, 488, 0, .none, s0484_zero_contract, 362, s0484_zero_checked⟩

def s0484_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s0484_positive_checked : check 368 s0484_positive_contract = true := by decide +kernel
def s0484_positive : CertifiedContract :=
  ⟨484, 485, 1, (.dec 2), s0484_positive_contract, 368, s0484_positive_checked⟩

def s0485_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s0485_plain_checked : check 381 s0485_plain_contract = true := by decide +kernel
def s0485_plain : CertifiedContract :=
  ⟨485, 486, 0, (.inc 5), s0485_plain_contract, 381, s0485_plain_checked⟩

def s0486_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s0486_plain_checked : check 408 s0486_plain_contract = true := by decide +kernel
def s0486_plain : CertifiedContract :=
  ⟨486, 487, 0, (.inc 8), s0486_plain_contract, 408, s0486_plain_checked⟩

def s0487_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s0487_plain_checked : check 109 s0487_plain_contract = true := by decide +kernel
def s0487_plain : CertifiedContract :=
  ⟨487, 484, 0, .none, s0487_plain_contract, 109, s0487_plain_checked⟩

def s0488_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, false, true, true, true, true, true, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s0488_zero_checked : check 383 s0488_zero_contract = true := by decide +kernel
def s0488_zero : CertifiedContract :=
  ⟨488, 494, 0, .none, s0488_zero_contract, 383, s0488_zero_checked⟩

def nonterminal : Array CertifiedContract := #[
  s0439_zero,
  s0439_positive,
  s0440_plain,
  s0441_zero,
  s0441_positive,
  s0442_plain,
  s0443_plain,
  s0444_plain,
  s0445_zero,
  s0445_positive,
  s0446_plain,
  s0447_plain,
  s0448_plain,
  s0449_plain,
  s0450_plain,
  s0451_zero,
  s0451_positive,
  s0452_plain,
  s0453_zero,
  s0453_positive,
  s0454_plain,
  s0455_zero,
  s0455_positive,
  s0456_plain,
  s0457_plain,
  s0458_plain,
  s0459_zero,
  s0459_positive,
  s0460_plain,
  s0461_plain,
  s0462_zero,
  s0462_positive,
  s0463_plain,
  s0464_plain,
  s0465_plain,
  s0466_zero,
  s0466_positive,
  s0467_plain,
  s0468_zero,
  s0468_positive,
  s0469_plain,
  s0470_plain,
  s0471_plain,
  s0472_zero,
  s0472_positive,
  s0473_plain,
  s0474_plain,
  s0475_plain,
  s0476_plain,
  s0477_plain,
  s0478_zero,
  s0478_positive,
  s0479_plain,
  s0480_plain,
  s0481_zero,
  s0481_positive,
  s0482_plain,
  s0483_plain,
  s0484_zero,
  s0484_positive,
  s0485_plain,
  s0486_plain,
  s0487_plain,
  s0488_zero
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S009
