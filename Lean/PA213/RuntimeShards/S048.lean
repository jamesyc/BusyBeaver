module

public import PA213.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S048
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s2365_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, false, false] 0 .none⟩
theorem s2365_zero_checked : check 401 s2365_zero_contract = true := by decide +kernel
def s2365_zero : CertifiedContract :=
  ⟨2365, 2368, 0, .none, s2365_zero_contract, 401, s2365_zero_checked⟩

def s2365_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, true, true, false] 1 (.dec 5)⟩
theorem s2365_positive_checked : check 404 s2365_positive_contract = true := by decide +kernel
def s2365_positive : CertifiedContract :=
  ⟨2365, 2366, 1, (.dec 5), s2365_positive_contract, 404, s2365_positive_checked⟩

def s2366_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, true, true, true] 0 (.inc 0)⟩
theorem s2366_plain_checked : check 417 s2366_plain_contract = true := by decide +kernel
def s2366_plain : CertifiedContract :=
  ⟨2366, 2367, 0, (.inc 0), s2366_plain_contract, 417, s2366_plain_checked⟩

def s2367_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, false, true, false] 0 .none⟩
theorem s2367_plain_checked : check 112 s2367_plain_contract = true := by decide +kernel
def s2367_plain : CertifiedContract :=
  ⟨2367, 2365, 0, .none, s2367_plain_contract, 112, s2367_plain_checked⟩

def s2368_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, true, false] 0 .none⟩
theorem s2368_zero_checked : check 398 s2368_zero_contract = true := by decide +kernel
def s2368_zero : CertifiedContract :=
  ⟨2368, 2372, 0, .none, s2368_zero_contract, 398, s2368_zero_checked⟩

def s2368_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2368_positive_checked : check 404 s2368_positive_contract = true := by decide +kernel
def s2368_positive : CertifiedContract :=
  ⟨2368, 2369, 1, (.dec 2), s2368_positive_contract, 404, s2368_positive_checked⟩

def s2369_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2369_plain_checked : check 417 s2369_plain_contract = true := by decide +kernel
def s2369_plain : CertifiedContract :=
  ⟨2369, 2370, 0, (.inc 5), s2369_plain_contract, 417, s2369_plain_checked⟩

def s2370_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2370_plain_checked : check 444 s2370_plain_contract = true := by decide +kernel
def s2370_plain : CertifiedContract :=
  ⟨2370, 2371, 0, (.inc 8), s2370_plain_contract, 444, s2370_plain_checked⟩

def s2371_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, false, false] 0 .none⟩
theorem s2371_plain_checked : check 121 s2371_plain_contract = true := by decide +kernel
def s2371_plain : CertifiedContract :=
  ⟨2371, 2368, 0, .none, s2371_plain_contract, 121, s2371_plain_checked⟩

def s2372_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s2372_zero_checked : check 419 s2372_zero_contract = true := by decide +kernel
def s2372_zero : CertifiedContract :=
  ⟨2372, 2378, 0, .none, s2372_zero_contract, 419, s2372_zero_checked⟩

def s2372_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2372_positive_checked : check 422 s2372_positive_contract = true := by decide +kernel
def s2372_positive : CertifiedContract :=
  ⟨2372, 2373, 1, (.dec 8), s2372_positive_contract, 422, s2372_positive_checked⟩

def s2373_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2373_plain_checked : check 417 s2373_plain_contract = true := by decide +kernel
def s2373_plain : CertifiedContract :=
  ⟨2373, 2374, 0, (.inc 5), s2373_plain_contract, 417, s2373_plain_checked⟩

def s2374_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, true, true, true] 0 .none⟩
theorem s2374_zero_checked : check 437 s2374_zero_contract = true := by decide +kernel
def s2374_zero : CertifiedContract :=
  ⟨2374, 2377, 0, .none, s2374_zero_contract, 437, s2374_zero_checked⟩

def s2374_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2374_positive_checked : check 440 s2374_positive_contract = true := by decide +kernel
def s2374_positive : CertifiedContract :=
  ⟨2374, 2375, 1, (.dec 8), s2374_positive_contract, 440, s2374_positive_checked⟩

def s2375_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2375_plain_checked : check 435 s2375_plain_contract = true := by decide +kernel
def s2375_plain : CertifiedContract :=
  ⟨2375, 2376, 0, (.inc 2), s2375_plain_contract, 435, s2375_plain_checked⟩

def s2376_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s2376_plain_checked : check 121 s2376_plain_contract = true := by decide +kernel
def s2376_plain : CertifiedContract :=
  ⟨2376, 2374, 0, .none, s2376_plain_contract, 121, s2376_plain_checked⟩

def s2377_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, false, false, false] 0 .none⟩
theorem s2377_plain_checked : check 124 s2377_plain_contract = true := by decide +kernel
def s2377_plain : CertifiedContract :=
  ⟨2377, 2368, 0, .none, s2377_plain_contract, 124, s2377_plain_checked⟩

def s2378_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s2378_zero_checked : check 404 s2378_zero_contract = true := by decide +kernel
def s2378_zero : CertifiedContract :=
  ⟨2378, 2384, 0, .none, s2378_zero_contract, 404, s2378_zero_checked⟩

def s2378_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s2378_positive_checked : check 404 s2378_positive_contract = true := by decide +kernel
def s2378_positive : CertifiedContract :=
  ⟨2378, 2379, 1, (.dec 5), s2378_positive_contract, 404, s2378_positive_checked⟩

def s2379_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s2379_plain_checked : check 417 s2379_plain_contract = true := by decide +kernel
def s2379_plain : CertifiedContract :=
  ⟨2379, 2380, 0, (.inc 2), s2379_plain_contract, 417, s2379_plain_checked⟩

def s2380_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s2380_plain_checked : check 420 s2380_plain_contract = true := by decide +kernel
def s2380_plain : CertifiedContract :=
  ⟨2380, 2381, 0, (.inc 2), s2380_plain_contract, 420, s2380_plain_checked⟩

def s2381_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s2381_plain_checked : check 417 s2381_plain_contract = true := by decide +kernel
def s2381_plain : CertifiedContract :=
  ⟨2381, 2382, 0, (.inc 2), s2381_plain_contract, 417, s2381_plain_checked⟩

def s2382_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, true, true, true] 0 (.inc 2)⟩
theorem s2382_plain_checked : check 423 s2382_plain_contract = true := by decide +kernel
def s2382_plain : CertifiedContract :=
  ⟨2382, 2383, 0, (.inc 2), s2382_plain_contract, 423, s2382_plain_checked⟩

def s2383_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, true, false] 0 .none⟩
theorem s2383_plain_checked : check 109 s2383_plain_contract = true := by decide +kernel
def s2383_plain : CertifiedContract :=
  ⟨2383, 2378, 0, .none, s2383_plain_contract, 109, s2383_plain_checked⟩

def s2384_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, true, false] 0 .none⟩
theorem s2384_zero_checked : check 410 s2384_zero_contract = true := by decide +kernel
def s2384_zero : CertifiedContract :=
  ⟨2384, 2392, 0, .none, s2384_zero_contract, 410, s2384_zero_checked⟩

def s2384_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, false, true, false] 1 (.dec 0)⟩
theorem s2384_positive_checked : check 416 s2384_positive_contract = true := by decide +kernel
def s2384_positive : CertifiedContract :=
  ⟨2384, 2385, 1, (.dec 0), s2384_positive_contract, 416, s2384_positive_checked⟩

def s2385_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s2385_plain_checked : check 426 s2385_plain_contract = true := by decide +kernel
def s2385_plain : CertifiedContract :=
  ⟨2385, 2386, 0, (.inc 5), s2385_plain_contract, 426, s2385_plain_checked⟩

def s2386_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s2386_zero_checked : check 452 s2386_zero_contract = true := by decide +kernel
def s2386_zero : CertifiedContract :=
  ⟨2386, 2388, 0, .none, s2386_zero_contract, 452, s2386_zero_checked⟩

def s2386_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s2386_positive_checked : check 458 s2386_positive_contract = true := by decide +kernel
def s2386_positive : CertifiedContract :=
  ⟨2386, 2387, 1, (.dec 8), s2386_positive_contract, 458, s2386_positive_checked⟩

def s2387_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, false, true, true, true] 0 .none⟩
theorem s2387_plain_checked : check 127 s2387_plain_contract = true := by decide +kernel
def s2387_plain : CertifiedContract :=
  ⟨2387, 2391, 0, .none, s2387_plain_contract, 127, s2387_plain_checked⟩

def s2388_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, false, true, true, true] 0 .none⟩
theorem s2388_zero_checked : check 464 s2388_zero_contract = true := by decide +kernel
def s2388_zero : CertifiedContract :=
  ⟨2388, 2391, 0, .none, s2388_zero_contract, 464, s2388_zero_checked⟩

def s2388_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s2388_positive_checked : check 467 s2388_positive_contract = true := by decide +kernel
def s2388_positive : CertifiedContract :=
  ⟨2388, 2389, 1, (.dec 5), s2388_positive_contract, 467, s2388_positive_checked⟩

def s2389_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2389_plain_checked : check 471 s2389_plain_contract = true := by decide +kernel
def s2389_plain : CertifiedContract :=
  ⟨2389, 2390, 0, (.inc 8), s2389_plain_contract, 471, s2389_plain_checked⟩

def s2390_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s2390_plain_checked : check 130 s2390_plain_contract = true := by decide +kernel
def s2390_plain : CertifiedContract :=
  ⟨2390, 2388, 0, .none, s2390_plain_contract, 130, s2390_plain_checked⟩

def s2391_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, false, false] 0 .none⟩
theorem s2391_plain_checked : check 121 s2391_plain_contract = true := by decide +kernel
def s2391_plain : CertifiedContract :=
  ⟨2391, 2384, 0, .none, s2391_plain_contract, 121, s2391_plain_checked⟩

def s2392_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s2392_zero_checked : check 410 s2392_zero_contract = true := by decide +kernel
def s2392_zero : CertifiedContract :=
  ⟨2392, 2395, 0, .none, s2392_zero_contract, 410, s2392_zero_checked⟩

def s2392_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, true, true, false] 1 (.dec 5)⟩
theorem s2392_positive_checked : check 413 s2392_positive_contract = true := by decide +kernel
def s2392_positive : CertifiedContract :=
  ⟨2392, 2393, 1, (.dec 5), s2392_positive_contract, 413, s2392_positive_checked⟩

def s2393_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, true, true, true] 0 (.inc 0)⟩
theorem s2393_plain_checked : check 426 s2393_plain_contract = true := by decide +kernel
def s2393_plain : CertifiedContract :=
  ⟨2393, 2394, 0, (.inc 0), s2393_plain_contract, 426, s2393_plain_checked⟩

def s2394_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, false, true, false] 0 .none⟩
theorem s2394_plain_checked : check 115 s2394_plain_contract = true := by decide +kernel
def s2394_plain : CertifiedContract :=
  ⟨2394, 2392, 0, .none, s2394_plain_contract, 115, s2394_plain_checked⟩

def s2395_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s2395_zero_checked : check 407 s2395_zero_contract = true := by decide +kernel
def s2395_zero : CertifiedContract :=
  ⟨2395, 2399, 0, .none, s2395_zero_contract, 407, s2395_zero_checked⟩

def s2395_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2395_positive_checked : check 413 s2395_positive_contract = true := by decide +kernel
def s2395_positive : CertifiedContract :=
  ⟨2395, 2396, 1, (.dec 2), s2395_positive_contract, 413, s2395_positive_checked⟩

def s2396_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s2396_plain_checked : check 426 s2396_plain_contract = true := by decide +kernel
def s2396_plain : CertifiedContract :=
  ⟨2396, 2397, 0, (.inc 5), s2396_plain_contract, 426, s2396_plain_checked⟩

def s2397_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s2397_plain_checked : check 453 s2397_plain_contract = true := by decide +kernel
def s2397_plain : CertifiedContract :=
  ⟨2397, 2398, 0, (.inc 8), s2397_plain_contract, 453, s2397_plain_checked⟩

def s2398_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s2398_plain_checked : check 124 s2398_plain_contract = true := by decide +kernel
def s2398_plain : CertifiedContract :=
  ⟨2398, 2395, 0, .none, s2398_plain_contract, 124, s2398_plain_checked⟩

def s2399_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s2399_zero_checked : check 428 s2399_zero_contract = true := by decide +kernel
def s2399_zero : CertifiedContract :=
  ⟨2399, 2405, 0, .none, s2399_zero_contract, 428, s2399_zero_checked⟩

def s2399_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s2399_positive_checked : check 431 s2399_positive_contract = true := by decide +kernel
def s2399_positive : CertifiedContract :=
  ⟨2399, 2400, 1, (.dec 8), s2399_positive_contract, 431, s2399_positive_checked⟩

def s2400_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s2400_plain_checked : check 426 s2400_plain_contract = true := by decide +kernel
def s2400_plain : CertifiedContract :=
  ⟨2400, 2401, 0, (.inc 5), s2400_plain_contract, 426, s2400_plain_checked⟩

def s2401_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s2401_zero_checked : check 446 s2401_zero_contract = true := by decide +kernel
def s2401_zero : CertifiedContract :=
  ⟨2401, 2404, 0, .none, s2401_zero_contract, 446, s2401_zero_checked⟩

def s2401_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s2401_positive_checked : check 449 s2401_positive_contract = true := by decide +kernel
def s2401_positive : CertifiedContract :=
  ⟨2401, 2402, 1, (.dec 8), s2401_positive_contract, 449, s2401_positive_checked⟩

def s2402_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s2402_plain_checked : check 444 s2402_plain_contract = true := by decide +kernel
def s2402_plain : CertifiedContract :=
  ⟨2402, 2403, 0, (.inc 2), s2402_plain_contract, 444, s2402_plain_checked⟩

def s2403_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s2403_plain_checked : check 124 s2403_plain_contract = true := by decide +kernel
def s2403_plain : CertifiedContract :=
  ⟨2403, 2401, 0, .none, s2403_plain_contract, 124, s2403_plain_checked⟩

def s2404_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, false, false, false] 0 .none⟩
theorem s2404_plain_checked : check 127 s2404_plain_contract = true := by decide +kernel
def s2404_plain : CertifiedContract :=
  ⟨2404, 2395, 0, .none, s2404_plain_contract, 127, s2404_plain_checked⟩

def s2405_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s2405_zero_checked : check 416 s2405_zero_contract = true := by decide +kernel
def s2405_zero : CertifiedContract :=
  ⟨2405, 2411, 0, .none, s2405_zero_contract, 416, s2405_zero_checked⟩

def s2405_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s2405_positive_checked : check 413 s2405_positive_contract = true := by decide +kernel
def s2405_positive : CertifiedContract :=
  ⟨2405, 2406, 1, (.dec 5), s2405_positive_contract, 413, s2405_positive_checked⟩

def s2406_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s2406_plain_checked : check 426 s2406_plain_contract = true := by decide +kernel
def s2406_plain : CertifiedContract :=
  ⟨2406, 2407, 0, (.inc 2), s2406_plain_contract, 426, s2406_plain_checked⟩

def s2407_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s2407_plain_checked : check 429 s2407_plain_contract = true := by decide +kernel
def s2407_plain : CertifiedContract :=
  ⟨2407, 2408, 0, (.inc 2), s2407_plain_contract, 429, s2407_plain_checked⟩

def s2408_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s2408_plain_checked : check 426 s2408_plain_contract = true := by decide +kernel
def s2408_plain : CertifiedContract :=
  ⟨2408, 2409, 0, (.inc 2), s2408_plain_contract, 426, s2408_plain_checked⟩

def s2409_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, true, true, true] 0 (.inc 2)⟩
theorem s2409_plain_checked : check 432 s2409_plain_contract = true := by decide +kernel
def s2409_plain : CertifiedContract :=
  ⟨2409, 2410, 0, (.inc 2), s2409_plain_contract, 432, s2409_plain_checked⟩

def s2410_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, false, true, true, true, false] 0 .none⟩
theorem s2410_plain_checked : check 112 s2410_plain_contract = true := by decide +kernel
def s2410_plain : CertifiedContract :=
  ⟨2410, 2405, 0, .none, s2410_plain_contract, 112, s2410_plain_checked⟩

def s2411_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s2411_zero_checked : check 371 s2411_zero_contract = true := by decide +kernel
def s2411_zero : CertifiedContract :=
  ⟨2411, 2414, 0, .none, s2411_zero_contract, 371, s2411_zero_checked⟩

def s2411_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2411_positive_checked : check 377 s2411_positive_contract = true := by decide +kernel
def s2411_positive : CertifiedContract :=
  ⟨2411, 2412, 1, (.dec 2), s2411_positive_contract, 377, s2411_positive_checked⟩

def s2412_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s2412_plain_checked : check 390 s2412_plain_contract = true := by decide +kernel
def s2412_plain : CertifiedContract :=
  ⟨2412, 2413, 0, (.inc 8), s2412_plain_contract, 390, s2412_plain_checked⟩

def s2413_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s2413_plain_checked : check 103 s2413_plain_contract = true := by decide +kernel
def s2413_plain : CertifiedContract :=
  ⟨2413, 2411, 0, .none, s2413_plain_contract, 103, s2413_plain_checked⟩

def s2414_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, true, true, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s2414_zero_checked : check 392 s2414_zero_contract = true := by decide +kernel
def s2414_zero : CertifiedContract :=
  ⟨2414, 2417, 0, .none, s2414_zero_contract, 392, s2414_zero_checked⟩

def nonterminal : Array CertifiedContract := #[
  s2365_zero,
  s2365_positive,
  s2366_plain,
  s2367_plain,
  s2368_zero,
  s2368_positive,
  s2369_plain,
  s2370_plain,
  s2371_plain,
  s2372_zero,
  s2372_positive,
  s2373_plain,
  s2374_zero,
  s2374_positive,
  s2375_plain,
  s2376_plain,
  s2377_plain,
  s2378_zero,
  s2378_positive,
  s2379_plain,
  s2380_plain,
  s2381_plain,
  s2382_plain,
  s2383_plain,
  s2384_zero,
  s2384_positive,
  s2385_plain,
  s2386_zero,
  s2386_positive,
  s2387_plain,
  s2388_zero,
  s2388_positive,
  s2389_plain,
  s2390_plain,
  s2391_plain,
  s2392_zero,
  s2392_positive,
  s2393_plain,
  s2394_plain,
  s2395_zero,
  s2395_positive,
  s2396_plain,
  s2397_plain,
  s2398_plain,
  s2399_zero,
  s2399_positive,
  s2400_plain,
  s2401_zero,
  s2401_positive,
  s2402_plain,
  s2403_plain,
  s2404_plain,
  s2405_zero,
  s2405_positive,
  s2406_plain,
  s2407_plain,
  s2408_plain,
  s2409_plain,
  s2410_plain,
  s2411_zero,
  s2411_positive,
  s2412_plain,
  s2413_plain,
  s2414_zero
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S048
