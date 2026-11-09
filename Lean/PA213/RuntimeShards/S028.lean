module

public import PA213.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S028
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s1377_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, false, true, false] 1 (.dec 7)⟩
theorem s1377_positive_checked : check 332 s1377_positive_contract = true := by decide +kernel
def s1377_positive : CertifiedContract :=
  ⟨1377, 1378, 1, (.dec 7), s1377_positive_contract, 332, s1377_positive_checked⟩

def s1378_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s1378_plain_checked : check 336 s1378_plain_contract = true := by decide +kernel
def s1378_plain : CertifiedContract :=
  ⟨1378, 1379, 0, (.inc 2), s1378_plain_contract, 336, s1378_plain_checked⟩

def s1379_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1379_plain_checked : check 363 s1379_plain_contract = true := by decide +kernel
def s1379_plain : CertifiedContract :=
  ⟨1379, 1380, 0, (.inc 8), s1379_plain_contract, 363, s1379_plain_checked⟩

def s1380_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s1380_plain_checked : check 94 s1380_plain_contract = true := by decide +kernel
def s1380_plain : CertifiedContract :=
  ⟨1380, 1377, 0, .none, s1380_plain_contract, 94, s1380_plain_checked⟩

def s1381_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s1381_zero_checked : check 335 s1381_zero_contract = true := by decide +kernel
def s1381_zero : CertifiedContract :=
  ⟨1381, 1384, 0, .none, s1381_zero_contract, 335, s1381_zero_checked⟩

def s1381_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s1381_positive_checked : check 332 s1381_positive_contract = true := by decide +kernel
def s1381_positive : CertifiedContract :=
  ⟨1381, 1382, 1, (.dec 8), s1381_positive_contract, 332, s1381_positive_checked⟩

def s1382_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, true, true, true] 0 (.inc 7)⟩
theorem s1382_plain_checked : check 363 s1382_plain_contract = true := by decide +kernel
def s1382_plain : CertifiedContract :=
  ⟨1382, 1383, 0, (.inc 7), s1382_plain_contract, 363, s1382_plain_checked⟩

def s1383_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s1383_plain_checked : check 88 s1383_plain_contract = true := by decide +kernel
def s1383_plain : CertifiedContract :=
  ⟨1383, 1381, 0, .none, s1383_plain_contract, 88, s1383_plain_checked⟩

def s1384_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s1384_zero_checked : check 338 s1384_zero_contract = true := by decide +kernel
def s1384_zero : CertifiedContract :=
  ⟨1384, 1392, 0, .none, s1384_zero_contract, 338, s1384_zero_checked⟩

def s1384_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s1384_positive_checked : check 344 s1384_positive_contract = true := by decide +kernel
def s1384_positive : CertifiedContract :=
  ⟨1384, 1385, 1, (.dec 0), s1384_positive_contract, 344, s1384_positive_checked⟩

def s1385_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s1385_plain_checked : check 354 s1385_plain_contract = true := by decide +kernel
def s1385_plain : CertifiedContract :=
  ⟨1385, 1386, 0, (.inc 5), s1385_plain_contract, 354, s1385_plain_checked⟩

def s1386_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1386_zero_checked : check 380 s1386_zero_contract = true := by decide +kernel
def s1386_zero : CertifiedContract :=
  ⟨1386, 1388, 0, .none, s1386_zero_contract, 380, s1386_zero_checked⟩

def s1386_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s1386_positive_checked : check 386 s1386_positive_contract = true := by decide +kernel
def s1386_positive : CertifiedContract :=
  ⟨1386, 1387, 1, (.dec 8), s1386_positive_contract, 386, s1386_positive_checked⟩

def s1387_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s1387_plain_checked : check 103 s1387_plain_contract = true := by decide +kernel
def s1387_plain : CertifiedContract :=
  ⟨1387, 1391, 0, .none, s1387_plain_contract, 103, s1387_plain_checked⟩

def s1388_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s1388_zero_checked : check 392 s1388_zero_contract = true := by decide +kernel
def s1388_zero : CertifiedContract :=
  ⟨1388, 1391, 0, .none, s1388_zero_contract, 392, s1388_zero_checked⟩

def s1388_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s1388_positive_checked : check 395 s1388_positive_contract = true := by decide +kernel
def s1388_positive : CertifiedContract :=
  ⟨1388, 1389, 1, (.dec 5), s1388_positive_contract, 395, s1388_positive_checked⟩

def s1389_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1389_plain_checked : check 399 s1389_plain_contract = true := by decide +kernel
def s1389_plain : CertifiedContract :=
  ⟨1389, 1390, 0, (.inc 8), s1389_plain_contract, 399, s1389_plain_checked⟩

def s1390_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1390_plain_checked : check 106 s1390_plain_contract = true := by decide +kernel
def s1390_plain : CertifiedContract :=
  ⟨1390, 1388, 0, .none, s1390_plain_contract, 106, s1390_plain_checked⟩

def s1391_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s1391_plain_checked : check 97 s1391_plain_contract = true := by decide +kernel
def s1391_plain : CertifiedContract :=
  ⟨1391, 1384, 0, .none, s1391_plain_contract, 97, s1391_plain_checked⟩

def s1392_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s1392_zero_checked : check 338 s1392_zero_contract = true := by decide +kernel
def s1392_zero : CertifiedContract :=
  ⟨1392, 1395, 0, .none, s1392_zero_contract, 338, s1392_zero_checked⟩

def s1392_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s1392_positive_checked : check 341 s1392_positive_contract = true := by decide +kernel
def s1392_positive : CertifiedContract :=
  ⟨1392, 1393, 1, (.dec 5), s1392_positive_contract, 341, s1392_positive_checked⟩

def s1393_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s1393_plain_checked : check 354 s1393_plain_contract = true := by decide +kernel
def s1393_plain : CertifiedContract :=
  ⟨1393, 1394, 0, (.inc 0), s1393_plain_contract, 354, s1393_plain_checked⟩

def s1394_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s1394_plain_checked : check 91 s1394_plain_contract = true := by decide +kernel
def s1394_plain : CertifiedContract :=
  ⟨1394, 1392, 0, .none, s1394_plain_contract, 91, s1394_plain_checked⟩

def s1395_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s1395_zero_checked : check 335 s1395_zero_contract = true := by decide +kernel
def s1395_zero : CertifiedContract :=
  ⟨1395, 1399, 0, .none, s1395_zero_contract, 335, s1395_zero_checked⟩

def s1395_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1395_positive_checked : check 341 s1395_positive_contract = true := by decide +kernel
def s1395_positive : CertifiedContract :=
  ⟨1395, 1396, 1, (.dec 2), s1395_positive_contract, 341, s1395_positive_checked⟩

def s1396_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1396_plain_checked : check 354 s1396_plain_contract = true := by decide +kernel
def s1396_plain : CertifiedContract :=
  ⟨1396, 1397, 0, (.inc 5), s1396_plain_contract, 354, s1396_plain_checked⟩

def s1397_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1397_plain_checked : check 381 s1397_plain_contract = true := by decide +kernel
def s1397_plain : CertifiedContract :=
  ⟨1397, 1398, 0, (.inc 8), s1397_plain_contract, 381, s1397_plain_checked⟩

def s1398_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s1398_plain_checked : check 100 s1398_plain_contract = true := by decide +kernel
def s1398_plain : CertifiedContract :=
  ⟨1398, 1395, 0, .none, s1398_plain_contract, 100, s1398_plain_checked⟩

def s1399_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s1399_zero_checked : check 356 s1399_zero_contract = true := by decide +kernel
def s1399_zero : CertifiedContract :=
  ⟨1399, 1405, 0, .none, s1399_zero_contract, 356, s1399_zero_checked⟩

def s1399_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1399_positive_checked : check 359 s1399_positive_contract = true := by decide +kernel
def s1399_positive : CertifiedContract :=
  ⟨1399, 1400, 1, (.dec 8), s1399_positive_contract, 359, s1399_positive_checked⟩

def s1400_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1400_plain_checked : check 354 s1400_plain_contract = true := by decide +kernel
def s1400_plain : CertifiedContract :=
  ⟨1400, 1401, 0, (.inc 5), s1400_plain_contract, 354, s1400_plain_checked⟩

def s1401_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s1401_zero_checked : check 374 s1401_zero_contract = true := by decide +kernel
def s1401_zero : CertifiedContract :=
  ⟨1401, 1404, 0, .none, s1401_zero_contract, 374, s1401_zero_checked⟩

def s1401_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1401_positive_checked : check 377 s1401_positive_contract = true := by decide +kernel
def s1401_positive : CertifiedContract :=
  ⟨1401, 1402, 1, (.dec 8), s1401_positive_contract, 377, s1401_positive_checked⟩

def s1402_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1402_plain_checked : check 372 s1402_plain_contract = true := by decide +kernel
def s1402_plain : CertifiedContract :=
  ⟨1402, 1403, 0, (.inc 2), s1402_plain_contract, 372, s1402_plain_checked⟩

def s1403_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s1403_plain_checked : check 100 s1403_plain_contract = true := by decide +kernel
def s1403_plain : CertifiedContract :=
  ⟨1403, 1401, 0, .none, s1403_plain_contract, 100, s1403_plain_checked⟩

def s1404_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s1404_plain_checked : check 103 s1404_plain_contract = true := by decide +kernel
def s1404_plain : CertifiedContract :=
  ⟨1404, 1395, 0, .none, s1404_plain_contract, 103, s1404_plain_checked⟩

def s1405_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, true] 0 .none⟩
theorem s1405_zero_checked : check 341 s1405_zero_contract = true := by decide +kernel
def s1405_zero : CertifiedContract :=
  ⟨1405, 1411, 0, .none, s1405_zero_contract, 341, s1405_zero_checked⟩

def s1405_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s1405_positive_checked : check 341 s1405_positive_contract = true := by decide +kernel
def s1405_positive : CertifiedContract :=
  ⟨1405, 1406, 1, (.dec 5), s1405_positive_contract, 341, s1405_positive_checked⟩

def s1406_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s1406_plain_checked : check 354 s1406_plain_contract = true := by decide +kernel
def s1406_plain : CertifiedContract :=
  ⟨1406, 1407, 0, (.inc 2), s1406_plain_contract, 354, s1406_plain_checked⟩

def s1407_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s1407_plain_checked : check 357 s1407_plain_contract = true := by decide +kernel
def s1407_plain : CertifiedContract :=
  ⟨1407, 1408, 0, (.inc 2), s1407_plain_contract, 357, s1407_plain_checked⟩

def s1408_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s1408_plain_checked : check 354 s1408_plain_contract = true := by decide +kernel
def s1408_plain : CertifiedContract :=
  ⟨1408, 1409, 0, (.inc 2), s1408_plain_contract, 354, s1408_plain_checked⟩

def s1409_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s1409_plain_checked : check 360 s1409_plain_contract = true := by decide +kernel
def s1409_plain : CertifiedContract :=
  ⟨1409, 1410, 0, (.inc 2), s1409_plain_contract, 360, s1409_plain_checked⟩

def s1410_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s1410_plain_checked : check 88 s1410_plain_contract = true := by decide +kernel
def s1410_plain : CertifiedContract :=
  ⟨1410, 1405, 0, .none, s1410_plain_contract, 88, s1410_plain_checked⟩

def s1411_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, false] 0 (.inc 2)⟩
theorem s1411_plain_checked : check 315 s1411_plain_contract = true := by decide +kernel
def s1411_plain : CertifiedContract :=
  ⟨1411, 1412, 0, (.inc 2), s1411_plain_contract, 315, s1411_plain_checked⟩

def s1412_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, true, false] 0 .none⟩
theorem s1412_zero_checked : check 365 s1412_zero_contract = true := by decide +kernel
def s1412_zero : CertifiedContract :=
  ⟨1412, 1420, 0, .none, s1412_zero_contract, 365, s1412_zero_checked⟩

def s1412_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, false] 1 (.dec 0)⟩
theorem s1412_positive_checked : check 371 s1412_positive_contract = true := by decide +kernel
def s1412_positive : CertifiedContract :=
  ⟨1412, 1413, 1, (.dec 0), s1412_positive_contract, 371, s1412_positive_checked⟩

def s1413_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s1413_plain_checked : check 381 s1413_plain_contract = true := by decide +kernel
def s1413_plain : CertifiedContract :=
  ⟨1413, 1414, 0, (.inc 5), s1413_plain_contract, 381, s1413_plain_checked⟩

def s1414_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1414_zero_checked : check 407 s1414_zero_contract = true := by decide +kernel
def s1414_zero : CertifiedContract :=
  ⟨1414, 1416, 0, .none, s1414_zero_contract, 407, s1414_zero_checked⟩

def s1414_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s1414_positive_checked : check 413 s1414_positive_contract = true := by decide +kernel
def s1414_positive : CertifiedContract :=
  ⟨1414, 1415, 1, (.dec 8), s1414_positive_contract, 413, s1414_positive_checked⟩

def s1415_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, true] 0 .none⟩
theorem s1415_plain_checked : check 112 s1415_plain_contract = true := by decide +kernel
def s1415_plain : CertifiedContract :=
  ⟨1415, 1419, 0, .none, s1415_plain_contract, 112, s1415_plain_checked⟩

def s1416_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, true] 0 .none⟩
theorem s1416_zero_checked : check 419 s1416_zero_contract = true := by decide +kernel
def s1416_zero : CertifiedContract :=
  ⟨1416, 1419, 0, .none, s1416_zero_contract, 419, s1416_zero_checked⟩

def s1416_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s1416_positive_checked : check 422 s1416_positive_contract = true := by decide +kernel
def s1416_positive : CertifiedContract :=
  ⟨1416, 1417, 1, (.dec 5), s1416_positive_contract, 422, s1416_positive_checked⟩

def s1417_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1417_plain_checked : check 426 s1417_plain_contract = true := by decide +kernel
def s1417_plain : CertifiedContract :=
  ⟨1417, 1418, 0, (.inc 8), s1417_plain_contract, 426, s1417_plain_checked⟩

def s1418_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1418_plain_checked : check 115 s1418_plain_contract = true := by decide +kernel
def s1418_plain : CertifiedContract :=
  ⟨1418, 1416, 0, .none, s1418_plain_contract, 115, s1418_plain_checked⟩

def s1419_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s1419_plain_checked : check 106 s1419_plain_contract = true := by decide +kernel
def s1419_plain : CertifiedContract :=
  ⟨1419, 1412, 0, .none, s1419_plain_contract, 106, s1419_plain_checked⟩

def s1420_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, false, false] 0 .none⟩
theorem s1420_zero_checked : check 365 s1420_zero_contract = true := by decide +kernel
def s1420_zero : CertifiedContract :=
  ⟨1420, 1423, 0, .none, s1420_zero_contract, 365, s1420_zero_checked⟩

def s1420_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, true, true, false] 1 (.dec 5)⟩
theorem s1420_positive_checked : check 368 s1420_positive_contract = true := by decide +kernel
def s1420_positive : CertifiedContract :=
  ⟨1420, 1421, 1, (.dec 5), s1420_positive_contract, 368, s1420_positive_checked⟩

def s1421_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, true, true, true] 0 (.inc 0)⟩
theorem s1421_plain_checked : check 381 s1421_plain_contract = true := by decide +kernel
def s1421_plain : CertifiedContract :=
  ⟨1421, 1422, 0, (.inc 0), s1421_plain_contract, 381, s1421_plain_checked⟩

def s1422_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, true, false] 0 .none⟩
theorem s1422_plain_checked : check 100 s1422_plain_contract = true := by decide +kernel
def s1422_plain : CertifiedContract :=
  ⟨1422, 1420, 0, .none, s1422_plain_contract, 100, s1422_plain_checked⟩

def s1423_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, true, false] 0 .none⟩
theorem s1423_zero_checked : check 362 s1423_zero_contract = true := by decide +kernel
def s1423_zero : CertifiedContract :=
  ⟨1423, 1427, 0, .none, s1423_zero_contract, 362, s1423_zero_checked⟩

def s1423_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1423_positive_checked : check 368 s1423_positive_contract = true := by decide +kernel
def s1423_positive : CertifiedContract :=
  ⟨1423, 1424, 1, (.dec 2), s1423_positive_contract, 368, s1423_positive_checked⟩

def s1424_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1424_plain_checked : check 381 s1424_plain_contract = true := by decide +kernel
def s1424_plain : CertifiedContract :=
  ⟨1424, 1425, 0, (.inc 5), s1424_plain_contract, 381, s1424_plain_checked⟩

def s1425_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1425_plain_checked : check 408 s1425_plain_contract = true := by decide +kernel
def s1425_plain : CertifiedContract :=
  ⟨1425, 1426, 0, (.inc 8), s1425_plain_contract, 408, s1425_plain_checked⟩

def s1426_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, false, false] 0 .none⟩
theorem s1426_plain_checked : check 109 s1426_plain_contract = true := by decide +kernel
def s1426_plain : CertifiedContract :=
  ⟨1426, 1423, 0, .none, s1426_plain_contract, 109, s1426_plain_checked⟩

def nonterminal : Array CertifiedContract := #[
  s1377_positive,
  s1378_plain,
  s1379_plain,
  s1380_plain,
  s1381_zero,
  s1381_positive,
  s1382_plain,
  s1383_plain,
  s1384_zero,
  s1384_positive,
  s1385_plain,
  s1386_zero,
  s1386_positive,
  s1387_plain,
  s1388_zero,
  s1388_positive,
  s1389_plain,
  s1390_plain,
  s1391_plain,
  s1392_zero,
  s1392_positive,
  s1393_plain,
  s1394_plain,
  s1395_zero,
  s1395_positive,
  s1396_plain,
  s1397_plain,
  s1398_plain,
  s1399_zero,
  s1399_positive,
  s1400_plain,
  s1401_zero,
  s1401_positive,
  s1402_plain,
  s1403_plain,
  s1404_plain,
  s1405_zero,
  s1405_positive,
  s1406_plain,
  s1407_plain,
  s1408_plain,
  s1409_plain,
  s1410_plain,
  s1411_plain,
  s1412_zero,
  s1412_positive,
  s1413_plain,
  s1414_zero,
  s1414_positive,
  s1415_plain,
  s1416_zero,
  s1416_positive,
  s1417_plain,
  s1418_plain,
  s1419_plain,
  s1420_zero,
  s1420_positive,
  s1421_plain,
  s1422_plain,
  s1423_zero,
  s1423_positive,
  s1424_plain,
  s1425_plain,
  s1426_plain
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S028
