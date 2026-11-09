import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S028
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s1377_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, false, true, false] 1 (.dec 7)⟩
theorem s1377_positive_checked : check 333 s1377_positive_contract = true := by decide +kernel
def s1377_positive : CertifiedContract :=
  ⟨1377, 1378, 1, (.dec 7), s1377_positive_contract, 333, s1377_positive_checked⟩

def s1378_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s1378_plain_checked : check 337 s1378_plain_contract = true := by decide +kernel
def s1378_plain : CertifiedContract :=
  ⟨1378, 1379, 0, (.inc 2), s1378_plain_contract, 337, s1378_plain_checked⟩

def s1379_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1379_plain_checked : check 364 s1379_plain_contract = true := by decide +kernel
def s1379_plain : CertifiedContract :=
  ⟨1379, 1380, 0, (.inc 8), s1379_plain_contract, 364, s1379_plain_checked⟩

def s1380_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s1380_plain_checked : check 95 s1380_plain_contract = true := by decide +kernel
def s1380_plain : CertifiedContract :=
  ⟨1380, 1377, 0, .none, s1380_plain_contract, 95, s1380_plain_checked⟩

def s1381_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s1381_zero_checked : check 336 s1381_zero_contract = true := by decide +kernel
def s1381_zero : CertifiedContract :=
  ⟨1381, 1384, 0, .none, s1381_zero_contract, 336, s1381_zero_checked⟩

def s1381_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s1381_positive_checked : check 333 s1381_positive_contract = true := by decide +kernel
def s1381_positive : CertifiedContract :=
  ⟨1381, 1382, 1, (.dec 8), s1381_positive_contract, 333, s1381_positive_checked⟩

def s1382_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, true, true, true] 0 (.inc 7)⟩
theorem s1382_plain_checked : check 364 s1382_plain_contract = true := by decide +kernel
def s1382_plain : CertifiedContract :=
  ⟨1382, 1383, 0, (.inc 7), s1382_plain_contract, 364, s1382_plain_checked⟩

def s1383_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s1383_plain_checked : check 89 s1383_plain_contract = true := by decide +kernel
def s1383_plain : CertifiedContract :=
  ⟨1383, 1381, 0, .none, s1383_plain_contract, 89, s1383_plain_checked⟩

def s1384_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s1384_zero_checked : check 339 s1384_zero_contract = true := by decide +kernel
def s1384_zero : CertifiedContract :=
  ⟨1384, 1392, 0, .none, s1384_zero_contract, 339, s1384_zero_checked⟩

def s1384_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s1384_positive_checked : check 345 s1384_positive_contract = true := by decide +kernel
def s1384_positive : CertifiedContract :=
  ⟨1384, 1385, 1, (.dec 0), s1384_positive_contract, 345, s1384_positive_checked⟩

def s1385_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s1385_plain_checked : check 355 s1385_plain_contract = true := by decide +kernel
def s1385_plain : CertifiedContract :=
  ⟨1385, 1386, 0, (.inc 5), s1385_plain_contract, 355, s1385_plain_checked⟩

def s1386_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1386_zero_checked : check 381 s1386_zero_contract = true := by decide +kernel
def s1386_zero : CertifiedContract :=
  ⟨1386, 1388, 0, .none, s1386_zero_contract, 381, s1386_zero_checked⟩

def s1386_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s1386_positive_checked : check 387 s1386_positive_contract = true := by decide +kernel
def s1386_positive : CertifiedContract :=
  ⟨1386, 1387, 1, (.dec 8), s1386_positive_contract, 387, s1386_positive_checked⟩

def s1387_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s1387_plain_checked : check 104 s1387_plain_contract = true := by decide +kernel
def s1387_plain : CertifiedContract :=
  ⟨1387, 1391, 0, .none, s1387_plain_contract, 104, s1387_plain_checked⟩

def s1388_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s1388_zero_checked : check 393 s1388_zero_contract = true := by decide +kernel
def s1388_zero : CertifiedContract :=
  ⟨1388, 1391, 0, .none, s1388_zero_contract, 393, s1388_zero_checked⟩

def s1388_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s1388_positive_checked : check 396 s1388_positive_contract = true := by decide +kernel
def s1388_positive : CertifiedContract :=
  ⟨1388, 1389, 1, (.dec 5), s1388_positive_contract, 396, s1388_positive_checked⟩

def s1389_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1389_plain_checked : check 400 s1389_plain_contract = true := by decide +kernel
def s1389_plain : CertifiedContract :=
  ⟨1389, 1390, 0, (.inc 8), s1389_plain_contract, 400, s1389_plain_checked⟩

def s1390_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1390_plain_checked : check 107 s1390_plain_contract = true := by decide +kernel
def s1390_plain : CertifiedContract :=
  ⟨1390, 1388, 0, .none, s1390_plain_contract, 107, s1390_plain_checked⟩

def s1391_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s1391_plain_checked : check 98 s1391_plain_contract = true := by decide +kernel
def s1391_plain : CertifiedContract :=
  ⟨1391, 1384, 0, .none, s1391_plain_contract, 98, s1391_plain_checked⟩

def s1392_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s1392_zero_checked : check 339 s1392_zero_contract = true := by decide +kernel
def s1392_zero : CertifiedContract :=
  ⟨1392, 1395, 0, .none, s1392_zero_contract, 339, s1392_zero_checked⟩

def s1392_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s1392_positive_checked : check 342 s1392_positive_contract = true := by decide +kernel
def s1392_positive : CertifiedContract :=
  ⟨1392, 1393, 1, (.dec 5), s1392_positive_contract, 342, s1392_positive_checked⟩

def s1393_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s1393_plain_checked : check 355 s1393_plain_contract = true := by decide +kernel
def s1393_plain : CertifiedContract :=
  ⟨1393, 1394, 0, (.inc 0), s1393_plain_contract, 355, s1393_plain_checked⟩

def s1394_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s1394_plain_checked : check 92 s1394_plain_contract = true := by decide +kernel
def s1394_plain : CertifiedContract :=
  ⟨1394, 1392, 0, .none, s1394_plain_contract, 92, s1394_plain_checked⟩

def s1395_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s1395_zero_checked : check 336 s1395_zero_contract = true := by decide +kernel
def s1395_zero : CertifiedContract :=
  ⟨1395, 1399, 0, .none, s1395_zero_contract, 336, s1395_zero_checked⟩

def s1395_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1395_positive_checked : check 342 s1395_positive_contract = true := by decide +kernel
def s1395_positive : CertifiedContract :=
  ⟨1395, 1396, 1, (.dec 2), s1395_positive_contract, 342, s1395_positive_checked⟩

def s1396_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1396_plain_checked : check 355 s1396_plain_contract = true := by decide +kernel
def s1396_plain : CertifiedContract :=
  ⟨1396, 1397, 0, (.inc 5), s1396_plain_contract, 355, s1396_plain_checked⟩

def s1397_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1397_plain_checked : check 382 s1397_plain_contract = true := by decide +kernel
def s1397_plain : CertifiedContract :=
  ⟨1397, 1398, 0, (.inc 8), s1397_plain_contract, 382, s1397_plain_checked⟩

def s1398_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s1398_plain_checked : check 101 s1398_plain_contract = true := by decide +kernel
def s1398_plain : CertifiedContract :=
  ⟨1398, 1395, 0, .none, s1398_plain_contract, 101, s1398_plain_checked⟩

def s1399_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s1399_zero_checked : check 357 s1399_zero_contract = true := by decide +kernel
def s1399_zero : CertifiedContract :=
  ⟨1399, 1405, 0, .none, s1399_zero_contract, 357, s1399_zero_checked⟩

def s1399_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1399_positive_checked : check 360 s1399_positive_contract = true := by decide +kernel
def s1399_positive : CertifiedContract :=
  ⟨1399, 1400, 1, (.dec 8), s1399_positive_contract, 360, s1399_positive_checked⟩

def s1400_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1400_plain_checked : check 355 s1400_plain_contract = true := by decide +kernel
def s1400_plain : CertifiedContract :=
  ⟨1400, 1401, 0, (.inc 5), s1400_plain_contract, 355, s1400_plain_checked⟩

def s1401_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s1401_zero_checked : check 375 s1401_zero_contract = true := by decide +kernel
def s1401_zero : CertifiedContract :=
  ⟨1401, 1404, 0, .none, s1401_zero_contract, 375, s1401_zero_checked⟩

def s1401_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1401_positive_checked : check 378 s1401_positive_contract = true := by decide +kernel
def s1401_positive : CertifiedContract :=
  ⟨1401, 1402, 1, (.dec 8), s1401_positive_contract, 378, s1401_positive_checked⟩

def s1402_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1402_plain_checked : check 373 s1402_plain_contract = true := by decide +kernel
def s1402_plain : CertifiedContract :=
  ⟨1402, 1403, 0, (.inc 2), s1402_plain_contract, 373, s1402_plain_checked⟩

def s1403_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s1403_plain_checked : check 101 s1403_plain_contract = true := by decide +kernel
def s1403_plain : CertifiedContract :=
  ⟨1403, 1401, 0, .none, s1403_plain_contract, 101, s1403_plain_checked⟩

def s1404_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s1404_plain_checked : check 104 s1404_plain_contract = true := by decide +kernel
def s1404_plain : CertifiedContract :=
  ⟨1404, 1395, 0, .none, s1404_plain_contract, 104, s1404_plain_checked⟩

def s1405_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, true] 0 .none⟩
theorem s1405_zero_checked : check 342 s1405_zero_contract = true := by decide +kernel
def s1405_zero : CertifiedContract :=
  ⟨1405, 1411, 0, .none, s1405_zero_contract, 342, s1405_zero_checked⟩

def s1405_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s1405_positive_checked : check 342 s1405_positive_contract = true := by decide +kernel
def s1405_positive : CertifiedContract :=
  ⟨1405, 1406, 1, (.dec 5), s1405_positive_contract, 342, s1405_positive_checked⟩

def s1406_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s1406_plain_checked : check 355 s1406_plain_contract = true := by decide +kernel
def s1406_plain : CertifiedContract :=
  ⟨1406, 1407, 0, (.inc 2), s1406_plain_contract, 355, s1406_plain_checked⟩

def s1407_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s1407_plain_checked : check 358 s1407_plain_contract = true := by decide +kernel
def s1407_plain : CertifiedContract :=
  ⟨1407, 1408, 0, (.inc 2), s1407_plain_contract, 358, s1407_plain_checked⟩

def s1408_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s1408_plain_checked : check 364 s1408_plain_contract = true := by decide +kernel
def s1408_plain : CertifiedContract :=
  ⟨1408, 1409, 0, (.inc 2), s1408_plain_contract, 364, s1408_plain_checked⟩

def s1409_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s1409_plain_checked : check 370 s1409_plain_contract = true := by decide +kernel
def s1409_plain : CertifiedContract :=
  ⟨1409, 1410, 0, (.inc 2), s1409_plain_contract, 370, s1409_plain_checked⟩

def s1410_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s1410_plain_checked : check 89 s1410_plain_contract = true := by decide +kernel
def s1410_plain : CertifiedContract :=
  ⟨1410, 1405, 0, .none, s1410_plain_contract, 89, s1410_plain_checked⟩

def s1411_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, false] 0 (.inc 2)⟩
theorem s1411_plain_checked : check 316 s1411_plain_contract = true := by decide +kernel
def s1411_plain : CertifiedContract :=
  ⟨1411, 1412, 0, (.inc 2), s1411_plain_contract, 316, s1411_plain_checked⟩

def s1412_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, true, false] 0 .none⟩
theorem s1412_zero_checked : check 366 s1412_zero_contract = true := by decide +kernel
def s1412_zero : CertifiedContract :=
  ⟨1412, 1420, 0, .none, s1412_zero_contract, 366, s1412_zero_checked⟩

def s1412_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, false] 1 (.dec 0)⟩
theorem s1412_positive_checked : check 372 s1412_positive_contract = true := by decide +kernel
def s1412_positive : CertifiedContract :=
  ⟨1412, 1413, 1, (.dec 0), s1412_positive_contract, 372, s1412_positive_checked⟩

def s1413_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s1413_plain_checked : check 382 s1413_plain_contract = true := by decide +kernel
def s1413_plain : CertifiedContract :=
  ⟨1413, 1414, 0, (.inc 5), s1413_plain_contract, 382, s1413_plain_checked⟩

def s1414_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1414_zero_checked : check 408 s1414_zero_contract = true := by decide +kernel
def s1414_zero : CertifiedContract :=
  ⟨1414, 1416, 0, .none, s1414_zero_contract, 408, s1414_zero_checked⟩

def s1414_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s1414_positive_checked : check 414 s1414_positive_contract = true := by decide +kernel
def s1414_positive : CertifiedContract :=
  ⟨1414, 1415, 1, (.dec 8), s1414_positive_contract, 414, s1414_positive_checked⟩

def s1415_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, true] 0 .none⟩
theorem s1415_plain_checked : check 113 s1415_plain_contract = true := by decide +kernel
def s1415_plain : CertifiedContract :=
  ⟨1415, 1419, 0, .none, s1415_plain_contract, 113, s1415_plain_checked⟩

def s1416_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, true] 0 .none⟩
theorem s1416_zero_checked : check 420 s1416_zero_contract = true := by decide +kernel
def s1416_zero : CertifiedContract :=
  ⟨1416, 1419, 0, .none, s1416_zero_contract, 420, s1416_zero_checked⟩

def s1416_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s1416_positive_checked : check 423 s1416_positive_contract = true := by decide +kernel
def s1416_positive : CertifiedContract :=
  ⟨1416, 1417, 1, (.dec 5), s1416_positive_contract, 423, s1416_positive_checked⟩

def s1417_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1417_plain_checked : check 427 s1417_plain_contract = true := by decide +kernel
def s1417_plain : CertifiedContract :=
  ⟨1417, 1418, 0, (.inc 8), s1417_plain_contract, 427, s1417_plain_checked⟩

def s1418_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1418_plain_checked : check 116 s1418_plain_contract = true := by decide +kernel
def s1418_plain : CertifiedContract :=
  ⟨1418, 1416, 0, .none, s1418_plain_contract, 116, s1418_plain_checked⟩

def s1419_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s1419_plain_checked : check 107 s1419_plain_contract = true := by decide +kernel
def s1419_plain : CertifiedContract :=
  ⟨1419, 1412, 0, .none, s1419_plain_contract, 107, s1419_plain_checked⟩

def s1420_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, false, false] 0 .none⟩
theorem s1420_zero_checked : check 366 s1420_zero_contract = true := by decide +kernel
def s1420_zero : CertifiedContract :=
  ⟨1420, 1423, 0, .none, s1420_zero_contract, 366, s1420_zero_checked⟩

def s1420_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, true, true, false] 1 (.dec 5)⟩
theorem s1420_positive_checked : check 369 s1420_positive_contract = true := by decide +kernel
def s1420_positive : CertifiedContract :=
  ⟨1420, 1421, 1, (.dec 5), s1420_positive_contract, 369, s1420_positive_checked⟩

def s1421_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, true, true, true] 0 (.inc 0)⟩
theorem s1421_plain_checked : check 382 s1421_plain_contract = true := by decide +kernel
def s1421_plain : CertifiedContract :=
  ⟨1421, 1422, 0, (.inc 0), s1421_plain_contract, 382, s1421_plain_checked⟩

def s1422_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, false, true, false] 0 .none⟩
theorem s1422_plain_checked : check 101 s1422_plain_contract = true := by decide +kernel
def s1422_plain : CertifiedContract :=
  ⟨1422, 1420, 0, .none, s1422_plain_contract, 101, s1422_plain_checked⟩

def s1423_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, true, false] 0 .none⟩
theorem s1423_zero_checked : check 363 s1423_zero_contract = true := by decide +kernel
def s1423_zero : CertifiedContract :=
  ⟨1423, 1427, 0, .none, s1423_zero_contract, 363, s1423_zero_checked⟩

def s1423_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1423_positive_checked : check 369 s1423_positive_contract = true := by decide +kernel
def s1423_positive : CertifiedContract :=
  ⟨1423, 1424, 1, (.dec 2), s1423_positive_contract, 369, s1423_positive_checked⟩

def s1424_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1424_plain_checked : check 382 s1424_plain_contract = true := by decide +kernel
def s1424_plain : CertifiedContract :=
  ⟨1424, 1425, 0, (.inc 5), s1424_plain_contract, 382, s1424_plain_checked⟩

def s1425_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1425_plain_checked : check 409 s1425_plain_contract = true := by decide +kernel
def s1425_plain : CertifiedContract :=
  ⟨1425, 1426, 0, (.inc 8), s1425_plain_contract, 409, s1425_plain_checked⟩

def s1426_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, false, true, true, false, false, false, true, false, false, false] 0 .none⟩
theorem s1426_plain_checked : check 110 s1426_plain_contract = true := by decide +kernel
def s1426_plain : CertifiedContract :=
  ⟨1426, 1423, 0, .none, s1426_plain_contract, 110, s1426_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S028
