module

public import PA211.UserCandidate.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S032
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s1575_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s1575_zero_checked : check 345 s1575_zero_contract = true := by decide +kernel
def s1575_zero : CertifiedContract :=
  ⟨1575, 1577, 0, .none, s1575_zero_contract, 345, s1575_zero_checked⟩

def s1575_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s1575_positive_checked : check 351 s1575_positive_contract = true := by decide +kernel
def s1575_positive : CertifiedContract :=
  ⟨1575, 1576, 1, (.dec 8), s1575_positive_contract, 351, s1575_positive_checked⟩

def s1576_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, true] 0 .none⟩
theorem s1576_plain_checked : check 92 s1576_plain_contract = true := by decide +kernel
def s1576_plain : CertifiedContract :=
  ⟨1576, 1580, 0, .none, s1576_plain_contract, 92, s1576_plain_checked⟩

def s1577_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, true] 0 .none⟩
theorem s1577_zero_checked : check 357 s1577_zero_contract = true := by decide +kernel
def s1577_zero : CertifiedContract :=
  ⟨1577, 1580, 0, .none, s1577_zero_contract, 357, s1577_zero_checked⟩

def s1577_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s1577_positive_checked : check 360 s1577_positive_contract = true := by decide +kernel
def s1577_positive : CertifiedContract :=
  ⟨1577, 1578, 1, (.dec 5), s1577_positive_contract, 360, s1577_positive_checked⟩

def s1578_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1578_plain_checked : check 364 s1578_plain_contract = true := by decide +kernel
def s1578_plain : CertifiedContract :=
  ⟨1578, 1579, 0, (.inc 8), s1578_plain_contract, 364, s1578_plain_checked⟩

def s1579_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s1579_plain_checked : check 95 s1579_plain_contract = true := by decide +kernel
def s1579_plain : CertifiedContract :=
  ⟨1579, 1577, 0, .none, s1579_plain_contract, 95, s1579_plain_checked⟩

def s1580_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, false] 0 .none⟩
theorem s1580_plain_checked : check 86 s1580_plain_contract = true := by decide +kernel
def s1580_plain : CertifiedContract :=
  ⟨1580, 1573, 0, .none, s1580_plain_contract, 86, s1580_plain_checked⟩

def s1581_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, false, false] 0 .none⟩
theorem s1581_zero_checked : check 303 s1581_zero_contract = true := by decide +kernel
def s1581_zero : CertifiedContract :=
  ⟨1581, 1584, 0, .none, s1581_zero_contract, 303, s1581_zero_checked⟩

def s1581_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s1581_positive_checked : check 306 s1581_positive_contract = true := by decide +kernel
def s1581_positive : CertifiedContract :=
  ⟨1581, 1582, 1, (.dec 5), s1581_positive_contract, 306, s1581_positive_checked⟩

def s1582_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, true, true, true] 0 (.inc 0)⟩
theorem s1582_plain_checked : check 319 s1582_plain_contract = true := by decide +kernel
def s1582_plain : CertifiedContract :=
  ⟨1582, 1583, 0, (.inc 0), s1582_plain_contract, 319, s1582_plain_checked⟩

def s1583_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, true, false] 0 .none⟩
theorem s1583_plain_checked : check 80 s1583_plain_contract = true := by decide +kernel
def s1583_plain : CertifiedContract :=
  ⟨1583, 1581, 0, .none, s1583_plain_contract, 80, s1583_plain_checked⟩

def s1584_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, false] 0 .none⟩
theorem s1584_zero_checked : check 300 s1584_zero_contract = true := by decide +kernel
def s1584_zero : CertifiedContract :=
  ⟨1584, 1588, 0, .none, s1584_zero_contract, 300, s1584_zero_checked⟩

def s1584_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1584_positive_checked : check 306 s1584_positive_contract = true := by decide +kernel
def s1584_positive : CertifiedContract :=
  ⟨1584, 1585, 1, (.dec 2), s1584_positive_contract, 306, s1584_positive_checked⟩

def s1585_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1585_plain_checked : check 319 s1585_plain_contract = true := by decide +kernel
def s1585_plain : CertifiedContract :=
  ⟨1585, 1586, 0, (.inc 5), s1585_plain_contract, 319, s1585_plain_checked⟩

def s1586_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1586_plain_checked : check 346 s1586_plain_contract = true := by decide +kernel
def s1586_plain : CertifiedContract :=
  ⟨1586, 1587, 0, (.inc 8), s1586_plain_contract, 346, s1586_plain_checked⟩

def s1587_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, false, false] 0 .none⟩
theorem s1587_plain_checked : check 89 s1587_plain_contract = true := by decide +kernel
def s1587_plain : CertifiedContract :=
  ⟨1587, 1584, 0, .none, s1587_plain_contract, 89, s1587_plain_checked⟩

def s1588_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, true, false] 0 .none⟩
theorem s1588_zero_checked : check 321 s1588_zero_contract = true := by decide +kernel
def s1588_zero : CertifiedContract :=
  ⟨1588, 1594, 0, .none, s1588_zero_contract, 321, s1588_zero_checked⟩

def s1588_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1588_positive_checked : check 324 s1588_positive_contract = true := by decide +kernel
def s1588_positive : CertifiedContract :=
  ⟨1588, 1589, 1, (.dec 8), s1588_positive_contract, 324, s1588_positive_checked⟩

def s1589_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1589_plain_checked : check 319 s1589_plain_contract = true := by decide +kernel
def s1589_plain : CertifiedContract :=
  ⟨1589, 1590, 0, (.inc 5), s1589_plain_contract, 319, s1589_plain_checked⟩

def s1590_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, true, true] 0 .none⟩
theorem s1590_zero_checked : check 339 s1590_zero_contract = true := by decide +kernel
def s1590_zero : CertifiedContract :=
  ⟨1590, 1593, 0, .none, s1590_zero_contract, 339, s1590_zero_checked⟩

def s1590_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1590_positive_checked : check 342 s1590_positive_contract = true := by decide +kernel
def s1590_positive : CertifiedContract :=
  ⟨1590, 1591, 1, (.dec 8), s1590_positive_contract, 342, s1590_positive_checked⟩

def s1591_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1591_plain_checked : check 337 s1591_plain_contract = true := by decide +kernel
def s1591_plain : CertifiedContract :=
  ⟨1591, 1592, 0, (.inc 2), s1591_plain_contract, 337, s1591_plain_checked⟩

def s1592_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1592_plain_checked : check 89 s1592_plain_contract = true := by decide +kernel
def s1592_plain : CertifiedContract :=
  ⟨1592, 1590, 0, .none, s1592_plain_contract, 89, s1592_plain_checked⟩

def s1593_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, false, false] 0 .none⟩
theorem s1593_plain_checked : check 92 s1593_plain_contract = true := by decide +kernel
def s1593_plain : CertifiedContract :=
  ⟨1593, 1584, 0, .none, s1593_plain_contract, 92, s1593_plain_checked⟩

def s1594_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s1594_zero_checked : check 315 s1594_zero_contract = true := by decide +kernel
def s1594_zero : CertifiedContract :=
  ⟨1594, 1600, 0, .none, s1594_zero_contract, 315, s1594_zero_checked⟩

def s1594_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s1594_positive_checked : check 306 s1594_positive_contract = true := by decide +kernel
def s1594_positive : CertifiedContract :=
  ⟨1594, 1595, 1, (.dec 5), s1594_positive_contract, 306, s1594_positive_checked⟩

def s1595_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s1595_plain_checked : check 319 s1595_plain_contract = true := by decide +kernel
def s1595_plain : CertifiedContract :=
  ⟨1595, 1596, 0, (.inc 2), s1595_plain_contract, 319, s1595_plain_checked⟩

def s1596_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s1596_plain_checked : check 322 s1596_plain_contract = true := by decide +kernel
def s1596_plain : CertifiedContract :=
  ⟨1596, 1597, 0, (.inc 2), s1596_plain_contract, 322, s1596_plain_checked⟩

def s1597_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s1597_plain_checked : check 328 s1597_plain_contract = true := by decide +kernel
def s1597_plain : CertifiedContract :=
  ⟨1597, 1598, 0, (.inc 2), s1597_plain_contract, 328, s1597_plain_checked⟩

def s1598_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, true, true, true] 0 (.inc 2)⟩
theorem s1598_plain_checked : check 334 s1598_plain_contract = true := by decide +kernel
def s1598_plain : CertifiedContract :=
  ⟨1598, 1599, 0, (.inc 2), s1598_plain_contract, 334, s1598_plain_checked⟩

def s1599_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, true, false] 0 .none⟩
theorem s1599_plain_checked : check 77 s1599_plain_contract = true := by decide +kernel
def s1599_plain : CertifiedContract :=
  ⟨1599, 1594, 0, .none, s1599_plain_contract, 77, s1599_plain_checked⟩

def s1600_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, false, true] 0 (.inc 2)⟩
theorem s1600_plain_checked : check 292 s1600_plain_contract = true := by decide +kernel
def s1600_plain : CertifiedContract :=
  ⟨1600, 1601, 0, (.inc 2), s1600_plain_contract, 292, s1600_plain_checked⟩

def s1601_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, false, false] 0 (.inc 2)⟩
theorem s1601_plain_checked : check 295 s1601_plain_contract = true := by decide +kernel
def s1601_plain : CertifiedContract :=
  ⟨1601, 1602, 0, (.inc 2), s1601_plain_contract, 295, s1601_plain_checked⟩

def s1602_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s1602_zero_checked : check 336 s1602_zero_contract = true := by decide +kernel
def s1602_zero : CertifiedContract :=
  ⟨1602, 1605, 0, .none, s1602_zero_contract, 336, s1602_zero_checked⟩

def s1602_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s1602_positive_checked : check 342 s1602_positive_contract = true := by decide +kernel
def s1602_positive : CertifiedContract :=
  ⟨1602, 1603, 1, (.dec 2), s1602_positive_contract, 342, s1602_positive_checked⟩

def s1603_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s1603_plain_checked : check 355 s1603_plain_contract = true := by decide +kernel
def s1603_plain : CertifiedContract :=
  ⟨1603, 1604, 0, (.inc 8), s1603_plain_contract, 355, s1603_plain_checked⟩

def s1604_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s1604_plain_checked : check 92 s1604_plain_contract = true := by decide +kernel
def s1604_plain : CertifiedContract :=
  ⟨1604, 1602, 0, .none, s1604_plain_contract, 92, s1604_plain_checked⟩

def s1605_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1605_zero_checked : check 357 s1605_zero_contract = true := by decide +kernel
def s1605_zero : CertifiedContract :=
  ⟨1605, 1608, 0, .none, s1605_zero_contract, 357, s1605_zero_checked⟩

def s1605_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s1605_positive_checked : check 363 s1605_positive_contract = true := by decide +kernel
def s1605_positive : CertifiedContract :=
  ⟨1605, 1606, 1, (.dec 0), s1605_positive_contract, 363, s1605_positive_checked⟩

def s1606_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s1606_plain_checked : check 355 s1606_plain_contract = true := by decide +kernel
def s1606_plain : CertifiedContract :=
  ⟨1606, 1607, 0, (.inc 2), s1606_plain_contract, 355, s1606_plain_checked⟩

def s1607_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s1607_plain_checked : check 95 s1607_plain_contract = true := by decide +kernel
def s1607_plain : CertifiedContract :=
  ⟨1607, 1605, 0, .none, s1607_plain_contract, 95, s1607_plain_checked⟩

def s1608_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1608_zero_checked : check 363 s1608_zero_contract = true := by decide +kernel
def s1608_zero : CertifiedContract :=
  ⟨1608, 1612, 0, .none, s1608_zero_contract, 363, s1608_zero_checked⟩

def s1608_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1608_positive_checked : check 369 s1608_positive_contract = true := by decide +kernel
def s1608_positive : CertifiedContract :=
  ⟨1608, 1609, 1, (.dec 2), s1608_positive_contract, 369, s1608_positive_checked⟩

def s1609_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1609_plain_checked : check 382 s1609_plain_contract = true := by decide +kernel
def s1609_plain : CertifiedContract :=
  ⟨1609, 1610, 0, (.inc 5), s1609_plain_contract, 382, s1609_plain_checked⟩

def s1610_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1610_plain_checked : check 409 s1610_plain_contract = true := by decide +kernel
def s1610_plain : CertifiedContract :=
  ⟨1610, 1611, 0, (.inc 8), s1610_plain_contract, 409, s1610_plain_checked⟩

def s1611_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1611_plain_checked : check 110 s1611_plain_contract = true := by decide +kernel
def s1611_plain : CertifiedContract :=
  ⟨1611, 1608, 0, .none, s1611_plain_contract, 110, s1611_plain_checked⟩

def s1612_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s1612_zero_checked : check 384 s1612_zero_contract = true := by decide +kernel
def s1612_zero : CertifiedContract :=
  ⟨1612, 1618, 0, .none, s1612_zero_contract, 384, s1612_zero_checked⟩

def s1612_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1612_positive_checked : check 387 s1612_positive_contract = true := by decide +kernel
def s1612_positive : CertifiedContract :=
  ⟨1612, 1613, 1, (.dec 8), s1612_positive_contract, 387, s1612_positive_checked⟩

def s1613_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1613_plain_checked : check 382 s1613_plain_contract = true := by decide +kernel
def s1613_plain : CertifiedContract :=
  ⟨1613, 1614, 0, (.inc 5), s1613_plain_contract, 382, s1613_plain_checked⟩

def s1614_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s1614_zero_checked : check 402 s1614_zero_contract = true := by decide +kernel
def s1614_zero : CertifiedContract :=
  ⟨1614, 1617, 0, .none, s1614_zero_contract, 402, s1614_zero_checked⟩

def s1614_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1614_positive_checked : check 405 s1614_positive_contract = true := by decide +kernel
def s1614_positive : CertifiedContract :=
  ⟨1614, 1615, 1, (.dec 8), s1614_positive_contract, 405, s1614_positive_checked⟩

def s1615_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1615_plain_checked : check 400 s1615_plain_contract = true := by decide +kernel
def s1615_plain : CertifiedContract :=
  ⟨1615, 1616, 0, (.inc 2), s1615_plain_contract, 400, s1615_plain_checked⟩

def s1616_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1616_plain_checked : check 110 s1616_plain_contract = true := by decide +kernel
def s1616_plain : CertifiedContract :=
  ⟨1616, 1614, 0, .none, s1616_plain_contract, 110, s1616_plain_checked⟩

def s1617_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1617_plain_checked : check 113 s1617_plain_contract = true := by decide +kernel
def s1617_plain : CertifiedContract :=
  ⟨1617, 1608, 0, .none, s1617_plain_contract, 113, s1617_plain_checked⟩

def s1618_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s1618_zero_checked : check 372 s1618_zero_contract = true := by decide +kernel
def s1618_zero : CertifiedContract :=
  ⟨1618, 1621, 0, .none, s1618_zero_contract, 372, s1618_zero_checked⟩

def s1618_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s1618_positive_checked : check 369 s1618_positive_contract = true := by decide +kernel
def s1618_positive : CertifiedContract :=
  ⟨1618, 1619, 1, (.dec 5), s1618_positive_contract, 369, s1618_positive_checked⟩

def s1619_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s1619_plain_checked : check 382 s1619_plain_contract = true := by decide +kernel
def s1619_plain : CertifiedContract :=
  ⟨1619, 1620, 0, (.inc 0), s1619_plain_contract, 382, s1619_plain_checked⟩

def s1620_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s1620_plain_checked : check 101 s1620_plain_contract = true := by decide +kernel
def s1620_plain : CertifiedContract :=
  ⟨1620, 1618, 0, .none, s1620_plain_contract, 101, s1620_plain_checked⟩

def s1621_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s1621_zero_checked : check 336 s1621_zero_contract = true := by decide +kernel
def s1621_zero : CertifiedContract :=
  ⟨1621, 1625, 0, .none, s1621_zero_contract, 336, s1621_zero_checked⟩

def s1621_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, false, true, false] 1 (.dec 7)⟩
theorem s1621_positive_checked : check 342 s1621_positive_contract = true := by decide +kernel
def s1621_positive : CertifiedContract :=
  ⟨1621, 1622, 1, (.dec 7), s1621_positive_contract, 342, s1621_positive_checked⟩

def s1622_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s1622_plain_checked : check 346 s1622_plain_contract = true := by decide +kernel
def s1622_plain : CertifiedContract :=
  ⟨1622, 1623, 0, (.inc 2), s1622_plain_contract, 346, s1622_plain_checked⟩

def s1623_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1623_plain_checked : check 373 s1623_plain_contract = true := by decide +kernel
def s1623_plain : CertifiedContract :=
  ⟨1623, 1624, 0, (.inc 8), s1623_plain_contract, 373, s1623_plain_checked⟩

def s1624_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s1624_plain_checked : check 98 s1624_plain_contract = true := by decide +kernel
def s1624_plain : CertifiedContract :=
  ⟨1624, 1621, 0, .none, s1624_plain_contract, 98, s1624_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S032
