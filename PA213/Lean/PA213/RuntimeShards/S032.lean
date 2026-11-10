import PA213.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S032
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s1575_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s1575_zero_checked : check 344 s1575_zero_contract = true := by decide +kernel
def s1575_zero : CertifiedContract :=
  ⟨1575, 1577, 0, .none, s1575_zero_contract, 344, s1575_zero_checked⟩

def s1575_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s1575_positive_checked : check 350 s1575_positive_contract = true := by decide +kernel
def s1575_positive : CertifiedContract :=
  ⟨1575, 1576, 1, (.dec 8), s1575_positive_contract, 350, s1575_positive_checked⟩

def s1576_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, true] 0 .none⟩
theorem s1576_plain_checked : check 91 s1576_plain_contract = true := by decide +kernel
def s1576_plain : CertifiedContract :=
  ⟨1576, 1580, 0, .none, s1576_plain_contract, 91, s1576_plain_checked⟩

def s1577_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, true] 0 .none⟩
theorem s1577_zero_checked : check 356 s1577_zero_contract = true := by decide +kernel
def s1577_zero : CertifiedContract :=
  ⟨1577, 1580, 0, .none, s1577_zero_contract, 356, s1577_zero_checked⟩

def s1577_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s1577_positive_checked : check 359 s1577_positive_contract = true := by decide +kernel
def s1577_positive : CertifiedContract :=
  ⟨1577, 1578, 1, (.dec 5), s1577_positive_contract, 359, s1577_positive_checked⟩

def s1578_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1578_plain_checked : check 363 s1578_plain_contract = true := by decide +kernel
def s1578_plain : CertifiedContract :=
  ⟨1578, 1579, 0, (.inc 8), s1578_plain_contract, 363, s1578_plain_checked⟩

def s1579_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, false, true, false] 0 .none⟩
theorem s1579_plain_checked : check 94 s1579_plain_contract = true := by decide +kernel
def s1579_plain : CertifiedContract :=
  ⟨1579, 1577, 0, .none, s1579_plain_contract, 94, s1579_plain_checked⟩

def s1580_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, false, false] 0 .none⟩
theorem s1580_plain_checked : check 85 s1580_plain_contract = true := by decide +kernel
def s1580_plain : CertifiedContract :=
  ⟨1580, 1573, 0, .none, s1580_plain_contract, 85, s1580_plain_checked⟩

def s1581_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, false, false] 0 .none⟩
theorem s1581_zero_checked : check 302 s1581_zero_contract = true := by decide +kernel
def s1581_zero : CertifiedContract :=
  ⟨1581, 1584, 0, .none, s1581_zero_contract, 302, s1581_zero_checked⟩

def s1581_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s1581_positive_checked : check 305 s1581_positive_contract = true := by decide +kernel
def s1581_positive : CertifiedContract :=
  ⟨1581, 1582, 1, (.dec 5), s1581_positive_contract, 305, s1581_positive_checked⟩

def s1582_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, true, true, true] 0 (.inc 0)⟩
theorem s1582_plain_checked : check 318 s1582_plain_contract = true := by decide +kernel
def s1582_plain : CertifiedContract :=
  ⟨1582, 1583, 0, (.inc 0), s1582_plain_contract, 318, s1582_plain_checked⟩

def s1583_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, false, true, false] 0 .none⟩
theorem s1583_plain_checked : check 79 s1583_plain_contract = true := by decide +kernel
def s1583_plain : CertifiedContract :=
  ⟨1583, 1581, 0, .none, s1583_plain_contract, 79, s1583_plain_checked⟩

def s1584_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, false] 0 .none⟩
theorem s1584_zero_checked : check 299 s1584_zero_contract = true := by decide +kernel
def s1584_zero : CertifiedContract :=
  ⟨1584, 1588, 0, .none, s1584_zero_contract, 299, s1584_zero_checked⟩

def s1584_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1584_positive_checked : check 305 s1584_positive_contract = true := by decide +kernel
def s1584_positive : CertifiedContract :=
  ⟨1584, 1585, 1, (.dec 2), s1584_positive_contract, 305, s1584_positive_checked⟩

def s1585_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1585_plain_checked : check 318 s1585_plain_contract = true := by decide +kernel
def s1585_plain : CertifiedContract :=
  ⟨1585, 1586, 0, (.inc 5), s1585_plain_contract, 318, s1585_plain_checked⟩

def s1586_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1586_plain_checked : check 345 s1586_plain_contract = true := by decide +kernel
def s1586_plain : CertifiedContract :=
  ⟨1586, 1587, 0, (.inc 8), s1586_plain_contract, 345, s1586_plain_checked⟩

def s1587_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, false, false] 0 .none⟩
theorem s1587_plain_checked : check 88 s1587_plain_contract = true := by decide +kernel
def s1587_plain : CertifiedContract :=
  ⟨1587, 1584, 0, .none, s1587_plain_contract, 88, s1587_plain_checked⟩

def s1588_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, true, false] 0 .none⟩
theorem s1588_zero_checked : check 320 s1588_zero_contract = true := by decide +kernel
def s1588_zero : CertifiedContract :=
  ⟨1588, 1594, 0, .none, s1588_zero_contract, 320, s1588_zero_checked⟩

def s1588_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1588_positive_checked : check 323 s1588_positive_contract = true := by decide +kernel
def s1588_positive : CertifiedContract :=
  ⟨1588, 1589, 1, (.dec 8), s1588_positive_contract, 323, s1588_positive_checked⟩

def s1589_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1589_plain_checked : check 318 s1589_plain_contract = true := by decide +kernel
def s1589_plain : CertifiedContract :=
  ⟨1589, 1590, 0, (.inc 5), s1589_plain_contract, 318, s1589_plain_checked⟩

def s1590_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, true, true] 0 .none⟩
theorem s1590_zero_checked : check 338 s1590_zero_contract = true := by decide +kernel
def s1590_zero : CertifiedContract :=
  ⟨1590, 1593, 0, .none, s1590_zero_contract, 338, s1590_zero_checked⟩

def s1590_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1590_positive_checked : check 341 s1590_positive_contract = true := by decide +kernel
def s1590_positive : CertifiedContract :=
  ⟨1590, 1591, 1, (.dec 8), s1590_positive_contract, 341, s1590_positive_checked⟩

def s1591_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1591_plain_checked : check 336 s1591_plain_contract = true := by decide +kernel
def s1591_plain : CertifiedContract :=
  ⟨1591, 1592, 0, (.inc 2), s1591_plain_contract, 336, s1591_plain_checked⟩

def s1592_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1592_plain_checked : check 88 s1592_plain_contract = true := by decide +kernel
def s1592_plain : CertifiedContract :=
  ⟨1592, 1590, 0, .none, s1592_plain_contract, 88, s1592_plain_checked⟩

def s1593_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, false, false, false] 0 .none⟩
theorem s1593_plain_checked : check 91 s1593_plain_contract = true := by decide +kernel
def s1593_plain : CertifiedContract :=
  ⟨1593, 1584, 0, .none, s1593_plain_contract, 91, s1593_plain_checked⟩

def s1594_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s1594_zero_checked : check 314 s1594_zero_contract = true := by decide +kernel
def s1594_zero : CertifiedContract :=
  ⟨1594, 1600, 0, .none, s1594_zero_contract, 314, s1594_zero_checked⟩

def s1594_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s1594_positive_checked : check 305 s1594_positive_contract = true := by decide +kernel
def s1594_positive : CertifiedContract :=
  ⟨1594, 1595, 1, (.dec 5), s1594_positive_contract, 305, s1594_positive_checked⟩

def s1595_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s1595_plain_checked : check 318 s1595_plain_contract = true := by decide +kernel
def s1595_plain : CertifiedContract :=
  ⟨1595, 1596, 0, (.inc 2), s1595_plain_contract, 318, s1595_plain_checked⟩

def s1596_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s1596_plain_checked : check 321 s1596_plain_contract = true := by decide +kernel
def s1596_plain : CertifiedContract :=
  ⟨1596, 1597, 0, (.inc 2), s1596_plain_contract, 321, s1596_plain_checked⟩

def s1597_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s1597_plain_checked : check 318 s1597_plain_contract = true := by decide +kernel
def s1597_plain : CertifiedContract :=
  ⟨1597, 1598, 0, (.inc 2), s1597_plain_contract, 318, s1597_plain_checked⟩

def s1598_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, true, true, true] 0 (.inc 2)⟩
theorem s1598_plain_checked : check 324 s1598_plain_contract = true := by decide +kernel
def s1598_plain : CertifiedContract :=
  ⟨1598, 1599, 0, (.inc 2), s1598_plain_contract, 324, s1598_plain_checked⟩

def s1599_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, false, true, true, true, true, true, false] 0 .none⟩
theorem s1599_plain_checked : check 76 s1599_plain_contract = true := by decide +kernel
def s1599_plain : CertifiedContract :=
  ⟨1599, 1594, 0, .none, s1599_plain_contract, 76, s1599_plain_checked⟩

def s1600_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, false, true] 0 (.inc 2)⟩
theorem s1600_plain_checked : check 291 s1600_plain_contract = true := by decide +kernel
def s1600_plain : CertifiedContract :=
  ⟨1600, 1601, 0, (.inc 2), s1600_plain_contract, 291, s1600_plain_checked⟩

def s1601_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, false, false] 0 (.inc 2)⟩
theorem s1601_plain_checked : check 294 s1601_plain_contract = true := by decide +kernel
def s1601_plain : CertifiedContract :=
  ⟨1601, 1602, 0, (.inc 2), s1601_plain_contract, 294, s1601_plain_checked⟩

def s1602_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s1602_zero_checked : check 335 s1602_zero_contract = true := by decide +kernel
def s1602_zero : CertifiedContract :=
  ⟨1602, 1605, 0, .none, s1602_zero_contract, 335, s1602_zero_checked⟩

def s1602_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s1602_positive_checked : check 341 s1602_positive_contract = true := by decide +kernel
def s1602_positive : CertifiedContract :=
  ⟨1602, 1603, 1, (.dec 2), s1602_positive_contract, 341, s1602_positive_checked⟩

def s1603_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s1603_plain_checked : check 354 s1603_plain_contract = true := by decide +kernel
def s1603_plain : CertifiedContract :=
  ⟨1603, 1604, 0, (.inc 8), s1603_plain_contract, 354, s1603_plain_checked⟩

def s1604_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s1604_plain_checked : check 91 s1604_plain_contract = true := by decide +kernel
def s1604_plain : CertifiedContract :=
  ⟨1604, 1602, 0, .none, s1604_plain_contract, 91, s1604_plain_checked⟩

def s1605_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1605_zero_checked : check 356 s1605_zero_contract = true := by decide +kernel
def s1605_zero : CertifiedContract :=
  ⟨1605, 1608, 0, .none, s1605_zero_contract, 356, s1605_zero_checked⟩

def s1605_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s1605_positive_checked : check 362 s1605_positive_contract = true := by decide +kernel
def s1605_positive : CertifiedContract :=
  ⟨1605, 1606, 1, (.dec 0), s1605_positive_contract, 362, s1605_positive_checked⟩

def s1606_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s1606_plain_checked : check 354 s1606_plain_contract = true := by decide +kernel
def s1606_plain : CertifiedContract :=
  ⟨1606, 1607, 0, (.inc 2), s1606_plain_contract, 354, s1606_plain_checked⟩

def s1607_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s1607_plain_checked : check 94 s1607_plain_contract = true := by decide +kernel
def s1607_plain : CertifiedContract :=
  ⟨1607, 1605, 0, .none, s1607_plain_contract, 94, s1607_plain_checked⟩

def s1608_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1608_zero_checked : check 362 s1608_zero_contract = true := by decide +kernel
def s1608_zero : CertifiedContract :=
  ⟨1608, 1612, 0, .none, s1608_zero_contract, 362, s1608_zero_checked⟩

def s1608_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1608_positive_checked : check 368 s1608_positive_contract = true := by decide +kernel
def s1608_positive : CertifiedContract :=
  ⟨1608, 1609, 1, (.dec 2), s1608_positive_contract, 368, s1608_positive_checked⟩

def s1609_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1609_plain_checked : check 381 s1609_plain_contract = true := by decide +kernel
def s1609_plain : CertifiedContract :=
  ⟨1609, 1610, 0, (.inc 5), s1609_plain_contract, 381, s1609_plain_checked⟩

def s1610_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1610_plain_checked : check 408 s1610_plain_contract = true := by decide +kernel
def s1610_plain : CertifiedContract :=
  ⟨1610, 1611, 0, (.inc 8), s1610_plain_contract, 408, s1610_plain_checked⟩

def s1611_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1611_plain_checked : check 109 s1611_plain_contract = true := by decide +kernel
def s1611_plain : CertifiedContract :=
  ⟨1611, 1608, 0, .none, s1611_plain_contract, 109, s1611_plain_checked⟩

def s1612_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s1612_zero_checked : check 383 s1612_zero_contract = true := by decide +kernel
def s1612_zero : CertifiedContract :=
  ⟨1612, 1618, 0, .none, s1612_zero_contract, 383, s1612_zero_checked⟩

def s1612_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1612_positive_checked : check 386 s1612_positive_contract = true := by decide +kernel
def s1612_positive : CertifiedContract :=
  ⟨1612, 1613, 1, (.dec 8), s1612_positive_contract, 386, s1612_positive_checked⟩

def s1613_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1613_plain_checked : check 381 s1613_plain_contract = true := by decide +kernel
def s1613_plain : CertifiedContract :=
  ⟨1613, 1614, 0, (.inc 5), s1613_plain_contract, 381, s1613_plain_checked⟩

def s1614_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s1614_zero_checked : check 401 s1614_zero_contract = true := by decide +kernel
def s1614_zero : CertifiedContract :=
  ⟨1614, 1617, 0, .none, s1614_zero_contract, 401, s1614_zero_checked⟩

def s1614_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1614_positive_checked : check 404 s1614_positive_contract = true := by decide +kernel
def s1614_positive : CertifiedContract :=
  ⟨1614, 1615, 1, (.dec 8), s1614_positive_contract, 404, s1614_positive_checked⟩

def s1615_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1615_plain_checked : check 399 s1615_plain_contract = true := by decide +kernel
def s1615_plain : CertifiedContract :=
  ⟨1615, 1616, 0, (.inc 2), s1615_plain_contract, 399, s1615_plain_checked⟩

def s1616_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1616_plain_checked : check 109 s1616_plain_contract = true := by decide +kernel
def s1616_plain : CertifiedContract :=
  ⟨1616, 1614, 0, .none, s1616_plain_contract, 109, s1616_plain_checked⟩

def s1617_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1617_plain_checked : check 112 s1617_plain_contract = true := by decide +kernel
def s1617_plain : CertifiedContract :=
  ⟨1617, 1608, 0, .none, s1617_plain_contract, 112, s1617_plain_checked⟩

def s1618_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s1618_zero_checked : check 371 s1618_zero_contract = true := by decide +kernel
def s1618_zero : CertifiedContract :=
  ⟨1618, 1621, 0, .none, s1618_zero_contract, 371, s1618_zero_checked⟩

def s1618_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s1618_positive_checked : check 368 s1618_positive_contract = true := by decide +kernel
def s1618_positive : CertifiedContract :=
  ⟨1618, 1619, 1, (.dec 5), s1618_positive_contract, 368, s1618_positive_checked⟩

def s1619_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s1619_plain_checked : check 381 s1619_plain_contract = true := by decide +kernel
def s1619_plain : CertifiedContract :=
  ⟨1619, 1620, 0, (.inc 0), s1619_plain_contract, 381, s1619_plain_checked⟩

def s1620_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s1620_plain_checked : check 100 s1620_plain_contract = true := by decide +kernel
def s1620_plain : CertifiedContract :=
  ⟨1620, 1618, 0, .none, s1620_plain_contract, 100, s1620_plain_checked⟩

def s1621_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s1621_zero_checked : check 335 s1621_zero_contract = true := by decide +kernel
def s1621_zero : CertifiedContract :=
  ⟨1621, 1625, 0, .none, s1621_zero_contract, 335, s1621_zero_checked⟩

def s1621_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, false, true, false] 1 (.dec 7)⟩
theorem s1621_positive_checked : check 341 s1621_positive_contract = true := by decide +kernel
def s1621_positive : CertifiedContract :=
  ⟨1621, 1622, 1, (.dec 7), s1621_positive_contract, 341, s1621_positive_checked⟩

def s1622_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s1622_plain_checked : check 345 s1622_plain_contract = true := by decide +kernel
def s1622_plain : CertifiedContract :=
  ⟨1622, 1623, 0, (.inc 2), s1622_plain_contract, 345, s1622_plain_checked⟩

def s1623_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1623_plain_checked : check 372 s1623_plain_contract = true := by decide +kernel
def s1623_plain : CertifiedContract :=
  ⟨1623, 1624, 0, (.inc 8), s1623_plain_contract, 372, s1623_plain_checked⟩

def s1624_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s1624_plain_checked : check 97 s1624_plain_contract = true := by decide +kernel
def s1624_plain : CertifiedContract :=
  ⟨1624, 1621, 0, .none, s1624_plain_contract, 97, s1624_plain_checked⟩

def nonterminal : Array CertifiedContract := #[
  s1575_zero,
  s1575_positive,
  s1576_plain,
  s1577_zero,
  s1577_positive,
  s1578_plain,
  s1579_plain,
  s1580_plain,
  s1581_zero,
  s1581_positive,
  s1582_plain,
  s1583_plain,
  s1584_zero,
  s1584_positive,
  s1585_plain,
  s1586_plain,
  s1587_plain,
  s1588_zero,
  s1588_positive,
  s1589_plain,
  s1590_zero,
  s1590_positive,
  s1591_plain,
  s1592_plain,
  s1593_plain,
  s1594_zero,
  s1594_positive,
  s1595_plain,
  s1596_plain,
  s1597_plain,
  s1598_plain,
  s1599_plain,
  s1600_plain,
  s1601_plain,
  s1602_zero,
  s1602_positive,
  s1603_plain,
  s1604_plain,
  s1605_zero,
  s1605_positive,
  s1606_plain,
  s1607_plain,
  s1608_zero,
  s1608_positive,
  s1609_plain,
  s1610_plain,
  s1611_plain,
  s1612_zero,
  s1612_positive,
  s1613_plain,
  s1614_zero,
  s1614_positive,
  s1615_plain,
  s1616_plain,
  s1617_plain,
  s1618_zero,
  s1618_positive,
  s1619_plain,
  s1620_plain,
  s1621_zero,
  s1621_positive,
  s1622_plain,
  s1623_plain,
  s1624_plain
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S032
