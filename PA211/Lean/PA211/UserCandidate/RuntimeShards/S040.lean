import PA211.UserCandidate.RuntimeContracts
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S040
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s1970_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s1970_plain_checked : check 400 s1970_plain_contract = true := by decide +kernel
def s1970_plain : CertifiedContract :=
  ⟨1970, 1971, 0, (.inc 0), s1970_plain_contract, 400, s1970_plain_checked⟩

def s1971_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, true, false] 0 .none⟩
theorem s1971_plain_checked : check 107 s1971_plain_contract = true := by decide +kernel
def s1971_plain : CertifiedContract :=
  ⟨1971, 1969, 0, .none, s1971_plain_contract, 107, s1971_plain_checked⟩

def s1972_zero_contract : Contract :=
  ⟨(some (7, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s1972_zero_checked : check 354 s1972_zero_contract = true := by decide +kernel
def s1972_zero : CertifiedContract :=
  ⟨1972, 1976, 0, .none, s1972_zero_contract, 354, s1972_zero_checked⟩

def s1972_positive_contract : Contract :=
  ⟨(some (7, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, true, false, true, false] 1 (.dec 7)⟩
theorem s1972_positive_checked : check 360 s1972_positive_contract = true := by decide +kernel
def s1972_positive : CertifiedContract :=
  ⟨1972, 1973, 1, (.dec 7), s1972_positive_contract, 360, s1972_positive_checked⟩

def s1973_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s1973_plain_checked : check 364 s1973_plain_contract = true := by decide +kernel
def s1973_plain : CertifiedContract :=
  ⟨1973, 1974, 0, (.inc 2), s1973_plain_contract, 364, s1973_plain_checked⟩

def s1974_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1974_plain_checked : check 391 s1974_plain_contract = true := by decide +kernel
def s1974_plain : CertifiedContract :=
  ⟨1974, 1975, 0, (.inc 8), s1974_plain_contract, 391, s1974_plain_checked⟩

def s1975_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, true, false, false] 0 .none⟩
theorem s1975_plain_checked : check 104 s1975_plain_contract = true := by decide +kernel
def s1975_plain : CertifiedContract :=
  ⟨1975, 1972, 0, .none, s1975_plain_contract, 104, s1975_plain_checked⟩

def s1976_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, false, false] 0 .none⟩
theorem s1976_zero_checked : check 363 s1976_zero_contract = true := by decide +kernel
def s1976_zero : CertifiedContract :=
  ⟨1976, 1979, 0, .none, s1976_zero_contract, 363, s1976_zero_checked⟩

def s1976_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s1976_positive_checked : check 360 s1976_positive_contract = true := by decide +kernel
def s1976_positive : CertifiedContract :=
  ⟨1976, 1977, 1, (.dec 8), s1976_positive_contract, 360, s1976_positive_checked⟩

def s1977_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, true, true, true, true] 0 (.inc 7)⟩
theorem s1977_plain_checked : check 391 s1977_plain_contract = true := by decide +kernel
def s1977_plain : CertifiedContract :=
  ⟨1977, 1978, 0, (.inc 7), s1977_plain_contract, 391, s1977_plain_checked⟩

def s1978_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, true, true, false] 0 .none⟩
theorem s1978_plain_checked : check 98 s1978_plain_contract = true := by decide +kernel
def s1978_plain : CertifiedContract :=
  ⟨1978, 1976, 0, .none, s1978_plain_contract, 98, s1978_plain_checked⟩

def s1979_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, true, false] 0 .none⟩
theorem s1979_zero_checked : check 366 s1979_zero_contract = true := by decide +kernel
def s1979_zero : CertifiedContract :=
  ⟨1979, 1987, 0, .none, s1979_zero_contract, 366, s1979_zero_checked⟩

def s1979_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s1979_positive_checked : check 372 s1979_positive_contract = true := by decide +kernel
def s1979_positive : CertifiedContract :=
  ⟨1979, 1980, 1, (.dec 0), s1979_positive_contract, 372, s1979_positive_checked⟩

def s1980_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s1980_plain_checked : check 382 s1980_plain_contract = true := by decide +kernel
def s1980_plain : CertifiedContract :=
  ⟨1980, 1981, 0, (.inc 5), s1980_plain_contract, 382, s1980_plain_checked⟩

def s1981_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1981_zero_checked : check 408 s1981_zero_contract = true := by decide +kernel
def s1981_zero : CertifiedContract :=
  ⟨1981, 1983, 0, .none, s1981_zero_contract, 408, s1981_zero_checked⟩

def s1981_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s1981_positive_checked : check 414 s1981_positive_contract = true := by decide +kernel
def s1981_positive : CertifiedContract :=
  ⟨1981, 1982, 1, (.dec 8), s1981_positive_contract, 414, s1981_positive_checked⟩

def s1982_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, false, true, true, true] 0 .none⟩
theorem s1982_plain_checked : check 113 s1982_plain_contract = true := by decide +kernel
def s1982_plain : CertifiedContract :=
  ⟨1982, 1986, 0, .none, s1982_plain_contract, 113, s1982_plain_checked⟩

def s1983_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, false, true, true, true] 0 .none⟩
theorem s1983_zero_checked : check 420 s1983_zero_contract = true := by decide +kernel
def s1983_zero : CertifiedContract :=
  ⟨1983, 1986, 0, .none, s1983_zero_contract, 420, s1983_zero_checked⟩

def s1983_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s1983_positive_checked : check 423 s1983_positive_contract = true := by decide +kernel
def s1983_positive : CertifiedContract :=
  ⟨1983, 1984, 1, (.dec 5), s1983_positive_contract, 423, s1983_positive_checked⟩

def s1984_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1984_plain_checked : check 427 s1984_plain_contract = true := by decide +kernel
def s1984_plain : CertifiedContract :=
  ⟨1984, 1985, 0, (.inc 8), s1984_plain_contract, 427, s1984_plain_checked⟩

def s1985_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1985_plain_checked : check 116 s1985_plain_contract = true := by decide +kernel
def s1985_plain : CertifiedContract :=
  ⟨1985, 1983, 0, .none, s1985_plain_contract, 116, s1985_plain_checked⟩

def s1986_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, false, false] 0 .none⟩
theorem s1986_plain_checked : check 107 s1986_plain_contract = true := by decide +kernel
def s1986_plain : CertifiedContract :=
  ⟨1986, 1979, 0, .none, s1986_plain_contract, 107, s1986_plain_checked⟩

def s1987_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s1987_zero_checked : check 366 s1987_zero_contract = true := by decide +kernel
def s1987_zero : CertifiedContract :=
  ⟨1987, 1990, 0, .none, s1987_zero_contract, 366, s1987_zero_checked⟩

def s1987_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s1987_positive_checked : check 369 s1987_positive_contract = true := by decide +kernel
def s1987_positive : CertifiedContract :=
  ⟨1987, 1988, 1, (.dec 5), s1987_positive_contract, 369, s1987_positive_checked⟩

def s1988_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s1988_plain_checked : check 382 s1988_plain_contract = true := by decide +kernel
def s1988_plain : CertifiedContract :=
  ⟨1988, 1989, 0, (.inc 0), s1988_plain_contract, 382, s1988_plain_checked⟩

def s1989_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, false, true, false] 0 .none⟩
theorem s1989_plain_checked : check 101 s1989_plain_contract = true := by decide +kernel
def s1989_plain : CertifiedContract :=
  ⟨1989, 1987, 0, .none, s1989_plain_contract, 101, s1989_plain_checked⟩

def s1990_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, false, true, false] 0 .none⟩
theorem s1990_zero_checked : check 363 s1990_zero_contract = true := by decide +kernel
def s1990_zero : CertifiedContract :=
  ⟨1990, 1994, 0, .none, s1990_zero_contract, 363, s1990_zero_checked⟩

def s1990_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1990_positive_checked : check 369 s1990_positive_contract = true := by decide +kernel
def s1990_positive : CertifiedContract :=
  ⟨1990, 1991, 1, (.dec 2), s1990_positive_contract, 369, s1990_positive_checked⟩

def s1991_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1991_plain_checked : check 382 s1991_plain_contract = true := by decide +kernel
def s1991_plain : CertifiedContract :=
  ⟨1991, 1992, 0, (.inc 5), s1991_plain_contract, 382, s1991_plain_checked⟩

def s1992_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1992_plain_checked : check 409 s1992_plain_contract = true := by decide +kernel
def s1992_plain : CertifiedContract :=
  ⟨1992, 1993, 0, (.inc 8), s1992_plain_contract, 409, s1992_plain_checked⟩

def s1993_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s1993_plain_checked : check 110 s1993_plain_contract = true := by decide +kernel
def s1993_plain : CertifiedContract :=
  ⟨1993, 1990, 0, .none, s1993_plain_contract, 110, s1993_plain_checked⟩

def s1994_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, true, false] 0 .none⟩
theorem s1994_zero_checked : check 384 s1994_zero_contract = true := by decide +kernel
def s1994_zero : CertifiedContract :=
  ⟨1994, 2000, 0, .none, s1994_zero_contract, 384, s1994_zero_checked⟩

def s1994_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1994_positive_checked : check 387 s1994_positive_contract = true := by decide +kernel
def s1994_positive : CertifiedContract :=
  ⟨1994, 1995, 1, (.dec 8), s1994_positive_contract, 387, s1994_positive_checked⟩

def s1995_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1995_plain_checked : check 382 s1995_plain_contract = true := by decide +kernel
def s1995_plain : CertifiedContract :=
  ⟨1995, 1996, 0, (.inc 5), s1995_plain_contract, 382, s1995_plain_checked⟩

def s1996_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, false, true, true, true] 0 .none⟩
theorem s1996_zero_checked : check 402 s1996_zero_contract = true := by decide +kernel
def s1996_zero : CertifiedContract :=
  ⟨1996, 1999, 0, .none, s1996_zero_contract, 402, s1996_zero_checked⟩

def s1996_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1996_positive_checked : check 405 s1996_positive_contract = true := by decide +kernel
def s1996_positive : CertifiedContract :=
  ⟨1996, 1997, 1, (.dec 8), s1996_positive_contract, 405, s1996_positive_checked⟩

def s1997_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1997_plain_checked : check 400 s1997_plain_contract = true := by decide +kernel
def s1997_plain : CertifiedContract :=
  ⟨1997, 1998, 0, (.inc 2), s1997_plain_contract, 400, s1997_plain_checked⟩

def s1998_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s1998_plain_checked : check 110 s1998_plain_contract = true := by decide +kernel
def s1998_plain : CertifiedContract :=
  ⟨1998, 1996, 0, .none, s1998_plain_contract, 110, s1998_plain_checked⟩

def s1999_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, false, false, false] 0 .none⟩
theorem s1999_plain_checked : check 113 s1999_plain_contract = true := by decide +kernel
def s1999_plain : CertifiedContract :=
  ⟨1999, 1990, 0, .none, s1999_plain_contract, 113, s1999_plain_checked⟩

def s2000_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, true] 0 .none⟩
theorem s2000_zero_checked : check 369 s2000_zero_contract = true := by decide +kernel
def s2000_zero : CertifiedContract :=
  ⟨2000, 2006, 0, .none, s2000_zero_contract, 369, s2000_zero_checked⟩

def s2000_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s2000_positive_checked : check 369 s2000_positive_contract = true := by decide +kernel
def s2000_positive : CertifiedContract :=
  ⟨2000, 2001, 1, (.dec 5), s2000_positive_contract, 369, s2000_positive_checked⟩

def s2001_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s2001_plain_checked : check 382 s2001_plain_contract = true := by decide +kernel
def s2001_plain : CertifiedContract :=
  ⟨2001, 2002, 0, (.inc 2), s2001_plain_contract, 382, s2001_plain_checked⟩

def s2002_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s2002_plain_checked : check 385 s2002_plain_contract = true := by decide +kernel
def s2002_plain : CertifiedContract :=
  ⟨2002, 2003, 0, (.inc 2), s2002_plain_contract, 385, s2002_plain_checked⟩

def s2003_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s2003_plain_checked : check 391 s2003_plain_contract = true := by decide +kernel
def s2003_plain : CertifiedContract :=
  ⟨2003, 2004, 0, (.inc 2), s2003_plain_contract, 391, s2003_plain_checked⟩

def s2004_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s2004_plain_checked : check 397 s2004_plain_contract = true := by decide +kernel
def s2004_plain : CertifiedContract :=
  ⟨2004, 2005, 0, (.inc 2), s2004_plain_contract, 397, s2004_plain_checked⟩

def s2005_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, false, true, true, false] 0 .none⟩
theorem s2005_plain_checked : check 98 s2005_plain_contract = true := by decide +kernel
def s2005_plain : CertifiedContract :=
  ⟨2005, 2000, 0, .none, s2005_plain_contract, 98, s2005_plain_checked⟩

def s2006_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, false, false] 0 (.inc 2)⟩
theorem s2006_plain_checked : check 349 s2006_plain_contract = true := by decide +kernel
def s2006_plain : CertifiedContract :=
  ⟨2006, 2007, 0, (.inc 2), s2006_plain_contract, 349, s2006_plain_checked⟩

def s2007_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, true, false] 0 .none⟩
theorem s2007_zero_checked : check 375 s2007_zero_contract = true := by decide +kernel
def s2007_zero : CertifiedContract :=
  ⟨2007, 2015, 0, .none, s2007_zero_contract, 375, s2007_zero_checked⟩

def s2007_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, false, true, false] 1 (.dec 0)⟩
theorem s2007_positive_checked : check 381 s2007_positive_contract = true := by decide +kernel
def s2007_positive : CertifiedContract :=
  ⟨2007, 2008, 1, (.dec 0), s2007_positive_contract, 381, s2007_positive_checked⟩

def s2008_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s2008_plain_checked : check 391 s2008_plain_contract = true := by decide +kernel
def s2008_plain : CertifiedContract :=
  ⟨2008, 2009, 0, (.inc 5), s2008_plain_contract, 391, s2008_plain_checked⟩

def s2009_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2009_zero_checked : check 417 s2009_zero_contract = true := by decide +kernel
def s2009_zero : CertifiedContract :=
  ⟨2009, 2011, 0, .none, s2009_zero_contract, 417, s2009_zero_checked⟩

def s2009_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s2009_positive_checked : check 423 s2009_positive_contract = true := by decide +kernel
def s2009_positive : CertifiedContract :=
  ⟨2009, 2010, 1, (.dec 8), s2009_positive_contract, 423, s2009_positive_checked⟩

def s2010_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, false, true, true, true] 0 .none⟩
theorem s2010_plain_checked : check 116 s2010_plain_contract = true := by decide +kernel
def s2010_plain : CertifiedContract :=
  ⟨2010, 2014, 0, .none, s2010_plain_contract, 116, s2010_plain_checked⟩

def s2011_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, false, true, true, true] 0 .none⟩
theorem s2011_zero_checked : check 429 s2011_zero_contract = true := by decide +kernel
def s2011_zero : CertifiedContract :=
  ⟨2011, 2014, 0, .none, s2011_zero_contract, 429, s2011_zero_checked⟩

def s2011_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s2011_positive_checked : check 432 s2011_positive_contract = true := by decide +kernel
def s2011_positive : CertifiedContract :=
  ⟨2011, 2012, 1, (.dec 5), s2011_positive_contract, 432, s2011_positive_checked⟩

def s2012_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s2012_plain_checked : check 436 s2012_plain_contract = true := by decide +kernel
def s2012_plain : CertifiedContract :=
  ⟨2012, 2013, 0, (.inc 8), s2012_plain_contract, 436, s2012_plain_checked⟩

def s2013_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s2013_plain_checked : check 119 s2013_plain_contract = true := by decide +kernel
def s2013_plain : CertifiedContract :=
  ⟨2013, 2011, 0, .none, s2013_plain_contract, 119, s2013_plain_checked⟩

def s2014_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, false, false] 0 .none⟩
theorem s2014_plain_checked : check 110 s2014_plain_contract = true := by decide +kernel
def s2014_plain : CertifiedContract :=
  ⟨2014, 2007, 0, .none, s2014_plain_contract, 110, s2014_plain_checked⟩

def s2015_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, false, false] 0 .none⟩
theorem s2015_zero_checked : check 375 s2015_zero_contract = true := by decide +kernel
def s2015_zero : CertifiedContract :=
  ⟨2015, 2018, 0, .none, s2015_zero_contract, 375, s2015_zero_checked⟩

def s2015_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, true, true, false] 1 (.dec 5)⟩
theorem s2015_positive_checked : check 378 s2015_positive_contract = true := by decide +kernel
def s2015_positive : CertifiedContract :=
  ⟨2015, 2016, 1, (.dec 5), s2015_positive_contract, 378, s2015_positive_checked⟩

def s2016_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, true, true, true] 0 (.inc 0)⟩
theorem s2016_plain_checked : check 391 s2016_plain_contract = true := by decide +kernel
def s2016_plain : CertifiedContract :=
  ⟨2016, 2017, 0, (.inc 0), s2016_plain_contract, 391, s2016_plain_checked⟩

def s2017_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, false, true, false] 0 .none⟩
theorem s2017_plain_checked : check 104 s2017_plain_contract = true := by decide +kernel
def s2017_plain : CertifiedContract :=
  ⟨2017, 2015, 0, .none, s2017_plain_contract, 104, s2017_plain_checked⟩

def s2018_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, true, false] 0 .none⟩
theorem s2018_zero_checked : check 372 s2018_zero_contract = true := by decide +kernel
def s2018_zero : CertifiedContract :=
  ⟨2018, 2022, 0, .none, s2018_zero_contract, 372, s2018_zero_checked⟩

def s2018_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, true, false, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s2018_positive_checked : check 378 s2018_positive_contract = true := by decide +kernel
def s2018_positive : CertifiedContract :=
  ⟨2018, 2019, 1, (.dec 2), s2018_positive_contract, 378, s2018_positive_checked⟩

end PA211.UserCandidate.RuntimeShards.S040
