module

public import PA211.UserCandidate.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S037
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s1821_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s1821_positive_checked : check 459 s1821_positive_contract = true := by decide +kernel
def s1821_positive : CertifiedContract :=
  ⟨1821, 1822, 1, (.dec 5), s1821_positive_contract, 459, s1821_positive_checked⟩

def s1822_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1822_plain_checked : check 463 s1822_plain_contract = true := by decide +kernel
def s1822_plain : CertifiedContract :=
  ⟨1822, 1823, 0, (.inc 8), s1822_plain_contract, 463, s1822_plain_checked⟩

def s1823_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1823_plain_checked : check 128 s1823_plain_contract = true := by decide +kernel
def s1823_plain : CertifiedContract :=
  ⟨1823, 1821, 0, .none, s1823_plain_contract, 128, s1823_plain_checked⟩

def s1824_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, false, false] 0 .none⟩
theorem s1824_plain_checked : check 119 s1824_plain_contract = true := by decide +kernel
def s1824_plain : CertifiedContract :=
  ⟨1824, 1817, 0, .none, s1824_plain_contract, 119, s1824_plain_checked⟩

def s1825_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s1825_zero_checked : check 402 s1825_zero_contract = true := by decide +kernel
def s1825_zero : CertifiedContract :=
  ⟨1825, 1828, 0, .none, s1825_zero_contract, 402, s1825_zero_checked⟩

def s1825_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s1825_positive_checked : check 405 s1825_positive_contract = true := by decide +kernel
def s1825_positive : CertifiedContract :=
  ⟨1825, 1826, 1, (.dec 5), s1825_positive_contract, 405, s1825_positive_checked⟩

def s1826_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s1826_plain_checked : check 418 s1826_plain_contract = true := by decide +kernel
def s1826_plain : CertifiedContract :=
  ⟨1826, 1827, 0, (.inc 0), s1826_plain_contract, 418, s1826_plain_checked⟩

def s1827_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, false, true, false] 0 .none⟩
theorem s1827_plain_checked : check 113 s1827_plain_contract = true := by decide +kernel
def s1827_plain : CertifiedContract :=
  ⟨1827, 1825, 0, .none, s1827_plain_contract, 113, s1827_plain_checked⟩

def s1828_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s1828_zero_checked : check 399 s1828_zero_contract = true := by decide +kernel
def s1828_zero : CertifiedContract :=
  ⟨1828, 1832, 0, .none, s1828_zero_contract, 399, s1828_zero_checked⟩

def s1828_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1828_positive_checked : check 405 s1828_positive_contract = true := by decide +kernel
def s1828_positive : CertifiedContract :=
  ⟨1828, 1829, 1, (.dec 2), s1828_positive_contract, 405, s1828_positive_checked⟩

def s1829_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1829_plain_checked : check 418 s1829_plain_contract = true := by decide +kernel
def s1829_plain : CertifiedContract :=
  ⟨1829, 1830, 0, (.inc 5), s1829_plain_contract, 418, s1829_plain_checked⟩

def s1830_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1830_plain_checked : check 445 s1830_plain_contract = true := by decide +kernel
def s1830_plain : CertifiedContract :=
  ⟨1830, 1831, 0, (.inc 8), s1830_plain_contract, 445, s1830_plain_checked⟩

def s1831_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s1831_plain_checked : check 122 s1831_plain_contract = true := by decide +kernel
def s1831_plain : CertifiedContract :=
  ⟨1831, 1828, 0, .none, s1831_plain_contract, 122, s1831_plain_checked⟩

def s1832_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s1832_zero_checked : check 420 s1832_zero_contract = true := by decide +kernel
def s1832_zero : CertifiedContract :=
  ⟨1832, 1838, 0, .none, s1832_zero_contract, 420, s1832_zero_checked⟩

def s1832_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1832_positive_checked : check 423 s1832_positive_contract = true := by decide +kernel
def s1832_positive : CertifiedContract :=
  ⟨1832, 1833, 1, (.dec 8), s1832_positive_contract, 423, s1832_positive_checked⟩

def s1833_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1833_plain_checked : check 418 s1833_plain_contract = true := by decide +kernel
def s1833_plain : CertifiedContract :=
  ⟨1833, 1834, 0, (.inc 5), s1833_plain_contract, 418, s1833_plain_checked⟩

def s1834_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s1834_zero_checked : check 438 s1834_zero_contract = true := by decide +kernel
def s1834_zero : CertifiedContract :=
  ⟨1834, 1837, 0, .none, s1834_zero_contract, 438, s1834_zero_checked⟩

def s1834_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1834_positive_checked : check 441 s1834_positive_contract = true := by decide +kernel
def s1834_positive : CertifiedContract :=
  ⟨1834, 1835, 1, (.dec 8), s1834_positive_contract, 441, s1834_positive_checked⟩

def s1835_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1835_plain_checked : check 436 s1835_plain_contract = true := by decide +kernel
def s1835_plain : CertifiedContract :=
  ⟨1835, 1836, 0, (.inc 2), s1835_plain_contract, 436, s1835_plain_checked⟩

def s1836_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s1836_plain_checked : check 122 s1836_plain_contract = true := by decide +kernel
def s1836_plain : CertifiedContract :=
  ⟨1836, 1834, 0, .none, s1836_plain_contract, 122, s1836_plain_checked⟩

def s1837_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s1837_plain_checked : check 125 s1837_plain_contract = true := by decide +kernel
def s1837_plain : CertifiedContract :=
  ⟨1837, 1828, 0, .none, s1837_plain_contract, 125, s1837_plain_checked⟩

def s1838_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, true, false] 0 .none⟩
theorem s1838_zero_checked : check 405 s1838_zero_contract = true := by decide +kernel
def s1838_zero : CertifiedContract :=
  ⟨1838, 1844, 0, .none, s1838_zero_contract, 405, s1838_zero_checked⟩

def s1838_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s1838_positive_checked : check 405 s1838_positive_contract = true := by decide +kernel
def s1838_positive : CertifiedContract :=
  ⟨1838, 1839, 1, (.dec 5), s1838_positive_contract, 405, s1838_positive_checked⟩

def s1839_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s1839_plain_checked : check 418 s1839_plain_contract = true := by decide +kernel
def s1839_plain : CertifiedContract :=
  ⟨1839, 1840, 0, (.inc 2), s1839_plain_contract, 418, s1839_plain_checked⟩

def s1840_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s1840_plain_checked : check 421 s1840_plain_contract = true := by decide +kernel
def s1840_plain : CertifiedContract :=
  ⟨1840, 1841, 0, (.inc 2), s1840_plain_contract, 421, s1840_plain_checked⟩

def s1841_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s1841_plain_checked : check 427 s1841_plain_contract = true := by decide +kernel
def s1841_plain : CertifiedContract :=
  ⟨1841, 1842, 0, (.inc 2), s1841_plain_contract, 427, s1841_plain_checked⟩

def s1842_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s1842_plain_checked : check 433 s1842_plain_contract = true := by decide +kernel
def s1842_plain : CertifiedContract :=
  ⟨1842, 1843, 0, (.inc 2), s1842_plain_contract, 433, s1842_plain_checked⟩

def s1843_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, false, true, true, false] 0 .none⟩
theorem s1843_plain_checked : check 110 s1843_plain_contract = true := by decide +kernel
def s1843_plain : CertifiedContract :=
  ⟨1843, 1838, 0, .none, s1843_plain_contract, 110, s1843_plain_checked⟩

def s1844_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1844_plain_checked : check 373 s1844_plain_contract = true := by decide +kernel
def s1844_plain : CertifiedContract :=
  ⟨1844, 1845, 0, (.inc 2), s1844_plain_contract, 373, s1844_plain_checked⟩

def s1845_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, true] 0 (.inc 2)⟩
theorem s1845_plain_checked : check 382 s1845_plain_contract = true := by decide +kernel
def s1845_plain : CertifiedContract :=
  ⟨1845, 1846, 0, (.inc 2), s1845_plain_contract, 382, s1845_plain_checked⟩

def s1846_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, false, false] 0 (.inc 2)⟩
theorem s1846_plain_checked : check 349 s1846_plain_contract = true := by decide +kernel
def s1846_plain : CertifiedContract :=
  ⟨1846, 1847, 0, (.inc 2), s1846_plain_contract, 349, s1846_plain_checked⟩

def s1847_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s1847_zero_checked : check 354 s1847_zero_contract = true := by decide +kernel
def s1847_zero : CertifiedContract :=
  ⟨1847, 1850, 0, .none, s1847_zero_contract, 354, s1847_zero_checked⟩

def s1847_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s1847_positive_checked : check 360 s1847_positive_contract = true := by decide +kernel
def s1847_positive : CertifiedContract :=
  ⟨1847, 1848, 1, (.dec 2), s1847_positive_contract, 360, s1847_positive_checked⟩

def s1848_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s1848_plain_checked : check 373 s1848_plain_contract = true := by decide +kernel
def s1848_plain : CertifiedContract :=
  ⟨1848, 1849, 0, (.inc 8), s1848_plain_contract, 373, s1848_plain_checked⟩

def s1849_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, false, false] 0 .none⟩
theorem s1849_plain_checked : check 98 s1849_plain_contract = true := by decide +kernel
def s1849_plain : CertifiedContract :=
  ⟨1849, 1847, 0, .none, s1849_plain_contract, 98, s1849_plain_checked⟩

def s1850_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1850_zero_checked : check 375 s1850_zero_contract = true := by decide +kernel
def s1850_zero : CertifiedContract :=
  ⟨1850, 1853, 0, .none, s1850_zero_contract, 375, s1850_zero_checked⟩

def s1850_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s1850_positive_checked : check 381 s1850_positive_contract = true := by decide +kernel
def s1850_positive : CertifiedContract :=
  ⟨1850, 1851, 1, (.dec 0), s1850_positive_contract, 381, s1850_positive_checked⟩

def s1851_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s1851_plain_checked : check 373 s1851_plain_contract = true := by decide +kernel
def s1851_plain : CertifiedContract :=
  ⟨1851, 1852, 0, (.inc 2), s1851_plain_contract, 373, s1851_plain_checked⟩

def s1852_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, false, false] 0 .none⟩
theorem s1852_plain_checked : check 101 s1852_plain_contract = true := by decide +kernel
def s1852_plain : CertifiedContract :=
  ⟨1852, 1850, 0, .none, s1852_plain_contract, 101, s1852_plain_checked⟩

def s1853_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1853_zero_checked : check 381 s1853_zero_contract = true := by decide +kernel
def s1853_zero : CertifiedContract :=
  ⟨1853, 1857, 0, .none, s1853_zero_contract, 381, s1853_zero_checked⟩

def s1853_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1853_positive_checked : check 387 s1853_positive_contract = true := by decide +kernel
def s1853_positive : CertifiedContract :=
  ⟨1853, 1854, 1, (.dec 2), s1853_positive_contract, 387, s1853_positive_checked⟩

def s1854_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1854_plain_checked : check 400 s1854_plain_contract = true := by decide +kernel
def s1854_plain : CertifiedContract :=
  ⟨1854, 1855, 0, (.inc 5), s1854_plain_contract, 400, s1854_plain_checked⟩

def s1855_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1855_plain_checked : check 427 s1855_plain_contract = true := by decide +kernel
def s1855_plain : CertifiedContract :=
  ⟨1855, 1856, 0, (.inc 8), s1855_plain_contract, 427, s1855_plain_checked⟩

def s1856_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1856_plain_checked : check 116 s1856_plain_contract = true := by decide +kernel
def s1856_plain : CertifiedContract :=
  ⟨1856, 1853, 0, .none, s1856_plain_contract, 116, s1856_plain_checked⟩

def s1857_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s1857_zero_checked : check 402 s1857_zero_contract = true := by decide +kernel
def s1857_zero : CertifiedContract :=
  ⟨1857, 1863, 0, .none, s1857_zero_contract, 402, s1857_zero_checked⟩

def s1857_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1857_positive_checked : check 405 s1857_positive_contract = true := by decide +kernel
def s1857_positive : CertifiedContract :=
  ⟨1857, 1858, 1, (.dec 8), s1857_positive_contract, 405, s1857_positive_checked⟩

def s1858_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1858_plain_checked : check 400 s1858_plain_contract = true := by decide +kernel
def s1858_plain : CertifiedContract :=
  ⟨1858, 1859, 0, (.inc 5), s1858_plain_contract, 400, s1858_plain_checked⟩

def s1859_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s1859_zero_checked : check 420 s1859_zero_contract = true := by decide +kernel
def s1859_zero : CertifiedContract :=
  ⟨1859, 1862, 0, .none, s1859_zero_contract, 420, s1859_zero_checked⟩

def s1859_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1859_positive_checked : check 423 s1859_positive_contract = true := by decide +kernel
def s1859_positive : CertifiedContract :=
  ⟨1859, 1860, 1, (.dec 8), s1859_positive_contract, 423, s1859_positive_checked⟩

def s1860_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1860_plain_checked : check 418 s1860_plain_contract = true := by decide +kernel
def s1860_plain : CertifiedContract :=
  ⟨1860, 1861, 0, (.inc 2), s1860_plain_contract, 418, s1860_plain_checked⟩

def s1861_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1861_plain_checked : check 116 s1861_plain_contract = true := by decide +kernel
def s1861_plain : CertifiedContract :=
  ⟨1861, 1859, 0, .none, s1861_plain_contract, 116, s1861_plain_checked⟩

def s1862_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1862_plain_checked : check 119 s1862_plain_contract = true := by decide +kernel
def s1862_plain : CertifiedContract :=
  ⟨1862, 1853, 0, .none, s1862_plain_contract, 119, s1862_plain_checked⟩

def s1863_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s1863_zero_checked : check 390 s1863_zero_contract = true := by decide +kernel
def s1863_zero : CertifiedContract :=
  ⟨1863, 1866, 0, .none, s1863_zero_contract, 390, s1863_zero_checked⟩

def s1863_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s1863_positive_checked : check 387 s1863_positive_contract = true := by decide +kernel
def s1863_positive : CertifiedContract :=
  ⟨1863, 1864, 1, (.dec 5), s1863_positive_contract, 387, s1863_positive_checked⟩

def s1864_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s1864_plain_checked : check 400 s1864_plain_contract = true := by decide +kernel
def s1864_plain : CertifiedContract :=
  ⟨1864, 1865, 0, (.inc 0), s1864_plain_contract, 400, s1864_plain_checked⟩

def s1865_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, false, true, true, true, false] 0 .none⟩
theorem s1865_plain_checked : check 107 s1865_plain_contract = true := by decide +kernel
def s1865_plain : CertifiedContract :=
  ⟨1865, 1863, 0, .none, s1865_plain_contract, 107, s1865_plain_checked⟩

def s1866_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s1866_zero_checked : check 354 s1866_zero_contract = true := by decide +kernel
def s1866_zero : CertifiedContract :=
  ⟨1866, 1870, 0, .none, s1866_zero_contract, 354, s1866_zero_checked⟩

def s1866_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, true, false, true, false] 1 (.dec 4)⟩
theorem s1866_positive_checked : check 360 s1866_positive_contract = true := by decide +kernel
def s1866_positive : CertifiedContract :=
  ⟨1866, 1867, 1, (.dec 4), s1866_positive_contract, 360, s1866_positive_checked⟩

def s1867_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s1867_plain_checked : check 373 s1867_plain_contract = true := by decide +kernel
def s1867_plain : CertifiedContract :=
  ⟨1867, 1868, 0, (.inc 2), s1867_plain_contract, 373, s1867_plain_checked⟩

def s1868_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1868_plain_checked : check 400 s1868_plain_contract = true := by decide +kernel
def s1868_plain : CertifiedContract :=
  ⟨1868, 1869, 0, (.inc 8), s1868_plain_contract, 400, s1868_plain_checked⟩

def s1869_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, true, false, false] 0 .none⟩
theorem s1869_plain_checked : check 107 s1869_plain_contract = true := by decide +kernel
def s1869_plain : CertifiedContract :=
  ⟨1869, 1866, 0, .none, s1869_plain_contract, 107, s1869_plain_checked⟩

def s1870_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s1870_zero_checked : check 360 s1870_zero_contract = true := by decide +kernel
def s1870_zero : CertifiedContract :=
  ⟨1870, 1873, 0, .none, s1870_zero_contract, 360, s1870_zero_checked⟩

def s1870_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s1870_positive_checked : check 360 s1870_positive_contract = true := by decide +kernel
def s1870_positive : CertifiedContract :=
  ⟨1870, 1871, 1, (.dec 8), s1870_positive_contract, 360, s1870_positive_checked⟩

def s1871_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, true, true, true, true] 0 (.inc 4)⟩
theorem s1871_plain_checked : check 364 s1871_plain_contract = true := by decide +kernel
def s1871_plain : CertifiedContract :=
  ⟨1871, 1872, 0, (.inc 4), s1871_plain_contract, 364, s1871_plain_checked⟩

end PA211.UserCandidate.RuntimeShards.S037
