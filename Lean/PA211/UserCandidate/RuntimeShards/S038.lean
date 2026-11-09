module

public import PA211.UserCandidate.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA211.UserCandidate.RuntimeShards.S038
open PA215.Zip PA215.Runtime PA211.UserCandidate.CandidateTable PA211.UserCandidate.RuntimeContracts
def s1872_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, false, true, true, false] 0 .none⟩
theorem s1872_plain_checked : check 98 s1872_plain_contract = true := by decide +kernel
def s1872_plain : CertifiedContract :=
  ⟨1872, 1870, 0, .none, s1872_plain_contract, 98, s1872_plain_checked⟩

def s1873_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s1873_zero_checked : check 354 s1873_zero_contract = true := by decide +kernel
def s1873_zero : CertifiedContract :=
  ⟨1873, 1876, 0, .none, s1873_zero_contract, 354, s1873_zero_checked⟩

def s1873_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1873_positive_checked : check 360 s1873_positive_contract = true := by decide +kernel
def s1873_positive : CertifiedContract :=
  ⟨1873, 1874, 1, (.dec 2), s1873_positive_contract, 360, s1873_positive_checked⟩

def s1874_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s1874_plain_checked : check 373 s1874_plain_contract = true := by decide +kernel
def s1874_plain : CertifiedContract :=
  ⟨1874, 1875, 0, (.inc 8), s1874_plain_contract, 373, s1874_plain_checked⟩

def s1875_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, false, false] 0 .none⟩
theorem s1875_plain_checked : check 98 s1875_plain_contract = true := by decide +kernel
def s1875_plain : CertifiedContract :=
  ⟨1875, 1873, 0, .none, s1875_plain_contract, 98, s1875_plain_checked⟩

def s1876_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1876_zero_checked : check 375 s1876_zero_contract = true := by decide +kernel
def s1876_zero : CertifiedContract :=
  ⟨1876, 1879, 0, .none, s1876_zero_contract, 375, s1876_zero_checked⟩

def s1876_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s1876_positive_checked : check 381 s1876_positive_contract = true := by decide +kernel
def s1876_positive : CertifiedContract :=
  ⟨1876, 1877, 1, (.dec 0), s1876_positive_contract, 381, s1876_positive_checked⟩

def s1877_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s1877_plain_checked : check 373 s1877_plain_contract = true := by decide +kernel
def s1877_plain : CertifiedContract :=
  ⟨1877, 1878, 0, (.inc 2), s1877_plain_contract, 373, s1877_plain_checked⟩

def s1878_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, false, false] 0 .none⟩
theorem s1878_plain_checked : check 101 s1878_plain_contract = true := by decide +kernel
def s1878_plain : CertifiedContract :=
  ⟨1878, 1876, 0, .none, s1878_plain_contract, 101, s1878_plain_checked⟩

def s1879_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s1879_zero_checked : check 381 s1879_zero_contract = true := by decide +kernel
def s1879_zero : CertifiedContract :=
  ⟨1879, 1883, 0, .none, s1879_zero_contract, 381, s1879_zero_checked⟩

def s1879_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1879_positive_checked : check 387 s1879_positive_contract = true := by decide +kernel
def s1879_positive : CertifiedContract :=
  ⟨1879, 1880, 1, (.dec 2), s1879_positive_contract, 387, s1879_positive_checked⟩

def s1880_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1880_plain_checked : check 400 s1880_plain_contract = true := by decide +kernel
def s1880_plain : CertifiedContract :=
  ⟨1880, 1881, 0, (.inc 5), s1880_plain_contract, 400, s1880_plain_checked⟩

def s1881_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1881_plain_checked : check 427 s1881_plain_contract = true := by decide +kernel
def s1881_plain : CertifiedContract :=
  ⟨1881, 1882, 0, (.inc 8), s1881_plain_contract, 427, s1881_plain_checked⟩

def s1882_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1882_plain_checked : check 116 s1882_plain_contract = true := by decide +kernel
def s1882_plain : CertifiedContract :=
  ⟨1882, 1879, 0, .none, s1882_plain_contract, 116, s1882_plain_checked⟩

def s1883_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s1883_zero_checked : check 402 s1883_zero_contract = true := by decide +kernel
def s1883_zero : CertifiedContract :=
  ⟨1883, 1889, 0, .none, s1883_zero_contract, 402, s1883_zero_checked⟩

def s1883_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1883_positive_checked : check 405 s1883_positive_contract = true := by decide +kernel
def s1883_positive : CertifiedContract :=
  ⟨1883, 1884, 1, (.dec 8), s1883_positive_contract, 405, s1883_positive_checked⟩

def s1884_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1884_plain_checked : check 400 s1884_plain_contract = true := by decide +kernel
def s1884_plain : CertifiedContract :=
  ⟨1884, 1885, 0, (.inc 5), s1884_plain_contract, 400, s1884_plain_checked⟩

def s1885_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s1885_zero_checked : check 420 s1885_zero_contract = true := by decide +kernel
def s1885_zero : CertifiedContract :=
  ⟨1885, 1888, 0, .none, s1885_zero_contract, 420, s1885_zero_checked⟩

def s1885_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1885_positive_checked : check 423 s1885_positive_contract = true := by decide +kernel
def s1885_positive : CertifiedContract :=
  ⟨1885, 1886, 1, (.dec 8), s1885_positive_contract, 423, s1885_positive_checked⟩

def s1886_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1886_plain_checked : check 418 s1886_plain_contract = true := by decide +kernel
def s1886_plain : CertifiedContract :=
  ⟨1886, 1887, 0, (.inc 2), s1886_plain_contract, 418, s1886_plain_checked⟩

def s1887_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1887_plain_checked : check 116 s1887_plain_contract = true := by decide +kernel
def s1887_plain : CertifiedContract :=
  ⟨1887, 1885, 0, .none, s1887_plain_contract, 116, s1887_plain_checked⟩

def s1888_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1888_plain_checked : check 119 s1888_plain_contract = true := by decide +kernel
def s1888_plain : CertifiedContract :=
  ⟨1888, 1879, 0, .none, s1888_plain_contract, 119, s1888_plain_checked⟩

def s1889_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s1889_zero_checked : check 390 s1889_zero_contract = true := by decide +kernel
def s1889_zero : CertifiedContract :=
  ⟨1889, 1892, 0, .none, s1889_zero_contract, 390, s1889_zero_checked⟩

def s1889_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s1889_positive_checked : check 387 s1889_positive_contract = true := by decide +kernel
def s1889_positive : CertifiedContract :=
  ⟨1889, 1890, 1, (.dec 5), s1889_positive_contract, 387, s1889_positive_checked⟩

def s1890_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s1890_plain_checked : check 400 s1890_plain_contract = true := by decide +kernel
def s1890_plain : CertifiedContract :=
  ⟨1890, 1891, 0, (.inc 0), s1890_plain_contract, 400, s1890_plain_checked⟩

def s1891_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, false, true, true, true, false] 0 .none⟩
theorem s1891_plain_checked : check 107 s1891_plain_contract = true := by decide +kernel
def s1891_plain : CertifiedContract :=
  ⟨1891, 1889, 0, .none, s1891_plain_contract, 107, s1891_plain_checked⟩

def s1892_zero_contract : Contract :=
  ⟨(some (3, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s1892_zero_checked : check 354 s1892_zero_contract = true := by decide +kernel
def s1892_zero : CertifiedContract :=
  ⟨1892, 1896, 0, .none, s1892_zero_contract, 354, s1892_zero_checked⟩

def s1892_positive_contract : Contract :=
  ⟨(some (3, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, true, false, true, false] 1 (.dec 3)⟩
theorem s1892_positive_checked : check 360 s1892_positive_contract = true := by decide +kernel
def s1892_positive : CertifiedContract :=
  ⟨1892, 1893, 1, (.dec 3), s1892_positive_contract, 360, s1892_positive_checked⟩

def s1893_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, true, false, true, true, false] 0 (.inc 2)⟩
theorem s1893_plain_checked : check 373 s1893_plain_contract = true := by decide +kernel
def s1893_plain : CertifiedContract :=
  ⟨1893, 1894, 0, (.inc 2), s1893_plain_contract, 373, s1893_plain_checked⟩

def s1894_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1894_plain_checked : check 400 s1894_plain_contract = true := by decide +kernel
def s1894_plain : CertifiedContract :=
  ⟨1894, 1895, 0, (.inc 8), s1894_plain_contract, 400, s1894_plain_checked⟩

def s1895_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, true, false, false] 0 .none⟩
theorem s1895_plain_checked : check 107 s1895_plain_contract = true := by decide +kernel
def s1895_plain : CertifiedContract :=
  ⟨1895, 1892, 0, .none, s1895_plain_contract, 107, s1895_plain_checked⟩

def s1896_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s1896_zero_checked : check 363 s1896_zero_contract = true := by decide +kernel
def s1896_zero : CertifiedContract :=
  ⟨1896, 1899, 0, .none, s1896_zero_contract, 363, s1896_zero_checked⟩

def s1896_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, true, true, true, false] 1 (.dec 8)⟩
theorem s1896_positive_checked : check 360 s1896_positive_contract = true := by decide +kernel
def s1896_positive : CertifiedContract :=
  ⟨1896, 1897, 1, (.dec 8), s1896_positive_contract, 360, s1896_positive_checked⟩

def s1897_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, true, true, true, true] 0 (.inc 3)⟩
theorem s1897_plain_checked : check 376 s1897_plain_contract = true := by decide +kernel
def s1897_plain : CertifiedContract :=
  ⟨1897, 1898, 0, (.inc 3), s1897_plain_contract, 376, s1897_plain_checked⟩

def s1898_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, false, true, true, true, false] 0 .none⟩
theorem s1898_plain_checked : check 98 s1898_plain_contract = true := by decide +kernel
def s1898_plain : CertifiedContract :=
  ⟨1898, 1896, 0, .none, s1898_plain_contract, 98, s1898_plain_checked⟩

def s1899_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s1899_zero_checked : check 366 s1899_zero_contract = true := by decide +kernel
def s1899_zero : CertifiedContract :=
  ⟨1899, 1907, 0, .none, s1899_zero_contract, 366, s1899_zero_checked⟩

def s1899_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, false, true, false] 1 (.dec 0)⟩
theorem s1899_positive_checked : check 372 s1899_positive_contract = true := by decide +kernel
def s1899_positive : CertifiedContract :=
  ⟨1899, 1900, 1, (.dec 0), s1899_positive_contract, 372, s1899_positive_checked⟩

def s1900_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, false, true, true, false, false, false] 0 (.inc 5)⟩
theorem s1900_plain_checked : check 382 s1900_plain_contract = true := by decide +kernel
def s1900_plain : CertifiedContract :=
  ⟨1900, 1901, 0, (.inc 5), s1900_plain_contract, 382, s1900_plain_checked⟩

def s1901_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1901_zero_checked : check 408 s1901_zero_contract = true := by decide +kernel
def s1901_zero : CertifiedContract :=
  ⟨1901, 1903, 0, .none, s1901_zero_contract, 408, s1901_zero_checked⟩

def s1901_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, false, true, true, false, false, true] 1 (.dec 8)⟩
theorem s1901_positive_checked : check 414 s1901_positive_contract = true := by decide +kernel
def s1901_positive : CertifiedContract :=
  ⟨1901, 1902, 1, (.dec 8), s1901_positive_contract, 414, s1901_positive_checked⟩

def s1902_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, false, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s1902_plain_checked : check 113 s1902_plain_contract = true := by decide +kernel
def s1902_plain : CertifiedContract :=
  ⟨1902, 1906, 0, .none, s1902_plain_contract, 113, s1902_plain_checked⟩

def s1903_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, false, true, true, true] 0 .none⟩
theorem s1903_zero_checked : check 420 s1903_zero_contract = true := by decide +kernel
def s1903_zero : CertifiedContract :=
  ⟨1903, 1906, 0, .none, s1903_zero_contract, 420, s1903_zero_checked⟩

def s1903_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, false, true, true, false, true, true, false] 1 (.dec 5)⟩
theorem s1903_positive_checked : check 423 s1903_positive_contract = true := by decide +kernel
def s1903_positive : CertifiedContract :=
  ⟨1903, 1904, 1, (.dec 5), s1903_positive_contract, 423, s1903_positive_checked⟩

def s1904_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1904_plain_checked : check 427 s1904_plain_contract = true := by decide +kernel
def s1904_plain : CertifiedContract :=
  ⟨1904, 1905, 0, (.inc 8), s1904_plain_contract, 427, s1904_plain_checked⟩

def s1905_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1905_plain_checked : check 116 s1905_plain_contract = true := by decide +kernel
def s1905_plain : CertifiedContract :=
  ⟨1905, 1903, 0, .none, s1905_plain_contract, 116, s1905_plain_checked⟩

def s1906_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, false, false] 0 .none⟩
theorem s1906_plain_checked : check 107 s1906_plain_contract = true := by decide +kernel
def s1906_plain : CertifiedContract :=
  ⟨1906, 1899, 0, .none, s1906_plain_contract, 107, s1906_plain_checked⟩

def s1907_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s1907_zero_checked : check 366 s1907_zero_contract = true := by decide +kernel
def s1907_zero : CertifiedContract :=
  ⟨1907, 1910, 0, .none, s1907_zero_contract, 366, s1907_zero_checked⟩

def s1907_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, true, true, false] 1 (.dec 5)⟩
theorem s1907_positive_checked : check 369 s1907_positive_contract = true := by decide +kernel
def s1907_positive : CertifiedContract :=
  ⟨1907, 1908, 1, (.dec 5), s1907_positive_contract, 369, s1907_positive_checked⟩

def s1908_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, true, true, true] 0 (.inc 0)⟩
theorem s1908_plain_checked : check 382 s1908_plain_contract = true := by decide +kernel
def s1908_plain : CertifiedContract :=
  ⟨1908, 1909, 0, (.inc 0), s1908_plain_contract, 382, s1908_plain_checked⟩

def s1909_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, false, true, false] 0 .none⟩
theorem s1909_plain_checked : check 101 s1909_plain_contract = true := by decide +kernel
def s1909_plain : CertifiedContract :=
  ⟨1909, 1907, 0, .none, s1909_plain_contract, 101, s1909_plain_checked⟩

def s1910_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, false, true, false] 0 .none⟩
theorem s1910_zero_checked : check 363 s1910_zero_contract = true := by decide +kernel
def s1910_zero : CertifiedContract :=
  ⟨1910, 1914, 0, .none, s1910_zero_contract, 363, s1910_zero_checked⟩

def s1910_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1910_positive_checked : check 369 s1910_positive_contract = true := by decide +kernel
def s1910_positive : CertifiedContract :=
  ⟨1910, 1911, 1, (.dec 2), s1910_positive_contract, 369, s1910_positive_checked⟩

def s1911_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1911_plain_checked : check 382 s1911_plain_contract = true := by decide +kernel
def s1911_plain : CertifiedContract :=
  ⟨1911, 1912, 0, (.inc 5), s1911_plain_contract, 382, s1911_plain_checked⟩

def s1912_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1912_plain_checked : check 409 s1912_plain_contract = true := by decide +kernel
def s1912_plain : CertifiedContract :=
  ⟨1912, 1913, 0, (.inc 8), s1912_plain_contract, 409, s1912_plain_checked⟩

def s1913_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s1913_plain_checked : check 110 s1913_plain_contract = true := by decide +kernel
def s1913_plain : CertifiedContract :=
  ⟨1913, 1910, 0, .none, s1913_plain_contract, 110, s1913_plain_checked⟩

def s1914_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s1914_zero_checked : check 384 s1914_zero_contract = true := by decide +kernel
def s1914_zero : CertifiedContract :=
  ⟨1914, 1920, 0, .none, s1914_zero_contract, 384, s1914_zero_checked⟩

def s1914_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1914_positive_checked : check 387 s1914_positive_contract = true := by decide +kernel
def s1914_positive : CertifiedContract :=
  ⟨1914, 1915, 1, (.dec 8), s1914_positive_contract, 387, s1914_positive_checked⟩

def s1915_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1915_plain_checked : check 382 s1915_plain_contract = true := by decide +kernel
def s1915_plain : CertifiedContract :=
  ⟨1915, 1916, 0, (.inc 5), s1915_plain_contract, 382, s1915_plain_checked⟩

def s1916_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, false, true, true, true] 0 .none⟩
theorem s1916_zero_checked : check 402 s1916_zero_contract = true := by decide +kernel
def s1916_zero : CertifiedContract :=
  ⟨1916, 1919, 0, .none, s1916_zero_contract, 402, s1916_zero_checked⟩

def s1916_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1916_positive_checked : check 405 s1916_positive_contract = true := by decide +kernel
def s1916_positive : CertifiedContract :=
  ⟨1916, 1917, 1, (.dec 8), s1916_positive_contract, 405, s1916_positive_checked⟩

def s1917_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1917_plain_checked : check 400 s1917_plain_contract = true := by decide +kernel
def s1917_plain : CertifiedContract :=
  ⟨1917, 1918, 0, (.inc 2), s1917_plain_contract, 400, s1917_plain_checked⟩

def s1918_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s1918_plain_checked : check 110 s1918_plain_contract = true := by decide +kernel
def s1918_plain : CertifiedContract :=
  ⟨1918, 1916, 0, .none, s1918_plain_contract, 110, s1918_plain_checked⟩

def s1919_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, false, false, false] 0 .none⟩
theorem s1919_plain_checked : check 113 s1919_plain_contract = true := by decide +kernel
def s1919_plain : CertifiedContract :=
  ⟨1919, 1910, 0, .none, s1919_plain_contract, 113, s1919_plain_checked⟩

def s1920_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, true] 0 .none⟩
theorem s1920_zero_checked : check 369 s1920_zero_contract = true := by decide +kernel
def s1920_zero : CertifiedContract :=
  ⟨1920, 1926, 0, .none, s1920_zero_contract, 369, s1920_zero_checked⟩

end PA211.UserCandidate.RuntimeShards.S038
