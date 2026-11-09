module

public import PA213.RuntimeContracts

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace PA213.RuntimeShards.S039
open PA215.Zip PA215.Runtime PA213.CandidateTable PA213.RuntimeContracts
/- GENERATED AND UNCHECKED: every decide obligation must be compiled by Lean. -/
def s1920_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, true, true, false, false, false] 1 (.dec 5)⟩
theorem s1920_positive_checked : check 368 s1920_positive_contract = true := by decide +kernel
def s1920_positive : CertifiedContract :=
  ⟨1920, 1921, 1, (.dec 5), s1920_positive_contract, 368, s1920_positive_checked⟩

def s1921_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, true, true, false, false, true] 0 (.inc 2)⟩
theorem s1921_plain_checked : check 381 s1921_plain_contract = true := by decide +kernel
def s1921_plain : CertifiedContract :=
  ⟨1921, 1922, 0, (.inc 2), s1921_plain_contract, 381, s1921_plain_checked⟩

def s1922_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, true, true, false, false, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, true, true, false, true, false] 0 (.inc 2)⟩
theorem s1922_plain_checked : check 384 s1922_plain_contract = true := by decide +kernel
def s1922_plain : CertifiedContract :=
  ⟨1922, 1923, 0, (.inc 2), s1922_plain_contract, 384, s1922_plain_checked⟩

def s1923_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, true, true, false, true, true] 0 (.inc 2)⟩
theorem s1923_plain_checked : check 381 s1923_plain_contract = true := by decide +kernel
def s1923_plain : CertifiedContract :=
  ⟨1923, 1924, 0, (.inc 2), s1923_plain_contract, 381, s1923_plain_checked⟩

def s1924_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, true, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, true, true, true] 0 (.inc 2)⟩
theorem s1924_plain_checked : check 387 s1924_plain_contract = true := by decide +kernel
def s1924_plain : CertifiedContract :=
  ⟨1924, 1925, 0, (.inc 2), s1924_plain_contract, 387, s1924_plain_checked⟩

def s1925_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, false, true, true, false] 0 .none⟩
theorem s1925_plain_checked : check 97 s1925_plain_contract = true := by decide +kernel
def s1925_plain : CertifiedContract :=
  ⟨1925, 1920, 0, .none, s1925_plain_contract, 97, s1925_plain_checked⟩

def s1926_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, false, false] 0 (.inc 2)⟩
theorem s1926_plain_checked : check 342 s1926_plain_contract = true := by decide +kernel
def s1926_plain : CertifiedContract :=
  ⟨1926, 1927, 0, (.inc 2), s1926_plain_contract, 342, s1926_plain_checked⟩

def s1927_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s1927_zero_checked : check 353 s1927_zero_contract = true := by decide +kernel
def s1927_zero : CertifiedContract :=
  ⟨1927, 1930, 0, .none, s1927_zero_contract, 353, s1927_zero_checked⟩

def s1927_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, false, true, false] 1 (.dec 2)⟩
theorem s1927_positive_checked : check 359 s1927_positive_contract = true := by decide +kernel
def s1927_positive : CertifiedContract :=
  ⟨1927, 1928, 1, (.dec 2), s1927_positive_contract, 359, s1927_positive_checked⟩

def s1928_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, false, true, true] 0 (.inc 8)⟩
theorem s1928_plain_checked : check 372 s1928_plain_contract = true := by decide +kernel
def s1928_plain : CertifiedContract :=
  ⟨1928, 1929, 0, (.inc 8), s1928_plain_contract, 372, s1928_plain_checked⟩

def s1929_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, false, false] 0 .none⟩
theorem s1929_plain_checked : check 97 s1929_plain_contract = true := by decide +kernel
def s1929_plain : CertifiedContract :=
  ⟨1929, 1927, 0, .none, s1929_plain_contract, 97, s1929_plain_checked⟩

def s1930_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1930_zero_checked : check 374 s1930_zero_contract = true := by decide +kernel
def s1930_zero : CertifiedContract :=
  ⟨1930, 1933, 0, .none, s1930_zero_contract, 374, s1930_zero_checked⟩

def s1930_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, false, true, false] 1 (.dec 0)⟩
theorem s1930_positive_checked : check 380 s1930_positive_contract = true := by decide +kernel
def s1930_positive : CertifiedContract :=
  ⟨1930, 1931, 1, (.dec 0), s1930_positive_contract, 380, s1930_positive_checked⟩

def s1931_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, false, true, true] 0 (.inc 2)⟩
theorem s1931_plain_checked : check 372 s1931_plain_contract = true := by decide +kernel
def s1931_plain : CertifiedContract :=
  ⟨1931, 1932, 0, (.inc 2), s1931_plain_contract, 372, s1931_plain_checked⟩

def s1932_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, false, false] 0 .none⟩
theorem s1932_plain_checked : check 100 s1932_plain_contract = true := by decide +kernel
def s1932_plain : CertifiedContract :=
  ⟨1932, 1930, 0, .none, s1932_plain_contract, 100, s1932_plain_checked⟩

def s1933_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, false, true, false] 0 .none⟩
theorem s1933_zero_checked : check 380 s1933_zero_contract = true := by decide +kernel
def s1933_zero : CertifiedContract :=
  ⟨1933, 1937, 0, .none, s1933_zero_contract, 380, s1933_zero_checked⟩

def s1933_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1933_positive_checked : check 386 s1933_positive_contract = true := by decide +kernel
def s1933_positive : CertifiedContract :=
  ⟨1933, 1934, 1, (.dec 2), s1933_positive_contract, 386, s1933_positive_checked⟩

def s1934_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1934_plain_checked : check 399 s1934_plain_contract = true := by decide +kernel
def s1934_plain : CertifiedContract :=
  ⟨1934, 1935, 0, (.inc 5), s1934_plain_contract, 399, s1934_plain_checked⟩

def s1935_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1935_plain_checked : check 426 s1935_plain_contract = true := by decide +kernel
def s1935_plain : CertifiedContract :=
  ⟨1935, 1936, 0, (.inc 8), s1935_plain_contract, 426, s1935_plain_checked⟩

def s1936_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1936_plain_checked : check 115 s1936_plain_contract = true := by decide +kernel
def s1936_plain : CertifiedContract :=
  ⟨1936, 1933, 0, .none, s1936_plain_contract, 115, s1936_plain_checked⟩

def s1937_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, true, false] 0 .none⟩
theorem s1937_zero_checked : check 401 s1937_zero_contract = true := by decide +kernel
def s1937_zero : CertifiedContract :=
  ⟨1937, 1943, 0, .none, s1937_zero_contract, 401, s1937_zero_checked⟩

def s1937_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1937_positive_checked : check 404 s1937_positive_contract = true := by decide +kernel
def s1937_positive : CertifiedContract :=
  ⟨1937, 1938, 1, (.dec 8), s1937_positive_contract, 404, s1937_positive_checked⟩

def s1938_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1938_plain_checked : check 399 s1938_plain_contract = true := by decide +kernel
def s1938_plain : CertifiedContract :=
  ⟨1938, 1939, 0, (.inc 5), s1938_plain_contract, 399, s1938_plain_checked⟩

def s1939_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, false, true, true, true] 0 .none⟩
theorem s1939_zero_checked : check 419 s1939_zero_contract = true := by decide +kernel
def s1939_zero : CertifiedContract :=
  ⟨1939, 1942, 0, .none, s1939_zero_contract, 419, s1939_zero_checked⟩

def s1939_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1939_positive_checked : check 422 s1939_positive_contract = true := by decide +kernel
def s1939_positive : CertifiedContract :=
  ⟨1939, 1940, 1, (.dec 8), s1939_positive_contract, 422, s1939_positive_checked⟩

def s1940_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1940_plain_checked : check 417 s1940_plain_contract = true := by decide +kernel
def s1940_plain : CertifiedContract :=
  ⟨1940, 1941, 0, (.inc 2), s1940_plain_contract, 417, s1940_plain_checked⟩

def s1941_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1941_plain_checked : check 115 s1941_plain_contract = true := by decide +kernel
def s1941_plain : CertifiedContract :=
  ⟨1941, 1939, 0, .none, s1941_plain_contract, 115, s1941_plain_checked⟩

def s1942_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, false, false, false] 0 .none⟩
theorem s1942_plain_checked : check 118 s1942_plain_contract = true := by decide +kernel
def s1942_plain : CertifiedContract :=
  ⟨1942, 1933, 0, .none, s1942_plain_contract, 118, s1942_plain_checked⟩

def s1943_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, true, false, false] 0 .none⟩
theorem s1943_zero_checked : check 389 s1943_zero_contract = true := by decide +kernel
def s1943_zero : CertifiedContract :=
  ⟨1943, 1946, 0, .none, s1943_zero_contract, 389, s1943_zero_checked⟩

def s1943_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s1943_positive_checked : check 386 s1943_positive_contract = true := by decide +kernel
def s1943_positive : CertifiedContract :=
  ⟨1943, 1944, 1, (.dec 5), s1943_positive_contract, 386, s1943_positive_checked⟩

def s1944_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, true, true, true] 0 (.inc 0)⟩
theorem s1944_plain_checked : check 399 s1944_plain_contract = true := by decide +kernel
def s1944_plain : CertifiedContract :=
  ⟨1944, 1945, 0, (.inc 0), s1944_plain_contract, 399, s1944_plain_checked⟩

def s1945_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, false, true, true, true, false] 0 .none⟩
theorem s1945_plain_checked : check 106 s1945_plain_contract = true := by decide +kernel
def s1945_plain : CertifiedContract :=
  ⟨1945, 1943, 0, .none, s1945_plain_contract, 106, s1945_plain_checked⟩

def s1946_zero_contract : Contract :=
  ⟨(some (4, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, true, true, false] 0 .none⟩
theorem s1946_zero_checked : check 353 s1946_zero_contract = true := by decide +kernel
def s1946_zero : CertifiedContract :=
  ⟨1946, 1950, 0, .none, s1946_zero_contract, 353, s1946_zero_checked⟩

def s1946_positive_contract : Contract :=
  ⟨(some (4, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, true, false, true, false] 1 (.dec 4)⟩
theorem s1946_positive_checked : check 359 s1946_positive_contract = true := by decide +kernel
def s1946_positive : CertifiedContract :=
  ⟨1946, 1947, 1, (.dec 4), s1946_positive_contract, 359, s1946_positive_checked⟩

def s1947_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, true, false, true, true, false] 0 (.inc 2)⟩
theorem s1947_plain_checked : check 372 s1947_plain_contract = true := by decide +kernel
def s1947_plain : CertifiedContract :=
  ⟨1947, 1948, 0, (.inc 2), s1947_plain_contract, 372, s1947_plain_checked⟩

def s1948_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, true, false, true, true, true] 0 (.inc 8)⟩
theorem s1948_plain_checked : check 399 s1948_plain_contract = true := by decide +kernel
def s1948_plain : CertifiedContract :=
  ⟨1948, 1949, 0, (.inc 8), s1948_plain_contract, 399, s1948_plain_checked⟩

def s1949_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, true, false, false] 0 .none⟩
theorem s1949_plain_checked : check 106 s1949_plain_contract = true := by decide +kernel
def s1949_plain : CertifiedContract :=
  ⟨1949, 1946, 0, .none, s1949_plain_contract, 106, s1949_plain_checked⟩

def s1950_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, false, false] 0 .none⟩
theorem s1950_zero_checked : check 359 s1950_zero_contract = true := by decide +kernel
def s1950_zero : CertifiedContract :=
  ⟨1950, 1953, 0, .none, s1950_zero_contract, 359, s1950_zero_checked⟩

def s1950_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, true, true, true, false] 1 (.dec 8)⟩
theorem s1950_positive_checked : check 359 s1950_positive_contract = true := by decide +kernel
def s1950_positive : CertifiedContract :=
  ⟨1950, 1951, 1, (.dec 8), s1950_positive_contract, 359, s1950_positive_checked⟩

def s1951_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, true, true, true, true] 0 (.inc 4)⟩
theorem s1951_plain_checked : check 363 s1951_plain_contract = true := by decide +kernel
def s1951_plain : CertifiedContract :=
  ⟨1951, 1952, 0, (.inc 4), s1951_plain_contract, 363, s1951_plain_checked⟩

def s1952_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, true, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, false, true, true, false] 0 .none⟩
theorem s1952_plain_checked : check 97 s1952_plain_contract = true := by decide +kernel
def s1952_plain : CertifiedContract :=
  ⟨1952, 1950, 0, .none, s1952_plain_contract, 97, s1952_plain_checked⟩

def s1953_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s1953_zero_checked : check 353 s1953_zero_contract = true := by decide +kernel
def s1953_zero : CertifiedContract :=
  ⟨1953, 1956, 0, .none, s1953_zero_contract, 353, s1953_zero_checked⟩

def s1953_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1953_positive_checked : check 359 s1953_positive_contract = true := by decide +kernel
def s1953_positive : CertifiedContract :=
  ⟨1953, 1954, 1, (.dec 2), s1953_positive_contract, 359, s1953_positive_checked⟩

def s1954_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, false, true, true] 0 (.inc 8)⟩
theorem s1954_plain_checked : check 372 s1954_plain_contract = true := by decide +kernel
def s1954_plain : CertifiedContract :=
  ⟨1954, 1955, 0, (.inc 8), s1954_plain_contract, 372, s1954_plain_checked⟩

def s1955_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, false, false] 0 .none⟩
theorem s1955_plain_checked : check 97 s1955_plain_contract = true := by decide +kernel
def s1955_plain : CertifiedContract :=
  ⟨1955, 1953, 0, .none, s1955_plain_contract, 97, s1955_plain_checked⟩

def s1956_zero_contract : Contract :=
  ⟨(some (0, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1956_zero_checked : check 374 s1956_zero_contract = true := by decide +kernel
def s1956_zero : CertifiedContract :=
  ⟨1956, 1959, 0, .none, s1956_zero_contract, 374, s1956_zero_checked⟩

def s1956_positive_contract : Contract :=
  ⟨(some (0, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, false, true, false] 1 (.dec 0)⟩
theorem s1956_positive_checked : check 380 s1956_positive_contract = true := by decide +kernel
def s1956_positive : CertifiedContract :=
  ⟨1956, 1957, 1, (.dec 0), s1956_positive_contract, 380, s1956_positive_checked⟩

def s1957_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, false, true, true] 0 (.inc 2)⟩
theorem s1957_plain_checked : check 372 s1957_plain_contract = true := by decide +kernel
def s1957_plain : CertifiedContract :=
  ⟨1957, 1958, 0, (.inc 2), s1957_plain_contract, 372, s1957_plain_checked⟩

def s1958_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, false, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, false, false] 0 .none⟩
theorem s1958_plain_checked : check 100 s1958_plain_contract = true := by decide +kernel
def s1958_plain : CertifiedContract :=
  ⟨1958, 1956, 0, .none, s1958_plain_contract, 100, s1958_plain_checked⟩

def s1959_zero_contract : Contract :=
  ⟨(some (2, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, true, false] 0 .none⟩
theorem s1959_zero_checked : check 380 s1959_zero_contract = true := by decide +kernel
def s1959_zero : CertifiedContract :=
  ⟨1959, 1963, 0, .none, s1959_zero_contract, 380, s1959_zero_checked⟩

def s1959_positive_contract : Contract :=
  ⟨(some (2, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, false, true, false] 1 (.dec 2)⟩
theorem s1959_positive_checked : check 386 s1959_positive_contract = true := by decide +kernel
def s1959_positive : CertifiedContract :=
  ⟨1959, 1960, 1, (.dec 2), s1959_positive_contract, 386, s1959_positive_checked⟩

def s1960_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, false, true, true, false] 0 (.inc 5)⟩
theorem s1960_plain_checked : check 399 s1960_plain_contract = true := by decide +kernel
def s1960_plain : CertifiedContract :=
  ⟨1960, 1961, 0, (.inc 5), s1960_plain_contract, 399, s1960_plain_checked⟩

def s1961_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, false, true, true, true] 0 (.inc 8)⟩
theorem s1961_plain_checked : check 426 s1961_plain_contract = true := by decide +kernel
def s1961_plain : CertifiedContract :=
  ⟨1961, 1962, 0, (.inc 8), s1961_plain_contract, 426, s1961_plain_checked⟩

def s1962_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1962_plain_checked : check 115 s1962_plain_contract = true := by decide +kernel
def s1962_plain : CertifiedContract :=
  ⟨1962, 1959, 0, .none, s1962_plain_contract, 115, s1962_plain_checked⟩

def s1963_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, true, false] 0 .none⟩
theorem s1963_zero_checked : check 401 s1963_zero_contract = true := by decide +kernel
def s1963_zero : CertifiedContract :=
  ⟨1963, 1969, 0, .none, s1963_zero_contract, 401, s1963_zero_checked⟩

def s1963_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, false] 1 (.dec 8)⟩
theorem s1963_positive_checked : check 404 s1963_positive_contract = true := by decide +kernel
def s1963_positive : CertifiedContract :=
  ⟨1963, 1964, 1, (.dec 8), s1963_positive_contract, 404, s1963_positive_checked⟩

def s1964_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false] 0 (.inc 5)⟩
theorem s1964_plain_checked : check 399 s1964_plain_contract = true := by decide +kernel
def s1964_plain : CertifiedContract :=
  ⟨1964, 1965, 0, (.inc 5), s1964_plain_contract, 399, s1964_plain_checked⟩

def s1965_zero_contract : Contract :=
  ⟨(some (8, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, true, true, true] 0 .none⟩
theorem s1965_zero_checked : check 419 s1965_zero_contract = true := by decide +kernel
def s1965_zero : CertifiedContract :=
  ⟨1965, 1968, 0, .none, s1965_zero_contract, 419, s1965_zero_checked⟩

def s1965_positive_contract : Contract :=
  ⟨(some (8, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false] 1 (.dec 8)⟩
theorem s1965_positive_checked : check 422 s1965_positive_contract = true := by decide +kernel
def s1965_positive : CertifiedContract :=
  ⟨1965, 1966, 1, (.dec 8), s1965_positive_contract, 422, s1965_positive_checked⟩

def s1966_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true] 0 (.inc 2)⟩
theorem s1966_plain_checked : check 417 s1966_plain_contract = true := by decide +kernel
def s1966_plain : CertifiedContract :=
  ⟨1966, 1967, 0, (.inc 2), s1966_plain_contract, 417, s1966_plain_checked⟩

def s1967_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false] 0 .none⟩
theorem s1967_plain_checked : check 115 s1967_plain_contract = true := by decide +kernel
def s1967_plain : CertifiedContract :=
  ⟨1967, 1965, 0, .none, s1967_plain_contract, 115, s1967_plain_checked⟩

def s1968_plain_contract : Contract :=
  ⟨(none), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, true, true, true], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, false, false, false] 0 .none⟩
theorem s1968_plain_checked : check 118 s1968_plain_contract = true := by decide +kernel
def s1968_plain : CertifiedContract :=
  ⟨1968, 1959, 0, .none, s1968_plain_contract, 118, s1968_plain_checked⟩

def s1969_zero_contract : Contract :=
  ⟨(some (5, true)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, true, false, false] 0 .none⟩
theorem s1969_zero_checked : check 389 s1969_zero_contract = true := by decide +kernel
def s1969_zero : CertifiedContract :=
  ⟨1969, 1972, 0, .none, s1969_zero_contract, 389, s1969_zero_checked⟩

def s1969_positive_contract : Contract :=
  ⟨(some (5, false)), rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, true, false], rootFrame [true, false, true, false, false, true, true, true, true, false, false, false, false, true, false, true, true, false, true, false, true, true, true, true, false] 1 (.dec 5)⟩
theorem s1969_positive_checked : check 386 s1969_positive_contract = true := by decide +kernel
def s1969_positive : CertifiedContract :=
  ⟨1969, 1970, 1, (.dec 5), s1969_positive_contract, 386, s1969_positive_checked⟩

def nonterminal : Array CertifiedContract := #[
  s1920_positive,
  s1921_plain,
  s1922_plain,
  s1923_plain,
  s1924_plain,
  s1925_plain,
  s1926_plain,
  s1927_zero,
  s1927_positive,
  s1928_plain,
  s1929_plain,
  s1930_zero,
  s1930_positive,
  s1931_plain,
  s1932_plain,
  s1933_zero,
  s1933_positive,
  s1934_plain,
  s1935_plain,
  s1936_plain,
  s1937_zero,
  s1937_positive,
  s1938_plain,
  s1939_zero,
  s1939_positive,
  s1940_plain,
  s1941_plain,
  s1942_plain,
  s1943_zero,
  s1943_positive,
  s1944_plain,
  s1945_plain,
  s1946_zero,
  s1946_positive,
  s1947_plain,
  s1948_plain,
  s1949_plain,
  s1950_zero,
  s1950_positive,
  s1951_plain,
  s1952_plain,
  s1953_zero,
  s1953_positive,
  s1954_plain,
  s1955_plain,
  s1956_zero,
  s1956_positive,
  s1957_plain,
  s1958_plain,
  s1959_zero,
  s1959_positive,
  s1960_plain,
  s1961_plain,
  s1962_plain,
  s1963_zero,
  s1963_positive,
  s1964_plain,
  s1965_zero,
  s1965_positive,
  s1966_plain,
  s1967_plain,
  s1968_plain,
  s1969_zero,
  s1969_positive
]
def terminal : Array CertifiedHalt := #[

]
end PA213.RuntimeShards.S039
