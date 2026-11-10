import PA215.IndexedContracts.Shard015Part0
import PA215.IndexedContracts.Shard015Part1
import PA215.IndexedContracts.Shard015Part2
import PA215.IndexedContracts.Shard015Part3
import PA215.IndexedContracts.Shard015Part4
import PA215.IndexedContracts.Shard015Part5
import PA215.IndexedContracts.Shard015Part6
import PA215.IndexedContracts.Shard015Part7
namespace PA215.IndexedContracts.Shard015
open PA215.Census
def records : OriginalRegistry :=
  PA215.IndexedContracts.Shard015Part0.records ++
  PA215.IndexedContracts.Shard015Part1.records ++
  PA215.IndexedContracts.Shard015Part2.records ++
  PA215.IndexedContracts.Shard015Part3.records ++
  PA215.IndexedContracts.Shard015Part4.records ++
  PA215.IndexedContracts.Shard015Part5.records ++
  PA215.IndexedContracts.Shard015Part6.records ++
  PA215.IndexedContracts.Shard015Part7.records

theorem exact_ids : records.map (fun e => e.1.val) = [1926, 1927, 1928, 1929, 1930, 1931, 1932, 1933, 1934, 1935, 1936, 1937, 1938, 1939, 1940, 1941, 1942, 1943, 1944, 1945, 1946, 1947, 1948, 1949, 1950, 1951, 1952, 1953, 1954, 1955, 1956, 1957, 1958, 1959, 1960, 1961, 1962, 1963, 1964, 1965, 1966, 1967, 1968, 1969, 1970, 1971, 1972, 1973, 1974, 1975, 1976, 1977, 1978, 1979, 1980, 1981, 1982, 1983, 1984, 1985, 1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994, 1995, 1996, 1997, 1998, 1999, 2000, 2001, 2002, 2003, 2004, 2005, 2006, 2007, 2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021, 2022, 2023, 2024, 2025, 2026, 2027, 2028, 2029, 2030, 2031, 2032, 2033, 2034, 2035, 2036, 2037, 2038, 2039, 2040, 2041, 2042, 2043, 2044, 2045, 2046, 2047, 2048, 2049, 2050, 2051, 2052, 2053] := by
  simp only [records, List.map_append, PA215.IndexedContracts.Shard015Part0.exact_ids, PA215.IndexedContracts.Shard015Part1.exact_ids, PA215.IndexedContracts.Shard015Part2.exact_ids, PA215.IndexedContracts.Shard015Part3.exact_ids, PA215.IndexedContracts.Shard015Part4.exact_ids, PA215.IndexedContracts.Shard015Part5.exact_ids, PA215.IndexedContracts.Shard015Part6.exact_ids, PA215.IndexedContracts.Shard015Part7.exact_ids]
  rfl

end PA215.IndexedContracts.Shard015
