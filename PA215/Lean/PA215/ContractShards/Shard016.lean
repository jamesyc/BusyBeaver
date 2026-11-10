import PA215.ContractShards.Shard016Part0
import PA215.ContractShards.Shard016Part1
import PA215.ContractShards.Shard016Part2
import PA215.ContractShards.Shard016Part3
import PA215.ContractShards.Shard016Part4
import PA215.ContractShards.Shard016Part5
import PA215.ContractShards.Shard016Part6
import PA215.ContractShards.Shard016Part7
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard016
open PA215.Contracts

def records : List Certified :=
  PA215.ContractShards.Shard016Part0.records ++
  PA215.ContractShards.Shard016Part1.records ++
  PA215.ContractShards.Shard016Part2.records ++
  PA215.ContractShards.Shard016Part3.records ++
  PA215.ContractShards.Shard016Part4.records ++
  PA215.ContractShards.Shard016Part5.records ++
  PA215.ContractShards.Shard016Part6.records ++
  PA215.ContractShards.Shard016Part7.records

def ids : List Nat := records.map Certified.id

theorem exact_ids : ids = [2054, 2055, 2056, 2057, 2058, 2059, 2060, 2061, 2062, 2063, 2064, 2065, 2066, 2067, 2068, 2069, 2070, 2071, 2072, 2073, 2074, 2075, 2076, 2077, 2078, 2079, 2080, 2081, 2082, 2083, 2084, 2085, 2086, 2087, 2088, 2089, 2090, 2091, 2092, 2093, 2094, 2095, 2096, 2097, 2098, 2099, 2100, 2101, 2102, 2103, 2104, 2105, 2106, 2107, 2108, 2109, 2110, 2111, 2112, 2113, 2114, 2115, 2116, 2117, 2118, 2119, 2120, 2121, 2122, 2123, 2124, 2125, 2126, 2127, 2128, 2129, 2130, 2131, 2132, 2133, 2134, 2135, 2136, 2137, 2138, 2139, 2140, 2141, 2142, 2143, 2144, 2145, 2146, 2147, 2148, 2149, 2150, 2151, 2152, 2153, 2154, 2155, 2156, 2157, 2158, 2159, 2160, 2161, 2162, 2163, 2164, 2165, 2166, 2167, 2168, 2169, 2170, 2171, 2172, 2173, 2174, 2175, 2176, 2177, 2178, 2179, 2180, 2181] := by decide
theorem count : records.length = 128 := by decide
theorem distinct_ids : ids.Nodup := by decide

end PA215.ContractShards.Shard016
