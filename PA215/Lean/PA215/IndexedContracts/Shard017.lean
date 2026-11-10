import PA215.IndexedContracts.Shard017Part0
import PA215.IndexedContracts.Shard017Part1
import PA215.IndexedContracts.Shard017Part2
import PA215.IndexedContracts.Shard017Part3
import PA215.IndexedContracts.Shard017Part4
import PA215.IndexedContracts.Shard017Part5
import PA215.IndexedContracts.Shard017Part6
import PA215.IndexedContracts.Shard017Part7
namespace PA215.IndexedContracts.Shard017
open PA215.Census
def records : OriginalRegistry :=
  PA215.IndexedContracts.Shard017Part0.records ++
  PA215.IndexedContracts.Shard017Part1.records ++
  PA215.IndexedContracts.Shard017Part2.records ++
  PA215.IndexedContracts.Shard017Part3.records ++
  PA215.IndexedContracts.Shard017Part4.records ++
  PA215.IndexedContracts.Shard017Part5.records ++
  PA215.IndexedContracts.Shard017Part6.records ++
  PA215.IndexedContracts.Shard017Part7.records

theorem exact_ids : records.map (fun e => e.1.val) = [2182, 2183, 2184, 2185, 2186, 2187, 2188, 2189, 2190, 2191, 2192, 2193, 2194, 2195, 2196, 2197, 2198, 2199, 2200, 2201, 2202, 2203, 2204, 2205, 2206, 2207, 2208, 2209, 2210, 2211, 2212, 2213, 2214, 2215, 2216, 2217, 2218, 2219, 2220, 2221, 2222, 2223, 2224, 2225, 2226, 2227, 2228, 2229, 2230, 2231, 2232, 2233, 2234, 2235, 2236, 2237, 2238, 2239, 2240, 2241, 2242, 2243, 2244, 2245, 2246, 2247, 2248, 2249, 2250, 2251, 2252, 2253, 2254, 2255, 2256, 2257, 2258, 2259, 2260, 2261, 2262, 2263, 2264, 2265, 2266, 2267, 2268, 2269, 2270, 2271, 2272, 2273, 2274, 2275, 2276, 2277, 2278, 2279, 2280, 2281, 2282, 2283, 2284, 2285, 2286, 2287, 2288, 2289, 2290, 2291, 2292, 2293, 2294, 2295, 2296, 2297, 2298, 2299, 2300, 2301, 2302, 2303, 2304, 2305, 2306, 2307, 2308, 2309] := by
  simp only [records, List.map_append, PA215.IndexedContracts.Shard017Part0.exact_ids, PA215.IndexedContracts.Shard017Part1.exact_ids, PA215.IndexedContracts.Shard017Part2.exact_ids, PA215.IndexedContracts.Shard017Part3.exact_ids, PA215.IndexedContracts.Shard017Part4.exact_ids, PA215.IndexedContracts.Shard017Part5.exact_ids, PA215.IndexedContracts.Shard017Part6.exact_ids, PA215.IndexedContracts.Shard017Part7.exact_ids]
  all_goals rfl

end PA215.IndexedContracts.Shard017
