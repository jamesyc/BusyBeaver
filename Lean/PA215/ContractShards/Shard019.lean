import PA215.ContractShards.Shard019Part0
import PA215.ContractShards.Shard019Part1
import PA215.ContractShards.Shard019Part2
import PA215.ContractShards.Shard019Part3
import PA215.ContractShards.Shard019Part4
import PA215.ContractShards.Shard019Part5
import PA215.ContractShards.Shard019Part6
import PA215.ContractShards.Shard019Part7
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace PA215.ContractShards.Shard019
open PA215.Contracts

def records : List Certified :=
  PA215.ContractShards.Shard019Part0.records ++
  PA215.ContractShards.Shard019Part1.records ++
  PA215.ContractShards.Shard019Part2.records ++
  PA215.ContractShards.Shard019Part3.records ++
  PA215.ContractShards.Shard019Part4.records ++
  PA215.ContractShards.Shard019Part5.records ++
  PA215.ContractShards.Shard019Part6.records ++
  PA215.ContractShards.Shard019Part7.records

def ids : List Nat := records.map Certified.id

theorem exact_ids : ids = [2438, 2439, 2440, 2441, 2442, 2443, 2444, 2445, 2446, 2447, 2448, 2449, 2450, 2451, 2452, 2453, 2454, 2455, 2456, 2457, 2458, 2459, 2460, 2461, 2462, 2463, 2464, 2465, 2466, 2467, 2468, 2469, 2470, 2471, 2472, 2473, 2474, 2475, 2476, 2477, 2478, 2479, 2480, 2481, 2482, 2483, 2484, 2485, 2486, 2487, 2488, 2489, 2490, 2491, 2492, 2493, 2494, 2495, 2496, 2497, 2498, 2499, 2500, 2501, 2502, 2503, 2504, 2505, 2506, 2507, 2508, 2509, 2510, 2511, 2512, 2513, 2514, 2515, 2516, 2517, 2518, 2519, 2520, 2521, 2522, 2523, 2524, 2525, 2526, 2527, 2528, 2529, 2530, 2531, 2532, 2533, 2534, 2535, 2536, 2537, 2538, 2539, 2540, 2541, 2542, 2543, 2544, 2545, 2546, 2547, 2548, 2549, 2550, 2551, 2552, 2553, 2554, 2555, 2556, 2557, 2558, 2559, 2560, 2561, 2562, 2563, 2564, 2565] := by decide
theorem count : records.length = 128 := by decide
theorem distinct_ids : ids.Nodup := by decide

end PA215.ContractShards.Shard019
