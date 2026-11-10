import PA215.IndexedContracts.Shard021Part0
import PA215.IndexedContracts.Shard021Part1
import PA215.IndexedContracts.Shard021Part2
import PA215.IndexedContracts.Shard021Part3
import PA215.IndexedContracts.Shard021Part4
import PA215.IndexedContracts.Shard021Part5
import PA215.IndexedContracts.Shard021Part6
import PA215.IndexedContracts.Shard021Part7
namespace PA215.IndexedContracts.Shard021
open PA215.Census
def records : OriginalRegistry :=
  PA215.IndexedContracts.Shard021Part0.records ++
  PA215.IndexedContracts.Shard021Part1.records ++
  PA215.IndexedContracts.Shard021Part2.records ++
  PA215.IndexedContracts.Shard021Part3.records ++
  PA215.IndexedContracts.Shard021Part4.records ++
  PA215.IndexedContracts.Shard021Part5.records ++
  PA215.IndexedContracts.Shard021Part6.records ++
  PA215.IndexedContracts.Shard021Part7.records

theorem exact_ids : records.map (fun e => e.1.val) = [2694, 2695, 2696, 2697, 2698, 2699, 2700, 2701, 2702, 2703, 2704, 2705, 2706, 2707, 2708, 2709, 2710, 2711, 2712, 2713, 2714, 2715, 2716, 2717, 2718, 2719, 2720, 2721, 2722, 2723, 2724, 2725, 2726, 2727, 2728, 2729, 2730, 2731, 2732, 2733, 2734, 2735, 2736, 2737, 2738, 2739, 2740, 2741, 2742, 2743, 2744, 2745, 2746, 2747, 2748, 2749, 2750, 2751, 2752, 2753, 2754, 2755, 2756, 2757, 2758, 2759, 2760, 2761, 2762, 2763, 2764, 2765, 2766, 2767, 2768, 2769, 2770, 2771, 2772, 2773, 2774, 2775, 2776, 2777, 2778, 2779, 2780, 2781, 2782, 2783, 2784, 2785, 2786, 2787, 2788, 2789, 2790, 2791, 2792, 2793, 2794, 2795, 2796, 2797, 2798, 2799, 2800, 2801, 2802, 2803, 2804, 2805, 2806, 2807, 2808, 2809, 2810, 2811, 2812, 2813, 2814, 2815, 2816, 2817, 2818, 2819, 2820, 2821] := by
  simp only [records, List.map_append, PA215.IndexedContracts.Shard021Part0.exact_ids, PA215.IndexedContracts.Shard021Part1.exact_ids, PA215.IndexedContracts.Shard021Part2.exact_ids, PA215.IndexedContracts.Shard021Part3.exact_ids, PA215.IndexedContracts.Shard021Part4.exact_ids, PA215.IndexedContracts.Shard021Part5.exact_ids, PA215.IndexedContracts.Shard021Part6.exact_ids, PA215.IndexedContracts.Shard021Part7.exact_ids]
  all_goals rfl

end PA215.IndexedContracts.Shard021
