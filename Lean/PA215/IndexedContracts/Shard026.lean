import PA215.IndexedContracts.Shard026Part0
import PA215.IndexedContracts.Shard026Part1
import PA215.IndexedContracts.Shard026Part2
import PA215.IndexedContracts.Shard026Part3
import PA215.IndexedContracts.Shard026Part4
import PA215.IndexedContracts.Shard026Part5
import PA215.IndexedContracts.Shard026Part6
import PA215.IndexedContracts.Shard026Part7
namespace PA215.IndexedContracts.Shard026
open PA215.Census
def records : OriginalRegistry :=
  PA215.IndexedContracts.Shard026Part0.records ++
  PA215.IndexedContracts.Shard026Part1.records ++
  PA215.IndexedContracts.Shard026Part2.records ++
  PA215.IndexedContracts.Shard026Part3.records ++
  PA215.IndexedContracts.Shard026Part4.records ++
  PA215.IndexedContracts.Shard026Part5.records ++
  PA215.IndexedContracts.Shard026Part6.records ++
  PA215.IndexedContracts.Shard026Part7.records

theorem exact_ids : records.map (fun e => e.1.val) = [3334, 3335, 3336, 3337, 3338, 3339, 3340, 3341, 3342, 3343, 3344, 3345, 3346, 3347, 3348, 3349, 3350, 3351, 3352, 3353, 3354, 3355, 3356, 3357, 3358, 3359, 3360, 3361, 3362, 3363, 3364, 3365, 3366, 3367, 3368, 3369, 3370, 3371, 3372, 3373, 3374, 3375, 3376, 3377, 3378, 3379, 3380, 3381, 3382, 3383, 3384, 3385, 3386, 3387, 3388, 3389, 3390, 3391, 3392, 3393, 3394, 3395, 3396, 3397, 3398, 3399, 3400, 3401, 3402, 3403, 3404, 3405, 3406, 3407, 3408, 3409, 3410, 3411, 3412, 3413, 3414, 3415, 3416, 3417, 3418, 3419, 3420, 3421, 3422, 3423, 3424, 3425, 3426, 3427, 3428, 3429, 3430, 3431, 3432, 3433, 3434, 3435, 3436, 3437, 3438, 3439, 3440, 3441, 3442, 3443, 3444, 3445, 3446, 3447, 3448, 3449, 3450, 3451, 3452, 3453, 3454, 3455, 3456, 3457, 3458, 3459, 3460, 3461] := by
  simp only [records, List.map_append, PA215.IndexedContracts.Shard026Part0.exact_ids, PA215.IndexedContracts.Shard026Part1.exact_ids, PA215.IndexedContracts.Shard026Part2.exact_ids, PA215.IndexedContracts.Shard026Part3.exact_ids, PA215.IndexedContracts.Shard026Part4.exact_ids, PA215.IndexedContracts.Shard026Part5.exact_ids, PA215.IndexedContracts.Shard026Part6.exact_ids, PA215.IndexedContracts.Shard026Part7.exact_ids]
  all_goals rfl

end PA215.IndexedContracts.Shard026
