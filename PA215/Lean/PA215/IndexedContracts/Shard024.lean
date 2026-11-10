import PA215.IndexedContracts.Shard024Part0
import PA215.IndexedContracts.Shard024Part1
import PA215.IndexedContracts.Shard024Part2
import PA215.IndexedContracts.Shard024Part3
import PA215.IndexedContracts.Shard024Part4
import PA215.IndexedContracts.Shard024Part5
import PA215.IndexedContracts.Shard024Part6
import PA215.IndexedContracts.Shard024Part7
namespace PA215.IndexedContracts.Shard024
open PA215.Census
def records : OriginalRegistry :=
  PA215.IndexedContracts.Shard024Part0.records ++
  PA215.IndexedContracts.Shard024Part1.records ++
  PA215.IndexedContracts.Shard024Part2.records ++
  PA215.IndexedContracts.Shard024Part3.records ++
  PA215.IndexedContracts.Shard024Part4.records ++
  PA215.IndexedContracts.Shard024Part5.records ++
  PA215.IndexedContracts.Shard024Part6.records ++
  PA215.IndexedContracts.Shard024Part7.records

theorem exact_ids : records.map (fun e => e.1.val) = [3078, 3079, 3080, 3081, 3082, 3083, 3084, 3085, 3086, 3087, 3088, 3089, 3090, 3091, 3092, 3093, 3094, 3095, 3096, 3097, 3098, 3099, 3100, 3101, 3102, 3103, 3104, 3105, 3106, 3107, 3108, 3109, 3110, 3111, 3112, 3113, 3114, 3115, 3116, 3117, 3118, 3119, 3120, 3121, 3122, 3123, 3124, 3125, 3126, 3127, 3128, 3129, 3130, 3131, 3132, 3133, 3134, 3135, 3136, 3137, 3138, 3139, 3140, 3141, 3142, 3143, 3144, 3145, 3146, 3147, 3148, 3149, 3150, 3151, 3152, 3153, 3154, 3155, 3156, 3157, 3158, 3159, 3160, 3161, 3162, 3163, 3164, 3165, 3166, 3167, 3168, 3169, 3170, 3171, 3172, 3173, 3174, 3175, 3176, 3177, 3178, 3179, 3180, 3181, 3182, 3183, 3184, 3185, 3186, 3187, 3188, 3189, 3190, 3191, 3192, 3193, 3194, 3195, 3196, 3197, 3198, 3199, 3200, 3201, 3202, 3203, 3204, 3205] := by
  simp only [records, List.map_append, PA215.IndexedContracts.Shard024Part0.exact_ids, PA215.IndexedContracts.Shard024Part1.exact_ids, PA215.IndexedContracts.Shard024Part2.exact_ids, PA215.IndexedContracts.Shard024Part3.exact_ids, PA215.IndexedContracts.Shard024Part4.exact_ids, PA215.IndexedContracts.Shard024Part5.exact_ids, PA215.IndexedContracts.Shard024Part6.exact_ids, PA215.IndexedContracts.Shard024Part7.exact_ids]
  all_goals rfl

end PA215.IndexedContracts.Shard024
