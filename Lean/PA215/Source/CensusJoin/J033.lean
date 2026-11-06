import PA215.Source.ContractJoinPilot
import PA215.Census.C033
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace PA215.Source.CensusJoin.J033
private def site3252 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,true,true,false,true,true,true,false,true,false],.inc 1⟩
private theorem lookup3252 : exactSites[3252]? = some site3252 := by rfl
private def site3253 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,true,true,false,true,true,true,false,true,true],.inc 1⟩
private theorem lookup3253 : exactSites[3253]? = some site3253 := by rfl
private def site3254 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true],.continueTo 2⟩
private theorem lookup3254 : exactSites[3254]? = some site3254 := by rfl
private def site3255 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,true,true,true],.inc 1⟩
private theorem lookup3255 : exactSites[3255]? = some site3255 := by rfl
private def site3256 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,false,false,false,false],.dec 1⟩
private theorem lookup3256 : exactSites[3256]? = some site3256 := by rfl
private def site3257 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,false,false,false,true,false],.inc 6⟩
private theorem lookup3257 : exactSites[3257]? = some site3257 := by rfl
private def site3258 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,false,false,false,true,true],.continueTo 2⟩
private theorem lookup3258 : exactSites[3258]? = some site3258 := by rfl
private def site3259 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,false,false,true,false,false],.dec 2⟩
private theorem lookup3259 : exactSites[3259]? = some site3259 := by rfl
private def site3260 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,false,false,true,false,true,false],.inc 1⟩
private theorem lookup3260 : exactSites[3260]? = some site3260 := by rfl
private def site3261 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,false,false,true,false,true,true],.continueTo 2⟩
private theorem lookup3261 : exactSites[3261]? = some site3261 := by rfl
private def site3262 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,false,false,true,true,false,false,false],.dec 1⟩
private theorem lookup3262 : exactSites[3262]? = some site3262 := by rfl
private def site3263 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,false,false,true,true,false,false,true,false],.inc 7⟩
private theorem lookup3263 : exactSites[3263]? = some site3263 := by rfl
private def site3264 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,false,false,true,true,false,false,true,true,false],.inc 6⟩
private theorem lookup3264 : exactSites[3264]? = some site3264 := by rfl
private def site3265 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,false,false,true,true,false,false,true,true,true],.continueTo 3⟩
private theorem lookup3265 : exactSites[3265]? = some site3265 := by rfl
private def site3266 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,false,false,true,true,false,true,false],.dec 6⟩
private theorem lookup3266 : exactSites[3266]? = some site3266 := by rfl
private def site3267 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,false,false,true,true,false,true,true,false,false],.inc 7⟩
private theorem lookup3267 : exactSites[3267]? = some site3267 := by rfl
private def site3268 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,false,false,true,true,false,true,true,false,true,false],.dec 6⟩
private theorem lookup3268 : exactSites[3268]? = some site3268 := by rfl
private def site3269 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,false,false,true,true,false,true,true,false,true,true,false],.inc 1⟩
private theorem lookup3269 : exactSites[3269]? = some site3269 := by rfl
private def site3270 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,false,false,true,true,false,true,true,false,true,true,true],.continueTo 2⟩
private theorem lookup3270 : exactSites[3270]? = some site3270 := by rfl
private def site3271 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,false,false,true,true,false,true,true,true],.continueTo 3⟩
private theorem lookup3271 : exactSites[3271]? = some site3271 := by rfl
private def site3272 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,false,false,true,true,true,false],.dec 7⟩
private theorem lookup3272 : exactSites[3272]? = some site3272 := by rfl
private def site3273 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,false,false,true,true,true,true,false],.inc 2⟩
private theorem lookup3273 : exactSites[3273]? = some site3273 := by rfl
private def site3274 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,false,false,true,true,true,true,true],.continueTo 2⟩
private theorem lookup3274 : exactSites[3274]? = some site3274 := by rfl
private def site3275 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,false,true,false,false],.dec 3⟩
private theorem lookup3275 : exactSites[3275]? = some site3275 := by rfl
private def site3276 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,false,true,false,true,false],.inc 1⟩
private theorem lookup3276 : exactSites[3276]? = some site3276 := by rfl
private def site3277 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,false,true,false,true,true,false],.inc 6⟩
private theorem lookup3277 : exactSites[3277]? = some site3277 := by rfl
private def site3278 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,false,true,false,true,true,true],.continueTo 3⟩
private theorem lookup3278 : exactSites[3278]? = some site3278 := by rfl
private def site3279 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,false,true,true,false],.dec 6⟩
private theorem lookup3279 : exactSites[3279]? = some site3279 := by rfl
private def site3280 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,false,true,true,true,false],.inc 3⟩
private theorem lookup3280 : exactSites[3280]? = some site3280 := by rfl
private def site3281 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,false,true,true,true,true],.continueTo 2⟩
private theorem lookup3281 : exactSites[3281]? = some site3281 := by rfl
private def site3282 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,false,false,false,false],.dec 2⟩
private theorem lookup3282 : exactSites[3282]? = some site3282 := by rfl
private def site3283 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,false,false,false,true,false],.inc 7⟩
private theorem lookup3283 : exactSites[3283]? = some site3283 := by rfl
private def site3284 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,false,false,false,true,true,false,false,false],.dec 6⟩
private theorem lookup3284 : exactSites[3284]? = some site3284 := by rfl
private def site3285 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,false,false,false,true,true,false,false,true],.breakTo 1⟩
private theorem lookup3285 : exactSites[3285]? = some site3285 := by rfl
private def site3286 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,false,false,false,true,true,false,true,false],.dec 7⟩
private theorem lookup3286 : exactSites[3286]? = some site3286 := by rfl
private def site3287 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,false,false,false,true,true,false,true,true,false],.inc 6⟩
private theorem lookup3287 : exactSites[3287]? = some site3287 := by rfl
private def site3288 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,false,false,false,true,true,false,true,true,true],.continueTo 2⟩
private theorem lookup3288 : exactSites[3288]? = some site3288 := by rfl
private def site3289 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,false,false,false,true,true,true],.continueTo 3⟩
private theorem lookup3289 : exactSites[3289]? = some site3289 := by rfl
private def site3290 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,false,false,true,false],.dec 7⟩
private theorem lookup3290 : exactSites[3290]? = some site3290 := by rfl
private def site3291 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,false,false,true,true,false],.inc 2⟩
private theorem lookup3291 : exactSites[3291]? = some site3291 := by rfl
private def site3292 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,false,false,true,true,true],.continueTo 2⟩
private theorem lookup3292 : exactSites[3292]? = some site3292 := by rfl
private def site3293 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,false,true,false,false,false],.dec 1⟩
private theorem lookup3293 : exactSites[3293]? = some site3293 := by rfl
private def site3294 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,false,true,false,false,true,false],.inc 7⟩
private theorem lookup3294 : exactSites[3294]? = some site3294 := by rfl
private def site3295 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,false,true,false,false,true,true,false],.inc 6⟩
private theorem lookup3295 : exactSites[3295]? = some site3295 := by rfl
private def site3296 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,false,true,false,false,true,true,true],.continueTo 3⟩
private theorem lookup3296 : exactSites[3296]? = some site3296 := by rfl
private def site3297 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,false,true,false,true,false],.dec 6⟩
private theorem lookup3297 : exactSites[3297]? = some site3297 := by rfl
private def site3298 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,false,true,false,true,true,false,false],.inc 7⟩
private theorem lookup3298 : exactSites[3298]? = some site3298 := by rfl
private def site3299 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,false,true,false,true,true,false,true,false],.dec 6⟩
private theorem lookup3299 : exactSites[3299]? = some site3299 := by rfl
private def site3300 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,false,true,false,true,true,false,true,true,false],.inc 1⟩
private theorem lookup3300 : exactSites[3300]? = some site3300 := by rfl
private def site3301 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,false,true,false,true,true,false,true,true,true],.continueTo 2⟩
private theorem lookup3301 : exactSites[3301]? = some site3301 := by rfl
private def site3302 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,false,true,false,true,true,true],.continueTo 3⟩
private theorem lookup3302 : exactSites[3302]? = some site3302 := by rfl
private def site3303 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,false,true,true,false],.dec 7⟩
private theorem lookup3303 : exactSites[3303]? = some site3303 := by rfl
private def site3304 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,false,true,true,true,false,false,false],.inc 1⟩
private theorem lookup3304 : exactSites[3304]? = some site3304 := by rfl
private def site3305 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,false,true,true,true,false,false,true],.inc 1⟩
private theorem lookup3305 : exactSites[3305]? = some site3305 := by rfl
private def site3306 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,false,true,true,true,false,true,false],.inc 1⟩
private theorem lookup3306 : exactSites[3306]? = some site3306 := by rfl
private def site3307 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,false,true,true,true,false,true,true],.inc 1⟩
private theorem lookup3307 : exactSites[3307]? = some site3307 := by rfl
private def site3308 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,false,true,true,true,true],.continueTo 2⟩
private theorem lookup3308 : exactSites[3308]? = some site3308 := by rfl
private def site3309 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,false,false,false,false],.dec 1⟩
private theorem lookup3309 : exactSites[3309]? = some site3309 := by rfl
private def site3310 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,false,false,false,true,false],.inc 6⟩
private theorem lookup3310 : exactSites[3310]? = some site3310 := by rfl
private def site3311 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,false,false,false,true,true],.continueTo 2⟩
private theorem lookup3311 : exactSites[3311]? = some site3311 := by rfl
private def site3312 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,false,false,true,false,false],.dec 2⟩
private theorem lookup3312 : exactSites[3312]? = some site3312 := by rfl
private def site3313 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,false,false,true,false,true,false],.inc 1⟩
private theorem lookup3313 : exactSites[3313]? = some site3313 := by rfl
private def site3314 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,false,false,true,false,true,true],.continueTo 2⟩
private theorem lookup3314 : exactSites[3314]? = some site3314 := by rfl
private def site3315 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,false,false,true,true,false,false,false],.dec 1⟩
private theorem lookup3315 : exactSites[3315]? = some site3315 := by rfl
private def site3316 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,false,false,true,true,false,false,true,false],.inc 7⟩
private theorem lookup3316 : exactSites[3316]? = some site3316 := by rfl
private def site3317 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,false,false,true,true,false,false,true,true,false],.inc 6⟩
private theorem lookup3317 : exactSites[3317]? = some site3317 := by rfl
private def site3318 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,false,false,true,true,false,false,true,true,true],.continueTo 3⟩
private theorem lookup3318 : exactSites[3318]? = some site3318 := by rfl
private def site3319 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,false,false,true,true,false,true,false],.dec 6⟩
private theorem lookup3319 : exactSites[3319]? = some site3319 := by rfl
private def site3320 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,false,false,true,true,false,true,true,false,false],.inc 7⟩
private theorem lookup3320 : exactSites[3320]? = some site3320 := by rfl
private def site3321 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,false,false,true,true,false,true,true,false,true,false],.dec 6⟩
private theorem lookup3321 : exactSites[3321]? = some site3321 := by rfl
private def site3322 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,false,false,true,true,false,true,true,false,true,true,false],.inc 1⟩
private theorem lookup3322 : exactSites[3322]? = some site3322 := by rfl
private def site3323 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,false,false,true,true,false,true,true,false,true,true,true],.continueTo 2⟩
private theorem lookup3323 : exactSites[3323]? = some site3323 := by rfl
private def site3324 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,false,false,true,true,false,true,true,true],.continueTo 3⟩
private theorem lookup3324 : exactSites[3324]? = some site3324 := by rfl
private def site3325 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,false,false,true,true,true,false],.dec 7⟩
private theorem lookup3325 : exactSites[3325]? = some site3325 := by rfl
private def site3326 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,false,false,true,true,true,true,false],.inc 2⟩
private theorem lookup3326 : exactSites[3326]? = some site3326 := by rfl
private def site3327 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,false,false,true,true,true,true,true],.continueTo 2⟩
private theorem lookup3327 : exactSites[3327]? = some site3327 := by rfl
private def site3328 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,false,true],.inc 1⟩
private theorem lookup3328 : exactSites[3328]? = some site3328 := by rfl
private def site3329 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,true,false,false,false],.dec 2⟩
private theorem lookup3329 : exactSites[3329]? = some site3329 := by rfl
private def site3330 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,true,false,false,true,false],.inc 7⟩
private theorem lookup3330 : exactSites[3330]? = some site3330 := by rfl
private def site3331 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,true,false,false,true,true,false,false,false],.dec 6⟩
private theorem lookup3331 : exactSites[3331]? = some site3331 := by rfl
private def site3332 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,true,false,false,true,true,false,false,true],.breakTo 1⟩
private theorem lookup3332 : exactSites[3332]? = some site3332 := by rfl
private def site3333 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,true,false,false,true,true,false,true,false],.dec 7⟩
private theorem lookup3333 : exactSites[3333]? = some site3333 := by rfl
private def site3334 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,true,false,false,true,true,false,true,true,false],.inc 6⟩
private theorem lookup3334 : exactSites[3334]? = some site3334 := by rfl
private def site3335 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,true,false,false,true,true,false,true,true,true],.continueTo 2⟩
private theorem lookup3335 : exactSites[3335]? = some site3335 := by rfl
private def site3336 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,true,false,false,true,true,true],.continueTo 3⟩
private theorem lookup3336 : exactSites[3336]? = some site3336 := by rfl
private def site3337 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,true,false,true,false],.dec 7⟩
private theorem lookup3337 : exactSites[3337]? = some site3337 := by rfl
private def site3338 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,true,false,true,true,false],.inc 2⟩
private theorem lookup3338 : exactSites[3338]? = some site3338 := by rfl
private def site3339 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,true,false,true,true,true],.continueTo 2⟩
private theorem lookup3339 : exactSites[3339]? = some site3339 := by rfl
private def site3340 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,true,true,false,false,false],.dec 1⟩
private theorem lookup3340 : exactSites[3340]? = some site3340 := by rfl
private def site3341 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,true,true,false,false,true,false],.inc 7⟩
private theorem lookup3341 : exactSites[3341]? = some site3341 := by rfl
private def site3342 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,true,true,false,false,true,true,false],.inc 6⟩
private theorem lookup3342 : exactSites[3342]? = some site3342 := by rfl
private def site3343 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,true,true,false,false,true,true,true],.continueTo 3⟩
private theorem lookup3343 : exactSites[3343]? = some site3343 := by rfl
private def site3344 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,true,true,false,true,false],.dec 6⟩
private theorem lookup3344 : exactSites[3344]? = some site3344 := by rfl
private def site3345 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,true,true,false,true,true,false,false],.inc 7⟩
private theorem lookup3345 : exactSites[3345]? = some site3345 := by rfl
private def site3346 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,true,true,false,true,true,false,true,false],.dec 6⟩
private theorem lookup3346 : exactSites[3346]? = some site3346 := by rfl
private def site3347 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,true,true,false,true,true,false,true,true,false],.inc 1⟩
private theorem lookup3347 : exactSites[3347]? = some site3347 := by rfl
private def site3348 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,true,true,false,true,true,false,true,true,true],.continueTo 2⟩
private theorem lookup3348 : exactSites[3348]? = some site3348 := by rfl
private def site3349 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,true,true,false,true,true,true],.continueTo 3⟩
private theorem lookup3349 : exactSites[3349]? = some site3349 := by rfl
private def site3350 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,false,true,false,true,true,true,true,false],.dec 7⟩
private theorem lookup3350 : exactSites[3350]? = some site3350 := by rfl
private def raw0 := PA215.Census.C033.records[0]'(by decide)
private theorem row0 : recordAgrees raw0 = true := by
  unfold recordAgrees
  rw [show raw0.siteIndex = 3252 from rfl,lookup3252]
  decide
private def raw1 := PA215.Census.C033.records[1]'(by decide)
private theorem row1 : recordAgrees raw1 = true := by
  unfold recordAgrees
  rw [show raw1.siteIndex = 3253 from rfl,lookup3253]
  decide
private def raw2 := PA215.Census.C033.records[2]'(by decide)
private theorem row2 : recordAgrees raw2 = true := by
  unfold recordAgrees
  rw [show raw2.siteIndex = 3254 from rfl,lookup3254]
  decide
private def raw3 := PA215.Census.C033.records[3]'(by decide)
private theorem row3 : recordAgrees raw3 = true := by
  unfold recordAgrees
  rw [show raw3.siteIndex = 3255 from rfl,lookup3255]
  decide
private def raw4 := PA215.Census.C033.records[4]'(by decide)
private theorem row4 : recordAgrees raw4 = true := by
  unfold recordAgrees
  rw [show raw4.siteIndex = 3256 from rfl,lookup3256]
  decide
private def raw5 := PA215.Census.C033.records[5]'(by decide)
private theorem row5 : recordAgrees raw5 = true := by
  unfold recordAgrees
  rw [show raw5.siteIndex = 3256 from rfl,lookup3256]
  decide
private def raw6 := PA215.Census.C033.records[6]'(by decide)
private theorem row6 : recordAgrees raw6 = true := by
  unfold recordAgrees
  rw [show raw6.siteIndex = 3257 from rfl,lookup3257]
  decide
private def raw7 := PA215.Census.C033.records[7]'(by decide)
private theorem row7 : recordAgrees raw7 = true := by
  unfold recordAgrees
  rw [show raw7.siteIndex = 3258 from rfl,lookup3258]
  decide
private def raw8 := PA215.Census.C033.records[8]'(by decide)
private theorem row8 : recordAgrees raw8 = true := by
  unfold recordAgrees
  rw [show raw8.siteIndex = 3259 from rfl,lookup3259]
  decide
private def raw9 := PA215.Census.C033.records[9]'(by decide)
private theorem row9 : recordAgrees raw9 = true := by
  unfold recordAgrees
  rw [show raw9.siteIndex = 3259 from rfl,lookup3259]
  decide
private def raw10 := PA215.Census.C033.records[10]'(by decide)
private theorem row10 : recordAgrees raw10 = true := by
  unfold recordAgrees
  rw [show raw10.siteIndex = 3260 from rfl,lookup3260]
  decide
private def raw11 := PA215.Census.C033.records[11]'(by decide)
private theorem row11 : recordAgrees raw11 = true := by
  unfold recordAgrees
  rw [show raw11.siteIndex = 3261 from rfl,lookup3261]
  decide
private def raw12 := PA215.Census.C033.records[12]'(by decide)
private theorem row12 : recordAgrees raw12 = true := by
  unfold recordAgrees
  rw [show raw12.siteIndex = 3262 from rfl,lookup3262]
  decide
private def raw13 := PA215.Census.C033.records[13]'(by decide)
private theorem row13 : recordAgrees raw13 = true := by
  unfold recordAgrees
  rw [show raw13.siteIndex = 3262 from rfl,lookup3262]
  decide
private def raw14 := PA215.Census.C033.records[14]'(by decide)
private theorem row14 : recordAgrees raw14 = true := by
  unfold recordAgrees
  rw [show raw14.siteIndex = 3263 from rfl,lookup3263]
  decide
private def raw15 := PA215.Census.C033.records[15]'(by decide)
private theorem row15 : recordAgrees raw15 = true := by
  unfold recordAgrees
  rw [show raw15.siteIndex = 3264 from rfl,lookup3264]
  decide
private def raw16 := PA215.Census.C033.records[16]'(by decide)
private theorem row16 : recordAgrees raw16 = true := by
  unfold recordAgrees
  rw [show raw16.siteIndex = 3265 from rfl,lookup3265]
  decide
private def raw17 := PA215.Census.C033.records[17]'(by decide)
private theorem row17 : recordAgrees raw17 = true := by
  unfold recordAgrees
  rw [show raw17.siteIndex = 3266 from rfl,lookup3266]
  decide
private def raw18 := PA215.Census.C033.records[18]'(by decide)
private theorem row18 : recordAgrees raw18 = true := by
  unfold recordAgrees
  rw [show raw18.siteIndex = 3266 from rfl,lookup3266]
  decide
private def raw19 := PA215.Census.C033.records[19]'(by decide)
private theorem row19 : recordAgrees raw19 = true := by
  unfold recordAgrees
  rw [show raw19.siteIndex = 3267 from rfl,lookup3267]
  decide
private def raw20 := PA215.Census.C033.records[20]'(by decide)
private theorem row20 : recordAgrees raw20 = true := by
  unfold recordAgrees
  rw [show raw20.siteIndex = 3268 from rfl,lookup3268]
  decide
private def raw21 := PA215.Census.C033.records[21]'(by decide)
private theorem row21 : recordAgrees raw21 = true := by
  unfold recordAgrees
  rw [show raw21.siteIndex = 3268 from rfl,lookup3268]
  decide
private def raw22 := PA215.Census.C033.records[22]'(by decide)
private theorem row22 : recordAgrees raw22 = true := by
  unfold recordAgrees
  rw [show raw22.siteIndex = 3269 from rfl,lookup3269]
  decide
private def raw23 := PA215.Census.C033.records[23]'(by decide)
private theorem row23 : recordAgrees raw23 = true := by
  unfold recordAgrees
  rw [show raw23.siteIndex = 3270 from rfl,lookup3270]
  decide
private def raw24 := PA215.Census.C033.records[24]'(by decide)
private theorem row24 : recordAgrees raw24 = true := by
  unfold recordAgrees
  rw [show raw24.siteIndex = 3271 from rfl,lookup3271]
  decide
private def raw25 := PA215.Census.C033.records[25]'(by decide)
private theorem row25 : recordAgrees raw25 = true := by
  unfold recordAgrees
  rw [show raw25.siteIndex = 3272 from rfl,lookup3272]
  decide
private def raw26 := PA215.Census.C033.records[26]'(by decide)
private theorem row26 : recordAgrees raw26 = true := by
  unfold recordAgrees
  rw [show raw26.siteIndex = 3272 from rfl,lookup3272]
  decide
private def raw27 := PA215.Census.C033.records[27]'(by decide)
private theorem row27 : recordAgrees raw27 = true := by
  unfold recordAgrees
  rw [show raw27.siteIndex = 3273 from rfl,lookup3273]
  decide
private def raw28 := PA215.Census.C033.records[28]'(by decide)
private theorem row28 : recordAgrees raw28 = true := by
  unfold recordAgrees
  rw [show raw28.siteIndex = 3274 from rfl,lookup3274]
  decide
private def raw29 := PA215.Census.C033.records[29]'(by decide)
private theorem row29 : recordAgrees raw29 = true := by
  unfold recordAgrees
  rw [show raw29.siteIndex = 3275 from rfl,lookup3275]
  decide
private def raw30 := PA215.Census.C033.records[30]'(by decide)
private theorem row30 : recordAgrees raw30 = true := by
  unfold recordAgrees
  rw [show raw30.siteIndex = 3275 from rfl,lookup3275]
  decide
private def raw31 := PA215.Census.C033.records[31]'(by decide)
private theorem row31 : recordAgrees raw31 = true := by
  unfold recordAgrees
  rw [show raw31.siteIndex = 3276 from rfl,lookup3276]
  decide
private def raw32 := PA215.Census.C033.records[32]'(by decide)
private theorem row32 : recordAgrees raw32 = true := by
  unfold recordAgrees
  rw [show raw32.siteIndex = 3277 from rfl,lookup3277]
  decide
private def raw33 := PA215.Census.C033.records[33]'(by decide)
private theorem row33 : recordAgrees raw33 = true := by
  unfold recordAgrees
  rw [show raw33.siteIndex = 3278 from rfl,lookup3278]
  decide
private def raw34 := PA215.Census.C033.records[34]'(by decide)
private theorem row34 : recordAgrees raw34 = true := by
  unfold recordAgrees
  rw [show raw34.siteIndex = 3279 from rfl,lookup3279]
  decide
private def raw35 := PA215.Census.C033.records[35]'(by decide)
private theorem row35 : recordAgrees raw35 = true := by
  unfold recordAgrees
  rw [show raw35.siteIndex = 3279 from rfl,lookup3279]
  decide
private def raw36 := PA215.Census.C033.records[36]'(by decide)
private theorem row36 : recordAgrees raw36 = true := by
  unfold recordAgrees
  rw [show raw36.siteIndex = 3280 from rfl,lookup3280]
  decide
private def raw37 := PA215.Census.C033.records[37]'(by decide)
private theorem row37 : recordAgrees raw37 = true := by
  unfold recordAgrees
  rw [show raw37.siteIndex = 3281 from rfl,lookup3281]
  decide
private def raw38 := PA215.Census.C033.records[38]'(by decide)
private theorem row38 : recordAgrees raw38 = true := by
  unfold recordAgrees
  rw [show raw38.siteIndex = 3282 from rfl,lookup3282]
  decide
private def raw39 := PA215.Census.C033.records[39]'(by decide)
private theorem row39 : recordAgrees raw39 = true := by
  unfold recordAgrees
  rw [show raw39.siteIndex = 3282 from rfl,lookup3282]
  decide
private def raw40 := PA215.Census.C033.records[40]'(by decide)
private theorem row40 : recordAgrees raw40 = true := by
  unfold recordAgrees
  rw [show raw40.siteIndex = 3283 from rfl,lookup3283]
  decide
private def raw41 := PA215.Census.C033.records[41]'(by decide)
private theorem row41 : recordAgrees raw41 = true := by
  unfold recordAgrees
  rw [show raw41.siteIndex = 3284 from rfl,lookup3284]
  decide
private def raw42 := PA215.Census.C033.records[42]'(by decide)
private theorem row42 : recordAgrees raw42 = true := by
  unfold recordAgrees
  rw [show raw42.siteIndex = 3284 from rfl,lookup3284]
  decide
private def raw43 := PA215.Census.C033.records[43]'(by decide)
private theorem row43 : recordAgrees raw43 = true := by
  unfold recordAgrees
  rw [show raw43.siteIndex = 3285 from rfl,lookup3285]
  decide
private def raw44 := PA215.Census.C033.records[44]'(by decide)
private theorem row44 : recordAgrees raw44 = true := by
  unfold recordAgrees
  rw [show raw44.siteIndex = 3286 from rfl,lookup3286]
  decide
private def raw45 := PA215.Census.C033.records[45]'(by decide)
private theorem row45 : recordAgrees raw45 = true := by
  unfold recordAgrees
  rw [show raw45.siteIndex = 3286 from rfl,lookup3286]
  decide
private def raw46 := PA215.Census.C033.records[46]'(by decide)
private theorem row46 : recordAgrees raw46 = true := by
  unfold recordAgrees
  rw [show raw46.siteIndex = 3287 from rfl,lookup3287]
  decide
private def raw47 := PA215.Census.C033.records[47]'(by decide)
private theorem row47 : recordAgrees raw47 = true := by
  unfold recordAgrees
  rw [show raw47.siteIndex = 3288 from rfl,lookup3288]
  decide
private def raw48 := PA215.Census.C033.records[48]'(by decide)
private theorem row48 : recordAgrees raw48 = true := by
  unfold recordAgrees
  rw [show raw48.siteIndex = 3289 from rfl,lookup3289]
  decide
private def raw49 := PA215.Census.C033.records[49]'(by decide)
private theorem row49 : recordAgrees raw49 = true := by
  unfold recordAgrees
  rw [show raw49.siteIndex = 3290 from rfl,lookup3290]
  decide
private def raw50 := PA215.Census.C033.records[50]'(by decide)
private theorem row50 : recordAgrees raw50 = true := by
  unfold recordAgrees
  rw [show raw50.siteIndex = 3290 from rfl,lookup3290]
  decide
private def raw51 := PA215.Census.C033.records[51]'(by decide)
private theorem row51 : recordAgrees raw51 = true := by
  unfold recordAgrees
  rw [show raw51.siteIndex = 3291 from rfl,lookup3291]
  decide
private def raw52 := PA215.Census.C033.records[52]'(by decide)
private theorem row52 : recordAgrees raw52 = true := by
  unfold recordAgrees
  rw [show raw52.siteIndex = 3292 from rfl,lookup3292]
  decide
private def raw53 := PA215.Census.C033.records[53]'(by decide)
private theorem row53 : recordAgrees raw53 = true := by
  unfold recordAgrees
  rw [show raw53.siteIndex = 3293 from rfl,lookup3293]
  decide
private def raw54 := PA215.Census.C033.records[54]'(by decide)
private theorem row54 : recordAgrees raw54 = true := by
  unfold recordAgrees
  rw [show raw54.siteIndex = 3293 from rfl,lookup3293]
  decide
private def raw55 := PA215.Census.C033.records[55]'(by decide)
private theorem row55 : recordAgrees raw55 = true := by
  unfold recordAgrees
  rw [show raw55.siteIndex = 3294 from rfl,lookup3294]
  decide
private def raw56 := PA215.Census.C033.records[56]'(by decide)
private theorem row56 : recordAgrees raw56 = true := by
  unfold recordAgrees
  rw [show raw56.siteIndex = 3295 from rfl,lookup3295]
  decide
private def raw57 := PA215.Census.C033.records[57]'(by decide)
private theorem row57 : recordAgrees raw57 = true := by
  unfold recordAgrees
  rw [show raw57.siteIndex = 3296 from rfl,lookup3296]
  decide
private def raw58 := PA215.Census.C033.records[58]'(by decide)
private theorem row58 : recordAgrees raw58 = true := by
  unfold recordAgrees
  rw [show raw58.siteIndex = 3297 from rfl,lookup3297]
  decide
private def raw59 := PA215.Census.C033.records[59]'(by decide)
private theorem row59 : recordAgrees raw59 = true := by
  unfold recordAgrees
  rw [show raw59.siteIndex = 3297 from rfl,lookup3297]
  decide
private def raw60 := PA215.Census.C033.records[60]'(by decide)
private theorem row60 : recordAgrees raw60 = true := by
  unfold recordAgrees
  rw [show raw60.siteIndex = 3298 from rfl,lookup3298]
  decide
private def raw61 := PA215.Census.C033.records[61]'(by decide)
private theorem row61 : recordAgrees raw61 = true := by
  unfold recordAgrees
  rw [show raw61.siteIndex = 3299 from rfl,lookup3299]
  decide
private def raw62 := PA215.Census.C033.records[62]'(by decide)
private theorem row62 : recordAgrees raw62 = true := by
  unfold recordAgrees
  rw [show raw62.siteIndex = 3299 from rfl,lookup3299]
  decide
private def raw63 := PA215.Census.C033.records[63]'(by decide)
private theorem row63 : recordAgrees raw63 = true := by
  unfold recordAgrees
  rw [show raw63.siteIndex = 3300 from rfl,lookup3300]
  decide
private def raw64 := PA215.Census.C033.records[64]'(by decide)
private theorem row64 : recordAgrees raw64 = true := by
  unfold recordAgrees
  rw [show raw64.siteIndex = 3301 from rfl,lookup3301]
  decide
private def raw65 := PA215.Census.C033.records[65]'(by decide)
private theorem row65 : recordAgrees raw65 = true := by
  unfold recordAgrees
  rw [show raw65.siteIndex = 3302 from rfl,lookup3302]
  decide
private def raw66 := PA215.Census.C033.records[66]'(by decide)
private theorem row66 : recordAgrees raw66 = true := by
  unfold recordAgrees
  rw [show raw66.siteIndex = 3303 from rfl,lookup3303]
  decide
private def raw67 := PA215.Census.C033.records[67]'(by decide)
private theorem row67 : recordAgrees raw67 = true := by
  unfold recordAgrees
  rw [show raw67.siteIndex = 3303 from rfl,lookup3303]
  decide
private def raw68 := PA215.Census.C033.records[68]'(by decide)
private theorem row68 : recordAgrees raw68 = true := by
  unfold recordAgrees
  rw [show raw68.siteIndex = 3304 from rfl,lookup3304]
  decide
private def raw69 := PA215.Census.C033.records[69]'(by decide)
private theorem row69 : recordAgrees raw69 = true := by
  unfold recordAgrees
  rw [show raw69.siteIndex = 3305 from rfl,lookup3305]
  decide
private def raw70 := PA215.Census.C033.records[70]'(by decide)
private theorem row70 : recordAgrees raw70 = true := by
  unfold recordAgrees
  rw [show raw70.siteIndex = 3306 from rfl,lookup3306]
  decide
private def raw71 := PA215.Census.C033.records[71]'(by decide)
private theorem row71 : recordAgrees raw71 = true := by
  unfold recordAgrees
  rw [show raw71.siteIndex = 3307 from rfl,lookup3307]
  decide
private def raw72 := PA215.Census.C033.records[72]'(by decide)
private theorem row72 : recordAgrees raw72 = true := by
  unfold recordAgrees
  rw [show raw72.siteIndex = 3308 from rfl,lookup3308]
  decide
private def raw73 := PA215.Census.C033.records[73]'(by decide)
private theorem row73 : recordAgrees raw73 = true := by
  unfold recordAgrees
  rw [show raw73.siteIndex = 3309 from rfl,lookup3309]
  decide
private def raw74 := PA215.Census.C033.records[74]'(by decide)
private theorem row74 : recordAgrees raw74 = true := by
  unfold recordAgrees
  rw [show raw74.siteIndex = 3309 from rfl,lookup3309]
  decide
private def raw75 := PA215.Census.C033.records[75]'(by decide)
private theorem row75 : recordAgrees raw75 = true := by
  unfold recordAgrees
  rw [show raw75.siteIndex = 3310 from rfl,lookup3310]
  decide
private def raw76 := PA215.Census.C033.records[76]'(by decide)
private theorem row76 : recordAgrees raw76 = true := by
  unfold recordAgrees
  rw [show raw76.siteIndex = 3311 from rfl,lookup3311]
  decide
private def raw77 := PA215.Census.C033.records[77]'(by decide)
private theorem row77 : recordAgrees raw77 = true := by
  unfold recordAgrees
  rw [show raw77.siteIndex = 3312 from rfl,lookup3312]
  decide
private def raw78 := PA215.Census.C033.records[78]'(by decide)
private theorem row78 : recordAgrees raw78 = true := by
  unfold recordAgrees
  rw [show raw78.siteIndex = 3312 from rfl,lookup3312]
  decide
private def raw79 := PA215.Census.C033.records[79]'(by decide)
private theorem row79 : recordAgrees raw79 = true := by
  unfold recordAgrees
  rw [show raw79.siteIndex = 3313 from rfl,lookup3313]
  decide
private def raw80 := PA215.Census.C033.records[80]'(by decide)
private theorem row80 : recordAgrees raw80 = true := by
  unfold recordAgrees
  rw [show raw80.siteIndex = 3314 from rfl,lookup3314]
  decide
private def raw81 := PA215.Census.C033.records[81]'(by decide)
private theorem row81 : recordAgrees raw81 = true := by
  unfold recordAgrees
  rw [show raw81.siteIndex = 3315 from rfl,lookup3315]
  decide
private def raw82 := PA215.Census.C033.records[82]'(by decide)
private theorem row82 : recordAgrees raw82 = true := by
  unfold recordAgrees
  rw [show raw82.siteIndex = 3315 from rfl,lookup3315]
  decide
private def raw83 := PA215.Census.C033.records[83]'(by decide)
private theorem row83 : recordAgrees raw83 = true := by
  unfold recordAgrees
  rw [show raw83.siteIndex = 3316 from rfl,lookup3316]
  decide
private def raw84 := PA215.Census.C033.records[84]'(by decide)
private theorem row84 : recordAgrees raw84 = true := by
  unfold recordAgrees
  rw [show raw84.siteIndex = 3317 from rfl,lookup3317]
  decide
private def raw85 := PA215.Census.C033.records[85]'(by decide)
private theorem row85 : recordAgrees raw85 = true := by
  unfold recordAgrees
  rw [show raw85.siteIndex = 3318 from rfl,lookup3318]
  decide
private def raw86 := PA215.Census.C033.records[86]'(by decide)
private theorem row86 : recordAgrees raw86 = true := by
  unfold recordAgrees
  rw [show raw86.siteIndex = 3319 from rfl,lookup3319]
  decide
private def raw87 := PA215.Census.C033.records[87]'(by decide)
private theorem row87 : recordAgrees raw87 = true := by
  unfold recordAgrees
  rw [show raw87.siteIndex = 3319 from rfl,lookup3319]
  decide
private def raw88 := PA215.Census.C033.records[88]'(by decide)
private theorem row88 : recordAgrees raw88 = true := by
  unfold recordAgrees
  rw [show raw88.siteIndex = 3320 from rfl,lookup3320]
  decide
private def raw89 := PA215.Census.C033.records[89]'(by decide)
private theorem row89 : recordAgrees raw89 = true := by
  unfold recordAgrees
  rw [show raw89.siteIndex = 3321 from rfl,lookup3321]
  decide
private def raw90 := PA215.Census.C033.records[90]'(by decide)
private theorem row90 : recordAgrees raw90 = true := by
  unfold recordAgrees
  rw [show raw90.siteIndex = 3321 from rfl,lookup3321]
  decide
private def raw91 := PA215.Census.C033.records[91]'(by decide)
private theorem row91 : recordAgrees raw91 = true := by
  unfold recordAgrees
  rw [show raw91.siteIndex = 3322 from rfl,lookup3322]
  decide
private def raw92 := PA215.Census.C033.records[92]'(by decide)
private theorem row92 : recordAgrees raw92 = true := by
  unfold recordAgrees
  rw [show raw92.siteIndex = 3323 from rfl,lookup3323]
  decide
private def raw93 := PA215.Census.C033.records[93]'(by decide)
private theorem row93 : recordAgrees raw93 = true := by
  unfold recordAgrees
  rw [show raw93.siteIndex = 3324 from rfl,lookup3324]
  decide
private def raw94 := PA215.Census.C033.records[94]'(by decide)
private theorem row94 : recordAgrees raw94 = true := by
  unfold recordAgrees
  rw [show raw94.siteIndex = 3325 from rfl,lookup3325]
  decide
private def raw95 := PA215.Census.C033.records[95]'(by decide)
private theorem row95 : recordAgrees raw95 = true := by
  unfold recordAgrees
  rw [show raw95.siteIndex = 3325 from rfl,lookup3325]
  decide
private def raw96 := PA215.Census.C033.records[96]'(by decide)
private theorem row96 : recordAgrees raw96 = true := by
  unfold recordAgrees
  rw [show raw96.siteIndex = 3326 from rfl,lookup3326]
  decide
private def raw97 := PA215.Census.C033.records[97]'(by decide)
private theorem row97 : recordAgrees raw97 = true := by
  unfold recordAgrees
  rw [show raw97.siteIndex = 3327 from rfl,lookup3327]
  decide
private def raw98 := PA215.Census.C033.records[98]'(by decide)
private theorem row98 : recordAgrees raw98 = true := by
  unfold recordAgrees
  rw [show raw98.siteIndex = 3328 from rfl,lookup3328]
  decide
private def raw99 := PA215.Census.C033.records[99]'(by decide)
private theorem row99 : recordAgrees raw99 = true := by
  unfold recordAgrees
  rw [show raw99.siteIndex = 3329 from rfl,lookup3329]
  decide
private def raw100 := PA215.Census.C033.records[100]'(by decide)
private theorem row100 : recordAgrees raw100 = true := by
  unfold recordAgrees
  rw [show raw100.siteIndex = 3329 from rfl,lookup3329]
  decide
private def raw101 := PA215.Census.C033.records[101]'(by decide)
private theorem row101 : recordAgrees raw101 = true := by
  unfold recordAgrees
  rw [show raw101.siteIndex = 3330 from rfl,lookup3330]
  decide
private def raw102 := PA215.Census.C033.records[102]'(by decide)
private theorem row102 : recordAgrees raw102 = true := by
  unfold recordAgrees
  rw [show raw102.siteIndex = 3331 from rfl,lookup3331]
  decide
private def raw103 := PA215.Census.C033.records[103]'(by decide)
private theorem row103 : recordAgrees raw103 = true := by
  unfold recordAgrees
  rw [show raw103.siteIndex = 3331 from rfl,lookup3331]
  decide
private def raw104 := PA215.Census.C033.records[104]'(by decide)
private theorem row104 : recordAgrees raw104 = true := by
  unfold recordAgrees
  rw [show raw104.siteIndex = 3332 from rfl,lookup3332]
  decide
private def raw105 := PA215.Census.C033.records[105]'(by decide)
private theorem row105 : recordAgrees raw105 = true := by
  unfold recordAgrees
  rw [show raw105.siteIndex = 3333 from rfl,lookup3333]
  decide
private def raw106 := PA215.Census.C033.records[106]'(by decide)
private theorem row106 : recordAgrees raw106 = true := by
  unfold recordAgrees
  rw [show raw106.siteIndex = 3333 from rfl,lookup3333]
  decide
private def raw107 := PA215.Census.C033.records[107]'(by decide)
private theorem row107 : recordAgrees raw107 = true := by
  unfold recordAgrees
  rw [show raw107.siteIndex = 3334 from rfl,lookup3334]
  decide
private def raw108 := PA215.Census.C033.records[108]'(by decide)
private theorem row108 : recordAgrees raw108 = true := by
  unfold recordAgrees
  rw [show raw108.siteIndex = 3335 from rfl,lookup3335]
  decide
private def raw109 := PA215.Census.C033.records[109]'(by decide)
private theorem row109 : recordAgrees raw109 = true := by
  unfold recordAgrees
  rw [show raw109.siteIndex = 3336 from rfl,lookup3336]
  decide
private def raw110 := PA215.Census.C033.records[110]'(by decide)
private theorem row110 : recordAgrees raw110 = true := by
  unfold recordAgrees
  rw [show raw110.siteIndex = 3337 from rfl,lookup3337]
  decide
private def raw111 := PA215.Census.C033.records[111]'(by decide)
private theorem row111 : recordAgrees raw111 = true := by
  unfold recordAgrees
  rw [show raw111.siteIndex = 3337 from rfl,lookup3337]
  decide
private def raw112 := PA215.Census.C033.records[112]'(by decide)
private theorem row112 : recordAgrees raw112 = true := by
  unfold recordAgrees
  rw [show raw112.siteIndex = 3338 from rfl,lookup3338]
  decide
private def raw113 := PA215.Census.C033.records[113]'(by decide)
private theorem row113 : recordAgrees raw113 = true := by
  unfold recordAgrees
  rw [show raw113.siteIndex = 3339 from rfl,lookup3339]
  decide
private def raw114 := PA215.Census.C033.records[114]'(by decide)
private theorem row114 : recordAgrees raw114 = true := by
  unfold recordAgrees
  rw [show raw114.siteIndex = 3340 from rfl,lookup3340]
  decide
private def raw115 := PA215.Census.C033.records[115]'(by decide)
private theorem row115 : recordAgrees raw115 = true := by
  unfold recordAgrees
  rw [show raw115.siteIndex = 3340 from rfl,lookup3340]
  decide
private def raw116 := PA215.Census.C033.records[116]'(by decide)
private theorem row116 : recordAgrees raw116 = true := by
  unfold recordAgrees
  rw [show raw116.siteIndex = 3341 from rfl,lookup3341]
  decide
private def raw117 := PA215.Census.C033.records[117]'(by decide)
private theorem row117 : recordAgrees raw117 = true := by
  unfold recordAgrees
  rw [show raw117.siteIndex = 3342 from rfl,lookup3342]
  decide
private def raw118 := PA215.Census.C033.records[118]'(by decide)
private theorem row118 : recordAgrees raw118 = true := by
  unfold recordAgrees
  rw [show raw118.siteIndex = 3343 from rfl,lookup3343]
  decide
private def raw119 := PA215.Census.C033.records[119]'(by decide)
private theorem row119 : recordAgrees raw119 = true := by
  unfold recordAgrees
  rw [show raw119.siteIndex = 3344 from rfl,lookup3344]
  decide
private def raw120 := PA215.Census.C033.records[120]'(by decide)
private theorem row120 : recordAgrees raw120 = true := by
  unfold recordAgrees
  rw [show raw120.siteIndex = 3344 from rfl,lookup3344]
  decide
private def raw121 := PA215.Census.C033.records[121]'(by decide)
private theorem row121 : recordAgrees raw121 = true := by
  unfold recordAgrees
  rw [show raw121.siteIndex = 3345 from rfl,lookup3345]
  decide
private def raw122 := PA215.Census.C033.records[122]'(by decide)
private theorem row122 : recordAgrees raw122 = true := by
  unfold recordAgrees
  rw [show raw122.siteIndex = 3346 from rfl,lookup3346]
  decide
private def raw123 := PA215.Census.C033.records[123]'(by decide)
private theorem row123 : recordAgrees raw123 = true := by
  unfold recordAgrees
  rw [show raw123.siteIndex = 3346 from rfl,lookup3346]
  decide
private def raw124 := PA215.Census.C033.records[124]'(by decide)
private theorem row124 : recordAgrees raw124 = true := by
  unfold recordAgrees
  rw [show raw124.siteIndex = 3347 from rfl,lookup3347]
  decide
private def raw125 := PA215.Census.C033.records[125]'(by decide)
private theorem row125 : recordAgrees raw125 = true := by
  unfold recordAgrees
  rw [show raw125.siteIndex = 3348 from rfl,lookup3348]
  decide
private def raw126 := PA215.Census.C033.records[126]'(by decide)
private theorem row126 : recordAgrees raw126 = true := by
  unfold recordAgrees
  rw [show raw126.siteIndex = 3349 from rfl,lookup3349]
  decide
private def raw127 := PA215.Census.C033.records[127]'(by decide)
private theorem row127 : recordAgrees raw127 = true := by
  unfold recordAgrees
  rw [show raw127.siteIndex = 3350 from rfl,lookup3350]
  decide
private theorem enumeration : PA215.Census.C033.records.toList = [raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7,raw8,raw9,raw10,raw11,raw12,raw13,raw14,raw15,raw16,raw17,raw18,raw19,raw20,raw21,raw22,raw23,raw24,raw25,raw26,raw27,raw28,raw29,raw30,raw31,raw32,raw33,raw34,raw35,raw36,raw37,raw38,raw39,raw40,raw41,raw42,raw43,raw44,raw45,raw46,raw47,raw48,raw49,raw50,raw51,raw52,raw53,raw54,raw55,raw56,raw57,raw58,raw59,raw60,raw61,raw62,raw63,raw64,raw65,raw66,raw67,raw68,raw69,raw70,raw71,raw72,raw73,raw74,raw75,raw76,raw77,raw78,raw79,raw80,raw81,raw82,raw83,raw84,raw85,raw86,raw87,raw88,raw89,raw90,raw91,raw92,raw93,raw94,raw95,raw96,raw97,raw98,raw99,raw100,raw101,raw102,raw103,raw104,raw105,raw106,raw107,raw108,raw109,raw110,raw111,raw112,raw113,raw114,raw115,raw116,raw117,raw118,raw119,raw120,raw121,raw122,raw123,raw124,raw125,raw126,raw127] := by rfl
theorem checked : PA215.Census.C033.records.toList.all recordAgrees = true := by
  rw [enumeration]
  simp only [List.all_cons,List.all_nil,row0,row1,row2,row3,row4,row5,row6,row7,row8,row9,row10,row11,row12,row13,row14,row15,row16,row17,row18,row19,row20,row21,row22,row23,row24,row25,row26,row27,row28,row29,row30,row31,row32,row33,row34,row35,row36,row37,row38,row39,row40,row41,row42,row43,row44,row45,row46,row47,row48,row49,row50,row51,row52,row53,row54,row55,row56,row57,row58,row59,row60,row61,row62,row63,row64,row65,row66,row67,row68,row69,row70,row71,row72,row73,row74,row75,row76,row77,row78,row79,row80,row81,row82,row83,row84,row85,row86,row87,row88,row89,row90,row91,row92,row93,row94,row95,row96,row97,row98,row99,row100,row101,row102,row103,row104,row105,row106,row107,row108,row109,row110,row111,row112,row113,row114,row115,row116,row117,row118,row119,row120,row121,row122,row123,row124,row125,row126,row127,Bool.and_self]
#print axioms checked
end PA215.Source.CensusJoin.J033
