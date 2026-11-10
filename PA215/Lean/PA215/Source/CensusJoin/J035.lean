import PA215.Source.ContractJoinPilot
import PA215.Census.C035
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace PA215.Source.CensusJoin.J035
private def site3449 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,false,false,true,false,true,true,false,true,true,true],.continueTo 2⟩
private theorem lookup3449 : exactSites[3449]? = some site3449 := by rfl
private def site3450 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,false,false,true,false,true,true,true],.continueTo 3⟩
private theorem lookup3450 : exactSites[3450]? = some site3450 := by rfl
private def site3451 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,false,false,true,true,false],.dec 7⟩
private theorem lookup3451 : exactSites[3451]? = some site3451 := by rfl
private def site3452 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,false,false,true,true,true,false,false,false],.inc 1⟩
private theorem lookup3452 : exactSites[3452]? = some site3452 := by rfl
private def site3453 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,false,false,true,true,true,false,false,true],.inc 1⟩
private theorem lookup3453 : exactSites[3453]? = some site3453 := by rfl
private def site3454 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,false,false,true,true,true,false,true,false],.inc 1⟩
private theorem lookup3454 : exactSites[3454]? = some site3454 := by rfl
private def site3455 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,false,false,true,true,true,false,true,true],.inc 1⟩
private theorem lookup3455 : exactSites[3455]? = some site3455 := by rfl
private def site3456 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,false,false,true,true,true,true],.continueTo 2⟩
private theorem lookup3456 : exactSites[3456]? = some site3456 := by rfl
private def site3457 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,false,true,false],.inc 1⟩
private theorem lookup3457 : exactSites[3457]? = some site3457 := by rfl
private def site3458 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,false,true,true],.inc 1⟩
private theorem lookup3458 : exactSites[3458]? = some site3458 := by rfl
private def site3459 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,true,false,false,false],.dec 1⟩
private theorem lookup3459 : exactSites[3459]? = some site3459 := by rfl
private def site3460 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,true,false,false,true,false],.inc 6⟩
private theorem lookup3460 : exactSites[3460]? = some site3460 := by rfl
private def site3461 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,true,false,false,true,true],.continueTo 2⟩
private theorem lookup3461 : exactSites[3461]? = some site3461 := by rfl
private def site3462 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,true,false,true,false,false],.dec 2⟩
private theorem lookup3462 : exactSites[3462]? = some site3462 := by rfl
private def site3463 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,true,false,true,false,true,false],.inc 1⟩
private theorem lookup3463 : exactSites[3463]? = some site3463 := by rfl
private def site3464 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,true,false,true,false,true,true],.continueTo 2⟩
private theorem lookup3464 : exactSites[3464]? = some site3464 := by rfl
private def site3465 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,true,false,true,true,false,false,false],.dec 1⟩
private theorem lookup3465 : exactSites[3465]? = some site3465 := by rfl
private def site3466 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,true,false,true,true,false,false,true,false],.inc 7⟩
private theorem lookup3466 : exactSites[3466]? = some site3466 := by rfl
private def site3467 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,true,false,true,true,false,false,true,true,false],.inc 6⟩
private theorem lookup3467 : exactSites[3467]? = some site3467 := by rfl
private def site3468 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,true,false,true,true,false,false,true,true,true],.continueTo 3⟩
private theorem lookup3468 : exactSites[3468]? = some site3468 := by rfl
private def site3469 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,true,false,true,true,false,true,false],.dec 6⟩
private theorem lookup3469 : exactSites[3469]? = some site3469 := by rfl
private def site3470 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,true,false,true,true,false,true,true,false,false],.inc 7⟩
private theorem lookup3470 : exactSites[3470]? = some site3470 := by rfl
private def site3471 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,true,false,true,true,false,true,true,false,true,false],.dec 6⟩
private theorem lookup3471 : exactSites[3471]? = some site3471 := by rfl
private def site3472 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,true,false,true,true,false,true,true,false,true,true,false],.inc 1⟩
private theorem lookup3472 : exactSites[3472]? = some site3472 := by rfl
private def site3473 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,true,false,true,true,false,true,true,false,true,true,true],.continueTo 2⟩
private theorem lookup3473 : exactSites[3473]? = some site3473 := by rfl
private def site3474 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,true,false,true,true,false,true,true,true],.continueTo 3⟩
private theorem lookup3474 : exactSites[3474]? = some site3474 := by rfl
private def site3475 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,true,false,true,true,true,false],.dec 7⟩
private theorem lookup3475 : exactSites[3475]? = some site3475 := by rfl
private def site3476 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,true,false,true,true,true,true,false],.inc 2⟩
private theorem lookup3476 : exactSites[3476]? = some site3476 := by rfl
private def site3477 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,true,false,true,true,true,true,true],.continueTo 2⟩
private theorem lookup3477 : exactSites[3477]? = some site3477 := by rfl
private def site3478 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,true,true,false,false],.dec 3⟩
private theorem lookup3478 : exactSites[3478]? = some site3478 := by rfl
private def site3479 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,true,true,false,true,false],.inc 1⟩
private theorem lookup3479 : exactSites[3479]? = some site3479 := by rfl
private def site3480 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,true,true,false,true,true,false],.inc 6⟩
private theorem lookup3480 : exactSites[3480]? = some site3480 := by rfl
private def site3481 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,true,true,false,true,true,true],.continueTo 3⟩
private theorem lookup3481 : exactSites[3481]? = some site3481 := by rfl
private def site3482 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,true,true,true,false],.dec 6⟩
private theorem lookup3482 : exactSites[3482]? = some site3482 := by rfl
private def site3483 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,true,true,true,true,false],.inc 3⟩
private theorem lookup3483 : exactSites[3483]? = some site3483 := by rfl
private def site3484 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,false,true,true,true,true,true],.continueTo 2⟩
private theorem lookup3484 : exactSites[3484]? = some site3484 := by rfl
private def site3485 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,false,false,false,false],.dec 1⟩
private theorem lookup3485 : exactSites[3485]? = some site3485 := by rfl
private def site3486 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,false,false,false,true,false],.inc 6⟩
private theorem lookup3486 : exactSites[3486]? = some site3486 := by rfl
private def site3487 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,false,false,false,true,true],.continueTo 2⟩
private theorem lookup3487 : exactSites[3487]? = some site3487 := by rfl
private def site3488 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,false,false,true,false,false],.dec 2⟩
private theorem lookup3488 : exactSites[3488]? = some site3488 := by rfl
private def site3489 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,false,false,true,false,true,false],.inc 1⟩
private theorem lookup3489 : exactSites[3489]? = some site3489 := by rfl
private def site3490 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,false,false,true,false,true,true],.continueTo 2⟩
private theorem lookup3490 : exactSites[3490]? = some site3490 := by rfl
private def site3491 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,false,false,true,true,false,false,false],.dec 1⟩
private theorem lookup3491 : exactSites[3491]? = some site3491 := by rfl
private def site3492 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,false,false,true,true,false,false,true,false],.inc 7⟩
private theorem lookup3492 : exactSites[3492]? = some site3492 := by rfl
private def site3493 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,false,false,true,true,false,false,true,true,false],.inc 6⟩
private theorem lookup3493 : exactSites[3493]? = some site3493 := by rfl
private def site3494 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,false,false,true,true,false,false,true,true,true],.continueTo 3⟩
private theorem lookup3494 : exactSites[3494]? = some site3494 := by rfl
private def site3495 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,false,false,true,true,false,true,false],.dec 6⟩
private theorem lookup3495 : exactSites[3495]? = some site3495 := by rfl
private def site3496 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,false,false,true,true,false,true,true,false,false],.inc 7⟩
private theorem lookup3496 : exactSites[3496]? = some site3496 := by rfl
private def site3497 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,false,false,true,true,false,true,true,false,true,false],.dec 6⟩
private theorem lookup3497 : exactSites[3497]? = some site3497 := by rfl
private def site3498 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,false,false,true,true,false,true,true,false,true,true,false],.inc 1⟩
private theorem lookup3498 : exactSites[3498]? = some site3498 := by rfl
private def site3499 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,false,false,true,true,false,true,true,false,true,true,true],.continueTo 2⟩
private theorem lookup3499 : exactSites[3499]? = some site3499 := by rfl
private def site3500 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,false,false,true,true,false,true,true,true],.continueTo 3⟩
private theorem lookup3500 : exactSites[3500]? = some site3500 := by rfl
private def site3501 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,false,false,true,true,true,false],.dec 7⟩
private theorem lookup3501 : exactSites[3501]? = some site3501 := by rfl
private def site3502 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,false,false,true,true,true,true,false],.inc 2⟩
private theorem lookup3502 : exactSites[3502]? = some site3502 := by rfl
private def site3503 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,false,false,true,true,true,true,true],.continueTo 2⟩
private theorem lookup3503 : exactSites[3503]? = some site3503 := by rfl
private def site3504 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,false,true,false,false],.dec 3⟩
private theorem lookup3504 : exactSites[3504]? = some site3504 := by rfl
private def site3505 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,false,true,false,true,false],.inc 1⟩
private theorem lookup3505 : exactSites[3505]? = some site3505 := by rfl
private def site3506 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,false,true,false,true,true,false],.inc 6⟩
private theorem lookup3506 : exactSites[3506]? = some site3506 := by rfl
private def site3507 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,false,true,false,true,true,true],.continueTo 3⟩
private theorem lookup3507 : exactSites[3507]? = some site3507 := by rfl
private def site3508 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,false,true,true,false],.dec 6⟩
private theorem lookup3508 : exactSites[3508]? = some site3508 := by rfl
private def site3509 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,false,true,true,true,false],.inc 3⟩
private theorem lookup3509 : exactSites[3509]? = some site3509 := by rfl
private def site3510 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,false,true,true,true,true],.continueTo 2⟩
private theorem lookup3510 : exactSites[3510]? = some site3510 := by rfl
private def site3511 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,true,false,false,false],.dec 1⟩
private theorem lookup3511 : exactSites[3511]? = some site3511 := by rfl
private def site3512 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,true,false,false,true,false],.inc 6⟩
private theorem lookup3512 : exactSites[3512]? = some site3512 := by rfl
private def site3513 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,true,false,false,true,true],.continueTo 2⟩
private theorem lookup3513 : exactSites[3513]? = some site3513 := by rfl
private def site3514 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,true,false,true,false,false],.dec 2⟩
private theorem lookup3514 : exactSites[3514]? = some site3514 := by rfl
private def site3515 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,true,false,true,false,true,false],.inc 1⟩
private theorem lookup3515 : exactSites[3515]? = some site3515 := by rfl
private def site3516 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,true,false,true,false,true,true],.continueTo 2⟩
private theorem lookup3516 : exactSites[3516]? = some site3516 := by rfl
private def site3517 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,true,false,true,true,false,false,false],.dec 1⟩
private theorem lookup3517 : exactSites[3517]? = some site3517 := by rfl
private def site3518 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,true,false,true,true,false,false,true,false],.inc 7⟩
private theorem lookup3518 : exactSites[3518]? = some site3518 := by rfl
private def site3519 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,true,false,true,true,false,false,true,true,false],.inc 6⟩
private theorem lookup3519 : exactSites[3519]? = some site3519 := by rfl
private def site3520 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,true,false,true,true,false,false,true,true,true],.continueTo 3⟩
private theorem lookup3520 : exactSites[3520]? = some site3520 := by rfl
private def site3521 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,true,false,true,true,false,true,false],.dec 6⟩
private theorem lookup3521 : exactSites[3521]? = some site3521 := by rfl
private def site3522 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,true,false,true,true,false,true,true,false,false],.inc 7⟩
private theorem lookup3522 : exactSites[3522]? = some site3522 := by rfl
private def site3523 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,true,false,true,true,false,true,true,false,true,false],.dec 6⟩
private theorem lookup3523 : exactSites[3523]? = some site3523 := by rfl
private def site3524 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,true,false,true,true,false,true,true,false,true,true,false],.inc 1⟩
private theorem lookup3524 : exactSites[3524]? = some site3524 := by rfl
private def site3525 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,true,false,true,true,false,true,true,false,true,true,true],.continueTo 2⟩
private theorem lookup3525 : exactSites[3525]? = some site3525 := by rfl
private def site3526 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,true,false,true,true,false,true,true,true],.continueTo 3⟩
private theorem lookup3526 : exactSites[3526]? = some site3526 := by rfl
private def site3527 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,true,false,true,true,true,false],.dec 7⟩
private theorem lookup3527 : exactSites[3527]? = some site3527 := by rfl
private def site3528 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,true,false,true,true,true,true,false],.inc 2⟩
private theorem lookup3528 : exactSites[3528]? = some site3528 := by rfl
private def site3529 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,true,false,true,true,true,true,true],.continueTo 2⟩
private theorem lookup3529 : exactSites[3529]? = some site3529 := by rfl
private def site3530 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,true,true,false,false],.dec 5⟩
private theorem lookup3530 : exactSites[3530]? = some site3530 := by rfl
private def site3531 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,true,true,false,true,false],.inc 1⟩
private theorem lookup3531 : exactSites[3531]? = some site3531 := by rfl
private def site3532 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,true,true,false,true,true,false],.inc 6⟩
private theorem lookup3532 : exactSites[3532]? = some site3532 := by rfl
private def site3533 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,true,true,false,true,true,true],.continueTo 3⟩
private theorem lookup3533 : exactSites[3533]? = some site3533 := by rfl
private def site3534 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,true,true,true,false],.dec 6⟩
private theorem lookup3534 : exactSites[3534]? = some site3534 := by rfl
private def site3535 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,true,true,true,true,false],.inc 5⟩
private theorem lookup3535 : exactSites[3535]? = some site3535 := by rfl
private def site3536 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,false,true,true,true,true,true],.continueTo 2⟩
private theorem lookup3536 : exactSites[3536]? = some site3536 := by rfl
private def site3537 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,true,false,false,false,false],.dec 2⟩
private theorem lookup3537 : exactSites[3537]? = some site3537 := by rfl
private def site3538 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,true,false,false,false,true,false],.inc 7⟩
private theorem lookup3538 : exactSites[3538]? = some site3538 := by rfl
private def site3539 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,true,false,false,false,true,true,false,false,false],.dec 6⟩
private theorem lookup3539 : exactSites[3539]? = some site3539 := by rfl
private def site3540 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,true,false,false,false,true,true,false,false,true],.breakTo 1⟩
private theorem lookup3540 : exactSites[3540]? = some site3540 := by rfl
private def site3541 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,true,false,false,false,true,true,false,true,false],.dec 7⟩
private theorem lookup3541 : exactSites[3541]? = some site3541 := by rfl
private def site3542 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,true,false,false,false,true,true,false,true,true,false],.inc 6⟩
private theorem lookup3542 : exactSites[3542]? = some site3542 := by rfl
private def site3543 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,true,false,false,false,true,true,false,true,true,true],.continueTo 2⟩
private theorem lookup3543 : exactSites[3543]? = some site3543 := by rfl
private def site3544 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,true,false,false,false,true,true,true],.continueTo 3⟩
private theorem lookup3544 : exactSites[3544]? = some site3544 := by rfl
private def site3545 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,true,false,false,true,false],.dec 7⟩
private theorem lookup3545 : exactSites[3545]? = some site3545 := by rfl
private def site3546 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,true,false,false,true,true,false],.inc 2⟩
private theorem lookup3546 : exactSites[3546]? = some site3546 := by rfl
private def site3547 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,true,false,true,true,false,true,false,false,true,true,true],.continueTo 2⟩
private theorem lookup3547 : exactSites[3547]? = some site3547 := by rfl
private def raw0 := PA215.Census.C035.records[0]'(by decide)
private theorem row0 : recordAgrees raw0 = true := by
  unfold recordAgrees
  rw [show raw0.siteIndex = 3449 from rfl,lookup3449]
  decide
private def raw1 := PA215.Census.C035.records[1]'(by decide)
private theorem row1 : recordAgrees raw1 = true := by
  unfold recordAgrees
  rw [show raw1.siteIndex = 3450 from rfl,lookup3450]
  decide
private def raw2 := PA215.Census.C035.records[2]'(by decide)
private theorem row2 : recordAgrees raw2 = true := by
  unfold recordAgrees
  rw [show raw2.siteIndex = 3451 from rfl,lookup3451]
  decide
private def raw3 := PA215.Census.C035.records[3]'(by decide)
private theorem row3 : recordAgrees raw3 = true := by
  unfold recordAgrees
  rw [show raw3.siteIndex = 3451 from rfl,lookup3451]
  decide
private def raw4 := PA215.Census.C035.records[4]'(by decide)
private theorem row4 : recordAgrees raw4 = true := by
  unfold recordAgrees
  rw [show raw4.siteIndex = 3452 from rfl,lookup3452]
  decide
private def raw5 := PA215.Census.C035.records[5]'(by decide)
private theorem row5 : recordAgrees raw5 = true := by
  unfold recordAgrees
  rw [show raw5.siteIndex = 3453 from rfl,lookup3453]
  decide
private def raw6 := PA215.Census.C035.records[6]'(by decide)
private theorem row6 : recordAgrees raw6 = true := by
  unfold recordAgrees
  rw [show raw6.siteIndex = 3454 from rfl,lookup3454]
  decide
private def raw7 := PA215.Census.C035.records[7]'(by decide)
private theorem row7 : recordAgrees raw7 = true := by
  unfold recordAgrees
  rw [show raw7.siteIndex = 3455 from rfl,lookup3455]
  decide
private def raw8 := PA215.Census.C035.records[8]'(by decide)
private theorem row8 : recordAgrees raw8 = true := by
  unfold recordAgrees
  rw [show raw8.siteIndex = 3456 from rfl,lookup3456]
  decide
private def raw9 := PA215.Census.C035.records[9]'(by decide)
private theorem row9 : recordAgrees raw9 = true := by
  unfold recordAgrees
  rw [show raw9.siteIndex = 3457 from rfl,lookup3457]
  decide
private def raw10 := PA215.Census.C035.records[10]'(by decide)
private theorem row10 : recordAgrees raw10 = true := by
  unfold recordAgrees
  rw [show raw10.siteIndex = 3458 from rfl,lookup3458]
  decide
private def raw11 := PA215.Census.C035.records[11]'(by decide)
private theorem row11 : recordAgrees raw11 = true := by
  unfold recordAgrees
  rw [show raw11.siteIndex = 3459 from rfl,lookup3459]
  decide
private def raw12 := PA215.Census.C035.records[12]'(by decide)
private theorem row12 : recordAgrees raw12 = true := by
  unfold recordAgrees
  rw [show raw12.siteIndex = 3459 from rfl,lookup3459]
  decide
private def raw13 := PA215.Census.C035.records[13]'(by decide)
private theorem row13 : recordAgrees raw13 = true := by
  unfold recordAgrees
  rw [show raw13.siteIndex = 3460 from rfl,lookup3460]
  decide
private def raw14 := PA215.Census.C035.records[14]'(by decide)
private theorem row14 : recordAgrees raw14 = true := by
  unfold recordAgrees
  rw [show raw14.siteIndex = 3461 from rfl,lookup3461]
  decide
private def raw15 := PA215.Census.C035.records[15]'(by decide)
private theorem row15 : recordAgrees raw15 = true := by
  unfold recordAgrees
  rw [show raw15.siteIndex = 3462 from rfl,lookup3462]
  decide
private def raw16 := PA215.Census.C035.records[16]'(by decide)
private theorem row16 : recordAgrees raw16 = true := by
  unfold recordAgrees
  rw [show raw16.siteIndex = 3462 from rfl,lookup3462]
  decide
private def raw17 := PA215.Census.C035.records[17]'(by decide)
private theorem row17 : recordAgrees raw17 = true := by
  unfold recordAgrees
  rw [show raw17.siteIndex = 3463 from rfl,lookup3463]
  decide
private def raw18 := PA215.Census.C035.records[18]'(by decide)
private theorem row18 : recordAgrees raw18 = true := by
  unfold recordAgrees
  rw [show raw18.siteIndex = 3464 from rfl,lookup3464]
  decide
private def raw19 := PA215.Census.C035.records[19]'(by decide)
private theorem row19 : recordAgrees raw19 = true := by
  unfold recordAgrees
  rw [show raw19.siteIndex = 3465 from rfl,lookup3465]
  decide
private def raw20 := PA215.Census.C035.records[20]'(by decide)
private theorem row20 : recordAgrees raw20 = true := by
  unfold recordAgrees
  rw [show raw20.siteIndex = 3465 from rfl,lookup3465]
  decide
private def raw21 := PA215.Census.C035.records[21]'(by decide)
private theorem row21 : recordAgrees raw21 = true := by
  unfold recordAgrees
  rw [show raw21.siteIndex = 3466 from rfl,lookup3466]
  decide
private def raw22 := PA215.Census.C035.records[22]'(by decide)
private theorem row22 : recordAgrees raw22 = true := by
  unfold recordAgrees
  rw [show raw22.siteIndex = 3467 from rfl,lookup3467]
  decide
private def raw23 := PA215.Census.C035.records[23]'(by decide)
private theorem row23 : recordAgrees raw23 = true := by
  unfold recordAgrees
  rw [show raw23.siteIndex = 3468 from rfl,lookup3468]
  decide
private def raw24 := PA215.Census.C035.records[24]'(by decide)
private theorem row24 : recordAgrees raw24 = true := by
  unfold recordAgrees
  rw [show raw24.siteIndex = 3469 from rfl,lookup3469]
  decide
private def raw25 := PA215.Census.C035.records[25]'(by decide)
private theorem row25 : recordAgrees raw25 = true := by
  unfold recordAgrees
  rw [show raw25.siteIndex = 3469 from rfl,lookup3469]
  decide
private def raw26 := PA215.Census.C035.records[26]'(by decide)
private theorem row26 : recordAgrees raw26 = true := by
  unfold recordAgrees
  rw [show raw26.siteIndex = 3470 from rfl,lookup3470]
  decide
private def raw27 := PA215.Census.C035.records[27]'(by decide)
private theorem row27 : recordAgrees raw27 = true := by
  unfold recordAgrees
  rw [show raw27.siteIndex = 3471 from rfl,lookup3471]
  decide
private def raw28 := PA215.Census.C035.records[28]'(by decide)
private theorem row28 : recordAgrees raw28 = true := by
  unfold recordAgrees
  rw [show raw28.siteIndex = 3471 from rfl,lookup3471]
  decide
private def raw29 := PA215.Census.C035.records[29]'(by decide)
private theorem row29 : recordAgrees raw29 = true := by
  unfold recordAgrees
  rw [show raw29.siteIndex = 3472 from rfl,lookup3472]
  decide
private def raw30 := PA215.Census.C035.records[30]'(by decide)
private theorem row30 : recordAgrees raw30 = true := by
  unfold recordAgrees
  rw [show raw30.siteIndex = 3473 from rfl,lookup3473]
  decide
private def raw31 := PA215.Census.C035.records[31]'(by decide)
private theorem row31 : recordAgrees raw31 = true := by
  unfold recordAgrees
  rw [show raw31.siteIndex = 3474 from rfl,lookup3474]
  decide
private def raw32 := PA215.Census.C035.records[32]'(by decide)
private theorem row32 : recordAgrees raw32 = true := by
  unfold recordAgrees
  rw [show raw32.siteIndex = 3475 from rfl,lookup3475]
  decide
private def raw33 := PA215.Census.C035.records[33]'(by decide)
private theorem row33 : recordAgrees raw33 = true := by
  unfold recordAgrees
  rw [show raw33.siteIndex = 3475 from rfl,lookup3475]
  decide
private def raw34 := PA215.Census.C035.records[34]'(by decide)
private theorem row34 : recordAgrees raw34 = true := by
  unfold recordAgrees
  rw [show raw34.siteIndex = 3476 from rfl,lookup3476]
  decide
private def raw35 := PA215.Census.C035.records[35]'(by decide)
private theorem row35 : recordAgrees raw35 = true := by
  unfold recordAgrees
  rw [show raw35.siteIndex = 3477 from rfl,lookup3477]
  decide
private def raw36 := PA215.Census.C035.records[36]'(by decide)
private theorem row36 : recordAgrees raw36 = true := by
  unfold recordAgrees
  rw [show raw36.siteIndex = 3478 from rfl,lookup3478]
  decide
private def raw37 := PA215.Census.C035.records[37]'(by decide)
private theorem row37 : recordAgrees raw37 = true := by
  unfold recordAgrees
  rw [show raw37.siteIndex = 3478 from rfl,lookup3478]
  decide
private def raw38 := PA215.Census.C035.records[38]'(by decide)
private theorem row38 : recordAgrees raw38 = true := by
  unfold recordAgrees
  rw [show raw38.siteIndex = 3479 from rfl,lookup3479]
  decide
private def raw39 := PA215.Census.C035.records[39]'(by decide)
private theorem row39 : recordAgrees raw39 = true := by
  unfold recordAgrees
  rw [show raw39.siteIndex = 3480 from rfl,lookup3480]
  decide
private def raw40 := PA215.Census.C035.records[40]'(by decide)
private theorem row40 : recordAgrees raw40 = true := by
  unfold recordAgrees
  rw [show raw40.siteIndex = 3481 from rfl,lookup3481]
  decide
private def raw41 := PA215.Census.C035.records[41]'(by decide)
private theorem row41 : recordAgrees raw41 = true := by
  unfold recordAgrees
  rw [show raw41.siteIndex = 3482 from rfl,lookup3482]
  decide
private def raw42 := PA215.Census.C035.records[42]'(by decide)
private theorem row42 : recordAgrees raw42 = true := by
  unfold recordAgrees
  rw [show raw42.siteIndex = 3482 from rfl,lookup3482]
  decide
private def raw43 := PA215.Census.C035.records[43]'(by decide)
private theorem row43 : recordAgrees raw43 = true := by
  unfold recordAgrees
  rw [show raw43.siteIndex = 3483 from rfl,lookup3483]
  decide
private def raw44 := PA215.Census.C035.records[44]'(by decide)
private theorem row44 : recordAgrees raw44 = true := by
  unfold recordAgrees
  rw [show raw44.siteIndex = 3484 from rfl,lookup3484]
  decide
private def raw45 := PA215.Census.C035.records[45]'(by decide)
private theorem row45 : recordAgrees raw45 = true := by
  unfold recordAgrees
  rw [show raw45.siteIndex = 3485 from rfl,lookup3485]
  decide
private def raw46 := PA215.Census.C035.records[46]'(by decide)
private theorem row46 : recordAgrees raw46 = true := by
  unfold recordAgrees
  rw [show raw46.siteIndex = 3485 from rfl,lookup3485]
  decide
private def raw47 := PA215.Census.C035.records[47]'(by decide)
private theorem row47 : recordAgrees raw47 = true := by
  unfold recordAgrees
  rw [show raw47.siteIndex = 3486 from rfl,lookup3486]
  decide
private def raw48 := PA215.Census.C035.records[48]'(by decide)
private theorem row48 : recordAgrees raw48 = true := by
  unfold recordAgrees
  rw [show raw48.siteIndex = 3487 from rfl,lookup3487]
  decide
private def raw49 := PA215.Census.C035.records[49]'(by decide)
private theorem row49 : recordAgrees raw49 = true := by
  unfold recordAgrees
  rw [show raw49.siteIndex = 3488 from rfl,lookup3488]
  decide
private def raw50 := PA215.Census.C035.records[50]'(by decide)
private theorem row50 : recordAgrees raw50 = true := by
  unfold recordAgrees
  rw [show raw50.siteIndex = 3488 from rfl,lookup3488]
  decide
private def raw51 := PA215.Census.C035.records[51]'(by decide)
private theorem row51 : recordAgrees raw51 = true := by
  unfold recordAgrees
  rw [show raw51.siteIndex = 3489 from rfl,lookup3489]
  decide
private def raw52 := PA215.Census.C035.records[52]'(by decide)
private theorem row52 : recordAgrees raw52 = true := by
  unfold recordAgrees
  rw [show raw52.siteIndex = 3490 from rfl,lookup3490]
  decide
private def raw53 := PA215.Census.C035.records[53]'(by decide)
private theorem row53 : recordAgrees raw53 = true := by
  unfold recordAgrees
  rw [show raw53.siteIndex = 3491 from rfl,lookup3491]
  decide
private def raw54 := PA215.Census.C035.records[54]'(by decide)
private theorem row54 : recordAgrees raw54 = true := by
  unfold recordAgrees
  rw [show raw54.siteIndex = 3491 from rfl,lookup3491]
  decide
private def raw55 := PA215.Census.C035.records[55]'(by decide)
private theorem row55 : recordAgrees raw55 = true := by
  unfold recordAgrees
  rw [show raw55.siteIndex = 3492 from rfl,lookup3492]
  decide
private def raw56 := PA215.Census.C035.records[56]'(by decide)
private theorem row56 : recordAgrees raw56 = true := by
  unfold recordAgrees
  rw [show raw56.siteIndex = 3493 from rfl,lookup3493]
  decide
private def raw57 := PA215.Census.C035.records[57]'(by decide)
private theorem row57 : recordAgrees raw57 = true := by
  unfold recordAgrees
  rw [show raw57.siteIndex = 3494 from rfl,lookup3494]
  decide
private def raw58 := PA215.Census.C035.records[58]'(by decide)
private theorem row58 : recordAgrees raw58 = true := by
  unfold recordAgrees
  rw [show raw58.siteIndex = 3495 from rfl,lookup3495]
  decide
private def raw59 := PA215.Census.C035.records[59]'(by decide)
private theorem row59 : recordAgrees raw59 = true := by
  unfold recordAgrees
  rw [show raw59.siteIndex = 3495 from rfl,lookup3495]
  decide
private def raw60 := PA215.Census.C035.records[60]'(by decide)
private theorem row60 : recordAgrees raw60 = true := by
  unfold recordAgrees
  rw [show raw60.siteIndex = 3496 from rfl,lookup3496]
  decide
private def raw61 := PA215.Census.C035.records[61]'(by decide)
private theorem row61 : recordAgrees raw61 = true := by
  unfold recordAgrees
  rw [show raw61.siteIndex = 3497 from rfl,lookup3497]
  decide
private def raw62 := PA215.Census.C035.records[62]'(by decide)
private theorem row62 : recordAgrees raw62 = true := by
  unfold recordAgrees
  rw [show raw62.siteIndex = 3497 from rfl,lookup3497]
  decide
private def raw63 := PA215.Census.C035.records[63]'(by decide)
private theorem row63 : recordAgrees raw63 = true := by
  unfold recordAgrees
  rw [show raw63.siteIndex = 3498 from rfl,lookup3498]
  decide
private def raw64 := PA215.Census.C035.records[64]'(by decide)
private theorem row64 : recordAgrees raw64 = true := by
  unfold recordAgrees
  rw [show raw64.siteIndex = 3499 from rfl,lookup3499]
  decide
private def raw65 := PA215.Census.C035.records[65]'(by decide)
private theorem row65 : recordAgrees raw65 = true := by
  unfold recordAgrees
  rw [show raw65.siteIndex = 3500 from rfl,lookup3500]
  decide
private def raw66 := PA215.Census.C035.records[66]'(by decide)
private theorem row66 : recordAgrees raw66 = true := by
  unfold recordAgrees
  rw [show raw66.siteIndex = 3501 from rfl,lookup3501]
  decide
private def raw67 := PA215.Census.C035.records[67]'(by decide)
private theorem row67 : recordAgrees raw67 = true := by
  unfold recordAgrees
  rw [show raw67.siteIndex = 3501 from rfl,lookup3501]
  decide
private def raw68 := PA215.Census.C035.records[68]'(by decide)
private theorem row68 : recordAgrees raw68 = true := by
  unfold recordAgrees
  rw [show raw68.siteIndex = 3502 from rfl,lookup3502]
  decide
private def raw69 := PA215.Census.C035.records[69]'(by decide)
private theorem row69 : recordAgrees raw69 = true := by
  unfold recordAgrees
  rw [show raw69.siteIndex = 3503 from rfl,lookup3503]
  decide
private def raw70 := PA215.Census.C035.records[70]'(by decide)
private theorem row70 : recordAgrees raw70 = true := by
  unfold recordAgrees
  rw [show raw70.siteIndex = 3504 from rfl,lookup3504]
  decide
private def raw71 := PA215.Census.C035.records[71]'(by decide)
private theorem row71 : recordAgrees raw71 = true := by
  unfold recordAgrees
  rw [show raw71.siteIndex = 3504 from rfl,lookup3504]
  decide
private def raw72 := PA215.Census.C035.records[72]'(by decide)
private theorem row72 : recordAgrees raw72 = true := by
  unfold recordAgrees
  rw [show raw72.siteIndex = 3505 from rfl,lookup3505]
  decide
private def raw73 := PA215.Census.C035.records[73]'(by decide)
private theorem row73 : recordAgrees raw73 = true := by
  unfold recordAgrees
  rw [show raw73.siteIndex = 3506 from rfl,lookup3506]
  decide
private def raw74 := PA215.Census.C035.records[74]'(by decide)
private theorem row74 : recordAgrees raw74 = true := by
  unfold recordAgrees
  rw [show raw74.siteIndex = 3507 from rfl,lookup3507]
  decide
private def raw75 := PA215.Census.C035.records[75]'(by decide)
private theorem row75 : recordAgrees raw75 = true := by
  unfold recordAgrees
  rw [show raw75.siteIndex = 3508 from rfl,lookup3508]
  decide
private def raw76 := PA215.Census.C035.records[76]'(by decide)
private theorem row76 : recordAgrees raw76 = true := by
  unfold recordAgrees
  rw [show raw76.siteIndex = 3508 from rfl,lookup3508]
  decide
private def raw77 := PA215.Census.C035.records[77]'(by decide)
private theorem row77 : recordAgrees raw77 = true := by
  unfold recordAgrees
  rw [show raw77.siteIndex = 3509 from rfl,lookup3509]
  decide
private def raw78 := PA215.Census.C035.records[78]'(by decide)
private theorem row78 : recordAgrees raw78 = true := by
  unfold recordAgrees
  rw [show raw78.siteIndex = 3510 from rfl,lookup3510]
  decide
private def raw79 := PA215.Census.C035.records[79]'(by decide)
private theorem row79 : recordAgrees raw79 = true := by
  unfold recordAgrees
  rw [show raw79.siteIndex = 3511 from rfl,lookup3511]
  decide
private def raw80 := PA215.Census.C035.records[80]'(by decide)
private theorem row80 : recordAgrees raw80 = true := by
  unfold recordAgrees
  rw [show raw80.siteIndex = 3511 from rfl,lookup3511]
  decide
private def raw81 := PA215.Census.C035.records[81]'(by decide)
private theorem row81 : recordAgrees raw81 = true := by
  unfold recordAgrees
  rw [show raw81.siteIndex = 3512 from rfl,lookup3512]
  decide
private def raw82 := PA215.Census.C035.records[82]'(by decide)
private theorem row82 : recordAgrees raw82 = true := by
  unfold recordAgrees
  rw [show raw82.siteIndex = 3513 from rfl,lookup3513]
  decide
private def raw83 := PA215.Census.C035.records[83]'(by decide)
private theorem row83 : recordAgrees raw83 = true := by
  unfold recordAgrees
  rw [show raw83.siteIndex = 3514 from rfl,lookup3514]
  decide
private def raw84 := PA215.Census.C035.records[84]'(by decide)
private theorem row84 : recordAgrees raw84 = true := by
  unfold recordAgrees
  rw [show raw84.siteIndex = 3514 from rfl,lookup3514]
  decide
private def raw85 := PA215.Census.C035.records[85]'(by decide)
private theorem row85 : recordAgrees raw85 = true := by
  unfold recordAgrees
  rw [show raw85.siteIndex = 3515 from rfl,lookup3515]
  decide
private def raw86 := PA215.Census.C035.records[86]'(by decide)
private theorem row86 : recordAgrees raw86 = true := by
  unfold recordAgrees
  rw [show raw86.siteIndex = 3516 from rfl,lookup3516]
  decide
private def raw87 := PA215.Census.C035.records[87]'(by decide)
private theorem row87 : recordAgrees raw87 = true := by
  unfold recordAgrees
  rw [show raw87.siteIndex = 3517 from rfl,lookup3517]
  decide
private def raw88 := PA215.Census.C035.records[88]'(by decide)
private theorem row88 : recordAgrees raw88 = true := by
  unfold recordAgrees
  rw [show raw88.siteIndex = 3517 from rfl,lookup3517]
  decide
private def raw89 := PA215.Census.C035.records[89]'(by decide)
private theorem row89 : recordAgrees raw89 = true := by
  unfold recordAgrees
  rw [show raw89.siteIndex = 3518 from rfl,lookup3518]
  decide
private def raw90 := PA215.Census.C035.records[90]'(by decide)
private theorem row90 : recordAgrees raw90 = true := by
  unfold recordAgrees
  rw [show raw90.siteIndex = 3519 from rfl,lookup3519]
  decide
private def raw91 := PA215.Census.C035.records[91]'(by decide)
private theorem row91 : recordAgrees raw91 = true := by
  unfold recordAgrees
  rw [show raw91.siteIndex = 3520 from rfl,lookup3520]
  decide
private def raw92 := PA215.Census.C035.records[92]'(by decide)
private theorem row92 : recordAgrees raw92 = true := by
  unfold recordAgrees
  rw [show raw92.siteIndex = 3521 from rfl,lookup3521]
  decide
private def raw93 := PA215.Census.C035.records[93]'(by decide)
private theorem row93 : recordAgrees raw93 = true := by
  unfold recordAgrees
  rw [show raw93.siteIndex = 3521 from rfl,lookup3521]
  decide
private def raw94 := PA215.Census.C035.records[94]'(by decide)
private theorem row94 : recordAgrees raw94 = true := by
  unfold recordAgrees
  rw [show raw94.siteIndex = 3522 from rfl,lookup3522]
  decide
private def raw95 := PA215.Census.C035.records[95]'(by decide)
private theorem row95 : recordAgrees raw95 = true := by
  unfold recordAgrees
  rw [show raw95.siteIndex = 3523 from rfl,lookup3523]
  decide
private def raw96 := PA215.Census.C035.records[96]'(by decide)
private theorem row96 : recordAgrees raw96 = true := by
  unfold recordAgrees
  rw [show raw96.siteIndex = 3523 from rfl,lookup3523]
  decide
private def raw97 := PA215.Census.C035.records[97]'(by decide)
private theorem row97 : recordAgrees raw97 = true := by
  unfold recordAgrees
  rw [show raw97.siteIndex = 3524 from rfl,lookup3524]
  decide
private def raw98 := PA215.Census.C035.records[98]'(by decide)
private theorem row98 : recordAgrees raw98 = true := by
  unfold recordAgrees
  rw [show raw98.siteIndex = 3525 from rfl,lookup3525]
  decide
private def raw99 := PA215.Census.C035.records[99]'(by decide)
private theorem row99 : recordAgrees raw99 = true := by
  unfold recordAgrees
  rw [show raw99.siteIndex = 3526 from rfl,lookup3526]
  decide
private def raw100 := PA215.Census.C035.records[100]'(by decide)
private theorem row100 : recordAgrees raw100 = true := by
  unfold recordAgrees
  rw [show raw100.siteIndex = 3527 from rfl,lookup3527]
  decide
private def raw101 := PA215.Census.C035.records[101]'(by decide)
private theorem row101 : recordAgrees raw101 = true := by
  unfold recordAgrees
  rw [show raw101.siteIndex = 3527 from rfl,lookup3527]
  decide
private def raw102 := PA215.Census.C035.records[102]'(by decide)
private theorem row102 : recordAgrees raw102 = true := by
  unfold recordAgrees
  rw [show raw102.siteIndex = 3528 from rfl,lookup3528]
  decide
private def raw103 := PA215.Census.C035.records[103]'(by decide)
private theorem row103 : recordAgrees raw103 = true := by
  unfold recordAgrees
  rw [show raw103.siteIndex = 3529 from rfl,lookup3529]
  decide
private def raw104 := PA215.Census.C035.records[104]'(by decide)
private theorem row104 : recordAgrees raw104 = true := by
  unfold recordAgrees
  rw [show raw104.siteIndex = 3530 from rfl,lookup3530]
  decide
private def raw105 := PA215.Census.C035.records[105]'(by decide)
private theorem row105 : recordAgrees raw105 = true := by
  unfold recordAgrees
  rw [show raw105.siteIndex = 3530 from rfl,lookup3530]
  decide
private def raw106 := PA215.Census.C035.records[106]'(by decide)
private theorem row106 : recordAgrees raw106 = true := by
  unfold recordAgrees
  rw [show raw106.siteIndex = 3531 from rfl,lookup3531]
  decide
private def raw107 := PA215.Census.C035.records[107]'(by decide)
private theorem row107 : recordAgrees raw107 = true := by
  unfold recordAgrees
  rw [show raw107.siteIndex = 3532 from rfl,lookup3532]
  decide
private def raw108 := PA215.Census.C035.records[108]'(by decide)
private theorem row108 : recordAgrees raw108 = true := by
  unfold recordAgrees
  rw [show raw108.siteIndex = 3533 from rfl,lookup3533]
  decide
private def raw109 := PA215.Census.C035.records[109]'(by decide)
private theorem row109 : recordAgrees raw109 = true := by
  unfold recordAgrees
  rw [show raw109.siteIndex = 3534 from rfl,lookup3534]
  decide
private def raw110 := PA215.Census.C035.records[110]'(by decide)
private theorem row110 : recordAgrees raw110 = true := by
  unfold recordAgrees
  rw [show raw110.siteIndex = 3534 from rfl,lookup3534]
  decide
private def raw111 := PA215.Census.C035.records[111]'(by decide)
private theorem row111 : recordAgrees raw111 = true := by
  unfold recordAgrees
  rw [show raw111.siteIndex = 3535 from rfl,lookup3535]
  decide
private def raw112 := PA215.Census.C035.records[112]'(by decide)
private theorem row112 : recordAgrees raw112 = true := by
  unfold recordAgrees
  rw [show raw112.siteIndex = 3536 from rfl,lookup3536]
  decide
private def raw113 := PA215.Census.C035.records[113]'(by decide)
private theorem row113 : recordAgrees raw113 = true := by
  unfold recordAgrees
  rw [show raw113.siteIndex = 3537 from rfl,lookup3537]
  decide
private def raw114 := PA215.Census.C035.records[114]'(by decide)
private theorem row114 : recordAgrees raw114 = true := by
  unfold recordAgrees
  rw [show raw114.siteIndex = 3537 from rfl,lookup3537]
  decide
private def raw115 := PA215.Census.C035.records[115]'(by decide)
private theorem row115 : recordAgrees raw115 = true := by
  unfold recordAgrees
  rw [show raw115.siteIndex = 3538 from rfl,lookup3538]
  decide
private def raw116 := PA215.Census.C035.records[116]'(by decide)
private theorem row116 : recordAgrees raw116 = true := by
  unfold recordAgrees
  rw [show raw116.siteIndex = 3539 from rfl,lookup3539]
  decide
private def raw117 := PA215.Census.C035.records[117]'(by decide)
private theorem row117 : recordAgrees raw117 = true := by
  unfold recordAgrees
  rw [show raw117.siteIndex = 3539 from rfl,lookup3539]
  decide
private def raw118 := PA215.Census.C035.records[118]'(by decide)
private theorem row118 : recordAgrees raw118 = true := by
  unfold recordAgrees
  rw [show raw118.siteIndex = 3540 from rfl,lookup3540]
  decide
private def raw119 := PA215.Census.C035.records[119]'(by decide)
private theorem row119 : recordAgrees raw119 = true := by
  unfold recordAgrees
  rw [show raw119.siteIndex = 3541 from rfl,lookup3541]
  decide
private def raw120 := PA215.Census.C035.records[120]'(by decide)
private theorem row120 : recordAgrees raw120 = true := by
  unfold recordAgrees
  rw [show raw120.siteIndex = 3541 from rfl,lookup3541]
  decide
private def raw121 := PA215.Census.C035.records[121]'(by decide)
private theorem row121 : recordAgrees raw121 = true := by
  unfold recordAgrees
  rw [show raw121.siteIndex = 3542 from rfl,lookup3542]
  decide
private def raw122 := PA215.Census.C035.records[122]'(by decide)
private theorem row122 : recordAgrees raw122 = true := by
  unfold recordAgrees
  rw [show raw122.siteIndex = 3543 from rfl,lookup3543]
  decide
private def raw123 := PA215.Census.C035.records[123]'(by decide)
private theorem row123 : recordAgrees raw123 = true := by
  unfold recordAgrees
  rw [show raw123.siteIndex = 3544 from rfl,lookup3544]
  decide
private def raw124 := PA215.Census.C035.records[124]'(by decide)
private theorem row124 : recordAgrees raw124 = true := by
  unfold recordAgrees
  rw [show raw124.siteIndex = 3545 from rfl,lookup3545]
  decide
private def raw125 := PA215.Census.C035.records[125]'(by decide)
private theorem row125 : recordAgrees raw125 = true := by
  unfold recordAgrees
  rw [show raw125.siteIndex = 3545 from rfl,lookup3545]
  decide
private def raw126 := PA215.Census.C035.records[126]'(by decide)
private theorem row126 : recordAgrees raw126 = true := by
  unfold recordAgrees
  rw [show raw126.siteIndex = 3546 from rfl,lookup3546]
  decide
private def raw127 := PA215.Census.C035.records[127]'(by decide)
private theorem row127 : recordAgrees raw127 = true := by
  unfold recordAgrees
  rw [show raw127.siteIndex = 3547 from rfl,lookup3547]
  decide
private theorem enumeration : PA215.Census.C035.records.toList = [raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7,raw8,raw9,raw10,raw11,raw12,raw13,raw14,raw15,raw16,raw17,raw18,raw19,raw20,raw21,raw22,raw23,raw24,raw25,raw26,raw27,raw28,raw29,raw30,raw31,raw32,raw33,raw34,raw35,raw36,raw37,raw38,raw39,raw40,raw41,raw42,raw43,raw44,raw45,raw46,raw47,raw48,raw49,raw50,raw51,raw52,raw53,raw54,raw55,raw56,raw57,raw58,raw59,raw60,raw61,raw62,raw63,raw64,raw65,raw66,raw67,raw68,raw69,raw70,raw71,raw72,raw73,raw74,raw75,raw76,raw77,raw78,raw79,raw80,raw81,raw82,raw83,raw84,raw85,raw86,raw87,raw88,raw89,raw90,raw91,raw92,raw93,raw94,raw95,raw96,raw97,raw98,raw99,raw100,raw101,raw102,raw103,raw104,raw105,raw106,raw107,raw108,raw109,raw110,raw111,raw112,raw113,raw114,raw115,raw116,raw117,raw118,raw119,raw120,raw121,raw122,raw123,raw124,raw125,raw126,raw127] := by rfl
theorem checked : PA215.Census.C035.records.toList.all recordAgrees = true := by
  rw [enumeration]
  simp only [List.all_cons,List.all_nil,row0,row1,row2,row3,row4,row5,row6,row7,row8,row9,row10,row11,row12,row13,row14,row15,row16,row17,row18,row19,row20,row21,row22,row23,row24,row25,row26,row27,row28,row29,row30,row31,row32,row33,row34,row35,row36,row37,row38,row39,row40,row41,row42,row43,row44,row45,row46,row47,row48,row49,row50,row51,row52,row53,row54,row55,row56,row57,row58,row59,row60,row61,row62,row63,row64,row65,row66,row67,row68,row69,row70,row71,row72,row73,row74,row75,row76,row77,row78,row79,row80,row81,row82,row83,row84,row85,row86,row87,row88,row89,row90,row91,row92,row93,row94,row95,row96,row97,row98,row99,row100,row101,row102,row103,row104,row105,row106,row107,row108,row109,row110,row111,row112,row113,row114,row115,row116,row117,row118,row119,row120,row121,row122,row123,row124,row125,row126,row127,Bool.and_self]
#print axioms checked
end PA215.Source.CensusJoin.J035
