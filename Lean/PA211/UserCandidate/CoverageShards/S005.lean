module

public import User211SourceEquivalence
public import PA211.UserCandidate.PrimitiveSimulation
public import PA211.UserCandidate.RuntimeShards.S006
public import PA211.UserCandidate.RuntimeShards.S007

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 32000000
namespace PA211.UserCandidate.CoverageShards.S005
open PA215.Source PA211.UserCandidate.PrimitiveSimulation
def e0320 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,false,false,false,true,true,false,false,false], .dec 6⟩, .dec 6 (some 322) (some 321), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,false,false,false,true,true,false,false,false] 6 (some 322) (some 321) 0 1 363 369 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S006.s0320_zero_checked PA211.UserCandidate.RuntimeShards.S006.s0320_positive_checked⟩

def e0321 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,false,false,false,true,true,false,false,true], .breakTo 1⟩, .jump (some 325), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,false,false,false,true,true,false,false,true] (some 325) 0 98 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S006.s0321_plain_checked⟩

def e0322 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,false,false,false,true,true,false,true,false], .dec 7⟩, .dec 7 (some 325) (some 323), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,false,false,false,true,true,false,true,false] 7 (some 325) (some 323) 0 1 375 378 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S006.s0322_zero_checked PA211.UserCandidate.RuntimeShards.S006.s0322_positive_checked⟩

def e0323 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,false,false,false,true,true,false,true,true,false], .inc 6⟩, .inc 6 (some 324), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,false,false,false,true,true,false,true,true,false] 6 (some 324) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S006.s0323_plain_checked⟩

def e0324 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,false,false,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 322), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,false,false,false,true,true,false,true,true,true] (some 322) 0 101 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S006.s0324_plain_checked⟩

def e0325 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,false,false,false,true,true,true], .continueTo 3⟩, .jump (some 318), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,false,false,false,true,true,true] (some 318) 0 92 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S006.s0325_plain_checked⟩

def e0326 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,false,false,true,false], .dec 7⟩, .dec 7 (some 329) (some 327), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,false,false,true,false] 7 (some 329) (some 327) 0 1 321 324 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S006.s0326_zero_checked PA211.UserCandidate.RuntimeShards.S006.s0326_positive_checked⟩

def e0327 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,false,false,true,true,false], .inc 2⟩, .inc 2 (some 328), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,false,false,true,true,false] 2 (some 328) 0 337 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S006.s0327_plain_checked⟩

def e0328 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,false,false,true,true,true], .continueTo 2⟩, .jump (some 326), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,false,false,true,true,true] (some 326) 0 86 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S006.s0328_plain_checked⟩

def e0329 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,false,true,false,false,false], .dec 1⟩, .dec 1 (some 333) (some 330), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,false,true,false,false,false] 1 (some 333) (some 330) 0 1 318 324 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S006.s0329_zero_checked PA211.UserCandidate.RuntimeShards.S006.s0329_positive_checked⟩

def e0330 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,false,true,false,false,true,false], .inc 7⟩, .inc 7 (some 331), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,false,true,false,false,true,false] 7 (some 331) 0 337 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S006.s0330_plain_checked⟩

def e0331 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,false,true,false,false,true,true,false], .inc 6⟩, .inc 6 (some 332), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,false,true,false,false,true,true,false] 6 (some 332) 0 364 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S006.s0331_plain_checked⟩

def e0332 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,false,true,false,false,true,true,true], .continueTo 3⟩, .jump (some 329), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,false,true,false,false,true,true,true] (some 329) 0 95 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S006.s0332_plain_checked⟩

def e0333 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,false,true,false,true,false], .dec 6⟩, .dec 6 (some 339) (some 334), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,false,true,false,true,false] 6 (some 339) (some 334) 0 1 339 342 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S006.s0333_zero_checked PA211.UserCandidate.RuntimeShards.S006.s0333_positive_checked⟩

def e0334 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,false,true,false,true,true,false,false], .inc 7⟩, .inc 7 (some 335), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,false,true,false,true,true,false,false] 7 (some 335) 0 337 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S006.s0334_plain_checked⟩

def e0335 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,false,true,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 338) (some 336), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,false,true,false,true,true,false,true,false] 6 (some 338) (some 336) 0 1 357 360 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S006.s0335_zero_checked PA211.UserCandidate.RuntimeShards.S006.s0335_positive_checked⟩

def e0336 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,false,true,false,true,true,false,true,true,false], .inc 1⟩, .inc 1 (some 337), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,false,true,false,true,true,false,true,true,false] 1 (some 337) 0 355 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S006.s0336_plain_checked⟩

def e0337 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,false,true,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 335), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,false,true,false,true,true,false,true,true,true] (some 335) 0 95 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S006.s0337_plain_checked⟩

def e0338 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,false,true,false,true,true,true], .continueTo 3⟩, .jump (some 329), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,false,true,false,true,true,true] (some 329) 0 98 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S006.s0338_plain_checked⟩

def e0339 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,false,true,true,false], .dec 7⟩, .dec 7 (some 345) (some 340), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,false,true,true,false] 7 (some 345) (some 340) 0 1 324 324 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S006.s0339_zero_checked PA211.UserCandidate.RuntimeShards.S006.s0339_positive_checked⟩

def e0340 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,false,true,true,true,false,false,false], .inc 1⟩, .inc 1 (some 341), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,false,true,true,true,false,false,false] 1 (some 341) 0 337 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0340_plain_checked⟩

def e0341 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,false,true,true,true,false,false,true], .inc 1⟩, .inc 1 (some 342), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,false,true,true,true,false,false,true] 1 (some 342) 0 340 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0341_plain_checked⟩

def e0342 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,false,true,true,true,false,true,false], .inc 1⟩, .inc 1 (some 343), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,false,true,true,true,false,true,false] 1 (some 343) 0 346 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0342_plain_checked⟩

def e0343 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,false,true,true,true,false,true,true], .inc 1⟩, .inc 1 (some 344), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,false,true,true,true,false,true,true] 1 (some 344) 0 352 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0343_plain_checked⟩

def e0344 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,false,true,true,true,true], .continueTo 2⟩, .jump (some 339), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,false,true,true,true,true] (some 339) 0 83 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0344_plain_checked⟩

def e0345 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,false,false], .dec 1⟩, .dec 1 (some 348) (some 346), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,false,false] 1 (some 348) (some 346) 0 1 309 315 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0345_zero_checked PA211.UserCandidate.RuntimeShards.S007.s0345_positive_checked⟩

def e0346 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,false,true,false], .inc 6⟩, .inc 6 (some 347), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,false,true,false] 6 (some 347) 0 328 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0346_plain_checked⟩

def e0347 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,false,true,true], .continueTo 2⟩, .jump (some 345), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,false,true,true] (some 345) 0 83 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0347_plain_checked⟩

def e0348 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,false,false], .dec 2⟩, .dec 2 (some 351) (some 349), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,false,false] 2 (some 351) (some 349) 0 1 330 336 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0348_zero_checked PA211.UserCandidate.RuntimeShards.S007.s0348_positive_checked⟩

def e0349 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,false,true,false], .inc 1⟩, .inc 1 (some 350), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,false,true,false] 1 (some 350) 0 328 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0349_plain_checked⟩

def e0350 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,false,true,true], .continueTo 2⟩, .jump (some 348), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,false,true,true] (some 348) 0 86 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0350_plain_checked⟩

def e0351 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,true,false,false,false], .dec 1⟩, .dec 1 (some 355) (some 352), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,true,false,false,false] 1 (some 355) (some 352) 0 1 336 342 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0351_zero_checked PA211.UserCandidate.RuntimeShards.S007.s0351_positive_checked⟩

def e0352 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,true,false,false,true,false], .inc 7⟩, .inc 7 (some 353), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,true,false,false,true,false] 7 (some 353) 0 355 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0352_plain_checked⟩

def e0353 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,true,false,false,true,true,false], .inc 6⟩, .inc 6 (some 354), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,true,false,false,true,true,false] 6 (some 354) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0353_plain_checked⟩

def e0354 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,true,false,false,true,true,true], .continueTo 3⟩, .jump (some 351), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,true,false,false,true,true,true] (some 351) 0 101 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0354_plain_checked⟩

def e0355 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 361) (some 356), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,true,false,true,false] 6 (some 361) (some 356) 0 1 357 360 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0355_zero_checked PA211.UserCandidate.RuntimeShards.S007.s0355_positive_checked⟩

def e0356 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,true,false,true,true,false,false], .inc 7⟩, .inc 7 (some 357), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,true,false,true,true,false,false] 7 (some 357) 0 355 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0356_plain_checked⟩

def e0357 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,true,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 360) (some 358), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,true,false,true,true,false,true,false] 6 (some 360) (some 358) 0 1 375 378 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0357_zero_checked PA211.UserCandidate.RuntimeShards.S007.s0357_positive_checked⟩

def e0358 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,true,false,true,true,false,true,true,false], .inc 1⟩, .inc 1 (some 359), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,true,false,true,true,false,true,true,false] 1 (some 359) 0 373 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0358_plain_checked⟩

def e0359 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,true,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 357), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,true,false,true,true,false,true,true,true] (some 357) 0 101 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0359_plain_checked⟩

def e0360 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,true,false,true,true,true], .continueTo 3⟩, .jump (some 351), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,true,false,true,true,true] (some 351) 0 104 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0360_plain_checked⟩

def e0361 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,true,true,false], .dec 7⟩, .dec 7 (some 364) (some 362), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,true,true,false] 7 (some 364) (some 362) 0 1 345 342 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0361_zero_checked PA211.UserCandidate.RuntimeShards.S007.s0361_positive_checked⟩

def e0362 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,true,true,true,false], .inc 2⟩, .inc 2 (some 363), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,true,true,true,false] 2 (some 363) 0 355 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0362_plain_checked⟩

def e0363 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,true,true,true,true], .continueTo 2⟩, .jump (some 361), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,false,false,true,true,true,true,true] (some 361) 0 92 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0363_plain_checked⟩

def e0364 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,false,true,false,false], .dec 5⟩, .dec 5 (some 368) (some 365), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,false,true,false,false] 5 (some 368) (some 365) 0 1 309 315 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0364_zero_checked PA211.UserCandidate.RuntimeShards.S007.s0364_positive_checked⟩

def e0365 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,false,true,false,true,false], .inc 1⟩, .inc 1 (some 366), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,false,true,false,true,false] 1 (some 366) 0 319 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0365_plain_checked⟩

def e0366 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,false,true,false,true,true,false], .inc 6⟩, .inc 6 (some 367), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,false,true,false,true,true,false] 6 (some 367) 0 346 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0366_plain_checked⟩

def e0367 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,false,true,false,true,true,true], .continueTo 3⟩, .jump (some 364), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,false,true,false,true,true,true] (some 364) 0 89 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0367_plain_checked⟩

def e0368 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,false,true,true,false], .dec 6⟩, .dec 6 (some 371) (some 369), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,false,true,true,false] 6 (some 371) (some 369) 0 1 315 315 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0368_zero_checked PA211.UserCandidate.RuntimeShards.S007.s0368_positive_checked⟩

def e0369 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,false,true,true,true,false], .inc 5⟩, .inc 5 (some 370), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,false,true,true,true,false] 5 (some 370) 0 346 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0369_plain_checked⟩

def e0370 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,false,true,true,true,true], .continueTo 2⟩, .jump (some 368), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,false,true,true,true,true] (some 368) 0 83 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0370_plain_checked⟩

def e0371 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,true,false,false,false], .dec 1⟩, .dec 1 (some 374) (some 372), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,true,false,false,false] 1 (some 374) (some 372) 0 1 309 315 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0371_zero_checked PA211.UserCandidate.RuntimeShards.S007.s0371_positive_checked⟩

def e0372 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,true,false,false,true,false], .inc 6⟩, .inc 6 (some 373), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,true,false,false,true,false] 6 (some 373) 0 328 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0372_plain_checked⟩

def e0373 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,true,false,false,true,true], .continueTo 2⟩, .jump (some 371), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,true,false,false,true,true] (some 371) 0 83 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0373_plain_checked⟩

def e0374 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,true,false,true,false,false], .dec 2⟩, .dec 2 (some 377) (some 375), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,true,false,true,false,false] 2 (some 377) (some 375) 0 1 330 336 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0374_zero_checked PA211.UserCandidate.RuntimeShards.S007.s0374_positive_checked⟩

def e0375 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,true,false,true,false,true,false], .inc 1⟩, .inc 1 (some 376), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,true,false,true,false,true,false] 1 (some 376) 0 328 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0375_plain_checked⟩

def e0376 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,true,false,true,false,true,true], .continueTo 2⟩, .jump (some 374), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,true,false,true,false,true,true] (some 374) 0 86 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0376_plain_checked⟩

def e0377 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,true,false,true,true,false,false,false], .dec 1⟩, .dec 1 (some 381) (some 378), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,true,false,true,true,false,false,false] 1 (some 381) (some 378) 0 1 336 342 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0377_zero_checked PA211.UserCandidate.RuntimeShards.S007.s0377_positive_checked⟩

def e0378 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,true,false,true,true,false,false,true,false], .inc 7⟩, .inc 7 (some 379), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,true,false,true,true,false,false,true,false] 7 (some 379) 0 355 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0378_plain_checked⟩

def e0379 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,true,false,true,true,false,false,true,true,false], .inc 6⟩, .inc 6 (some 380), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,true,false,true,true,false,false,true,true,false] 6 (some 380) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0379_plain_checked⟩

def e0380 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,true,false,true,true,false,false,true,true,true], .continueTo 3⟩, .jump (some 377), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,true,false,true,true,false,false,true,true,true] (some 377) 0 101 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0380_plain_checked⟩

def e0381 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,true,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 387) (some 382), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,true,false,true,true,false,true,false] 6 (some 387) (some 382) 0 1 357 360 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0381_zero_checked PA211.UserCandidate.RuntimeShards.S007.s0381_positive_checked⟩

def e0382 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,true,false,true,true,false,true,true,false,false], .inc 7⟩, .inc 7 (some 383), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,true,false,true,true,false,true,true,false,false] 7 (some 383) 0 355 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0382_plain_checked⟩

def e0383 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,false,true,true,true,false,true,true,false,true,true,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 386) (some 384), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,false,true,true,true,false,true,true,false,true,true,false,true,true,false,true,false] 6 (some 386) (some 384) 0 1 375 378 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S007.s0383_zero_checked PA211.UserCandidate.RuntimeShards.S007.s0383_positive_checked⟩

def entries : Array (Entry PA211.UserCandidate.Source.path 3947) := #[
  e0320,
  e0321,
  e0322,
  e0323,
  e0324,
  e0325,
  e0326,
  e0327,
  e0328,
  e0329,
  e0330,
  e0331,
  e0332,
  e0333,
  e0334,
  e0335,
  e0336,
  e0337,
  e0338,
  e0339,
  e0340,
  e0341,
  e0342,
  e0343,
  e0344,
  e0345,
  e0346,
  e0347,
  e0348,
  e0349,
  e0350,
  e0351,
  e0352,
  e0353,
  e0354,
  e0355,
  e0356,
  e0357,
  e0358,
  e0359,
  e0360,
  e0361,
  e0362,
  e0363,
  e0364,
  e0365,
  e0366,
  e0367,
  e0368,
  e0369,
  e0370,
  e0371,
  e0372,
  e0373,
  e0374,
  e0375,
  e0376,
  e0377,
  e0378,
  e0379,
  e0380,
  e0381,
  e0382,
  e0383
]
theorem sites_block : entries.toList.map (·.site) =
 (PA211.UserCandidate.Source.sites.toList.drop 320).take 64 := by decide +kernel
theorem codes_block : entries.toList.map (·.code) =
 (PA213.SourceProgram.codes.toList.drop 320).take 64 := by decide +kernel
end PA211.UserCandidate.CoverageShards.S005
