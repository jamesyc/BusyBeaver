module

public import User211SourceEquivalence
public import PA211.UserCandidate.PrimitiveSimulation
public import PA211.UserCandidate.RuntimeShards.S067
public import PA211.UserCandidate.RuntimeShards.S068

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 32000000
namespace PA211.UserCandidate.CoverageShards.S052
open PA215.Source PA211.UserCandidate.PrimitiveSimulation
def e3328 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,false,true], .inc 1⟩, .inc 1 (some 3329), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,false,true] 1 (some 3329) 0 349 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S067.s3328_plain_checked⟩

def e3329 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,false,false], .dec 2⟩, .dec 2 (some 3337) (some 3330), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,false,false] 2 (some 3337) (some 3330) 0 1 366 372 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S067.s3329_zero_checked PA211.UserCandidate.RuntimeShards.S067.s3329_positive_checked⟩

def e3330 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,false,true,false], .inc 7⟩, .inc 7 (some 3331), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,false,true,false] 7 (some 3331) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S067.s3330_plain_checked⟩

def e3331 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,false,true,true,false,false,false], .dec 6⟩, .dec 6 (some 3333) (some 3332), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,false,true,true,false,false,false] 6 (some 3333) (some 3332) 0 1 408 414 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S067.s3331_zero_checked PA211.UserCandidate.RuntimeShards.S067.s3331_positive_checked⟩

def e3332 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,false,true,true,false,false,true], .breakTo 1⟩, .jump (some 3336), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,false,true,true,false,false,true] (some 3336) 0 113 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S067.s3332_plain_checked⟩

def e3333 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,false,true,true,false,true,false], .dec 7⟩, .dec 7 (some 3336) (some 3334), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,false,true,true,false,true,false] 7 (some 3336) (some 3334) 0 1 420 423 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S067.s3333_zero_checked PA211.UserCandidate.RuntimeShards.S067.s3333_positive_checked⟩

def e3334 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,false,true,true,false,true,true,false], .inc 6⟩, .inc 6 (some 3335), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,false,true,true,false,true,true,false] 6 (some 3335) 0 427 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S067.s3334_plain_checked⟩

def e3335 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 3333), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,false,true,true,false,true,true,true] (some 3333) 0 116 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S067.s3335_plain_checked⟩

def e3336 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,false,true,true,true], .continueTo 3⟩, .jump (some 3329), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,false,true,true,true] (some 3329) 0 107 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S067.s3336_plain_checked⟩

def e3337 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,true,false], .dec 7⟩, .dec 7 (some 3340) (some 3338), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,true,false] 7 (some 3340) (some 3338) 0 1 366 369 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S067.s3337_zero_checked PA211.UserCandidate.RuntimeShards.S067.s3337_positive_checked⟩

def e3338 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,true,true,false], .inc 2⟩, .inc 2 (some 3339), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,true,true,false] 2 (some 3339) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S067.s3338_plain_checked⟩

def e3339 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 3337), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,true,true,true] (some 3337) 0 101 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S067.s3339_plain_checked⟩

def e3340 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,false,false,false], .dec 1⟩, .dec 1 (some 3344) (some 3341), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,false,false,false] 1 (some 3344) (some 3341) 0 1 363 369 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S067.s3340_zero_checked PA211.UserCandidate.RuntimeShards.S067.s3340_positive_checked⟩

def e3341 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,false,false,true,false], .inc 7⟩, .inc 7 (some 3342), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,false,false,true,false] 7 (some 3342) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S067.s3341_plain_checked⟩

def e3342 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,false,false,true,true,false], .inc 6⟩, .inc 6 (some 3343), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,false,false,true,true,false] 6 (some 3343) 0 409 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S067.s3342_plain_checked⟩

def e3343 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,false,false,true,true,true], .continueTo 3⟩, .jump (some 3340), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,false,false,true,true,true] (some 3340) 0 110 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S067.s3343_plain_checked⟩

def e3344 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,false,true,false], .dec 6⟩, .dec 6 (some 3350) (some 3345), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,false,true,false] 6 (some 3350) (some 3345) 0 1 384 387 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S067.s3344_zero_checked PA211.UserCandidate.RuntimeShards.S067.s3344_positive_checked⟩

def e3345 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,false,true,true,false,false], .inc 7⟩, .inc 7 (some 3346), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,false,true,true,false,false] 7 (some 3346) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S067.s3345_plain_checked⟩

def e3346 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 3349) (some 3347), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,false,true,true,false,true,false] 6 (some 3349) (some 3347) 0 1 402 405 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S067.s3346_zero_checked PA211.UserCandidate.RuntimeShards.S067.s3346_positive_checked⟩

def e3347 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,false,true,true,false,true,true,false], .inc 1⟩, .inc 1 (some 3348), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,false,true,true,false,true,true,false] 1 (some 3348) 0 400 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S067.s3347_plain_checked⟩

def e3348 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 3346), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,false,true,true,false,true,true,true] (some 3346) 0 110 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S067.s3348_plain_checked⟩

def e3349 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,false,true,true,true], .continueTo 3⟩, .jump (some 3340), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,false,true,true,true] (some 3340) 0 113 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S067.s3349_plain_checked⟩

def e3350 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,true,false], .dec 7⟩, .dec 7 (some 3356) (some 3351), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,true,false] 7 (some 3356) (some 3351) 0 1 375 369 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S067.s3350_zero_checked PA211.UserCandidate.RuntimeShards.S068.s3350_positive_checked⟩

def e3351 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,true,true,false,false,false], .inc 1⟩, .inc 1 (some 3352), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,true,true,false,false,false] 1 (some 3352) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3351_plain_checked⟩

def e3352 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,true,true,false,false,true], .inc 1⟩, .inc 1 (some 3353), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,true,true,false,false,true] 1 (some 3353) 0 385 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3352_plain_checked⟩

def e3353 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,true,true,false,true,false], .inc 1⟩, .inc 1 (some 3354), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,true,true,false,true,false] 1 (some 3354) 0 391 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3353_plain_checked⟩

def e3354 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,true,true,false,true,true], .inc 1⟩, .inc 1 (some 3355), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,true,true,false,true,true] 1 (some 3355) 0 397 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3354_plain_checked⟩

def e3355 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,true,true,true], .continueTo 2⟩, .jump (some 3350), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,true,true,true] (some 3350) 0 98 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3355_plain_checked⟩

def e3356 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,false,false,false], .dec 2⟩, .dec 2 (some 3364) (some 3357), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,false,false,false] 2 (some 3364) (some 3357) 0 1 357 363 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3356_zero_checked PA211.UserCandidate.RuntimeShards.S068.s3356_positive_checked⟩

def e3357 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,false,false,true,false], .inc 7⟩, .inc 7 (some 3358), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,false,false,true,false] 7 (some 3358) 0 373 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3357_plain_checked⟩

def e3358 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,false,false,true,true,false,false,false], .dec 6⟩, .dec 6 (some 3360) (some 3359), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,false,false,true,true,false,false,false] 6 (some 3360) (some 3359) 0 1 399 405 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3358_zero_checked PA211.UserCandidate.RuntimeShards.S068.s3358_positive_checked⟩

def e3359 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,false,false,true,true,false,false,true], .breakTo 1⟩, .jump (some 3363), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,false,false,true,true,false,false,true] (some 3363) 0 110 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3359_plain_checked⟩

def e3360 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,false,false,true,true,false,true,false], .dec 7⟩, .dec 7 (some 3363) (some 3361), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,false,false,true,true,false,true,false] 7 (some 3363) (some 3361) 0 1 411 414 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3360_zero_checked PA211.UserCandidate.RuntimeShards.S068.s3360_positive_checked⟩

def e3361 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,false,false,true,true,false,true,true,false], .inc 6⟩, .inc 6 (some 3362), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,false,false,true,true,false,true,true,false] 6 (some 3362) 0 418 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3361_plain_checked⟩

def e3362 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,false,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 3360), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,false,false,true,true,false,true,true,true] (some 3360) 0 113 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3362_plain_checked⟩

def e3363 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,false,false,true,true,true], .continueTo 3⟩, .jump (some 3356), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,false,false,true,true,true] (some 3356) 0 104 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3363_plain_checked⟩

def e3364 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,false,true,false], .dec 7⟩, .dec 7 (some 3367) (some 3365), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,false,true,false] 7 (some 3367) (some 3365) 0 1 357 360 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3364_zero_checked PA211.UserCandidate.RuntimeShards.S068.s3364_positive_checked⟩

def e3365 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,false,true,true,false], .inc 2⟩, .inc 2 (some 3366), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,false,true,true,false] 2 (some 3366) 0 373 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3365_plain_checked⟩

def e3366 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,false,true,true,true], .continueTo 2⟩, .jump (some 3364), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,false,true,true,true] (some 3364) 0 98 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3366_plain_checked⟩

def e3367 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,false,false,false], .dec 1⟩, .dec 1 (some 3371) (some 3368), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,false,false,false] 1 (some 3371) (some 3368) 0 1 354 360 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3367_zero_checked PA211.UserCandidate.RuntimeShards.S068.s3367_positive_checked⟩

def e3368 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,false,false,true,false], .inc 7⟩, .inc 7 (some 3369), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,false,false,true,false] 7 (some 3369) 0 373 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3368_plain_checked⟩

def e3369 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,false,false,true,true,false], .inc 6⟩, .inc 6 (some 3370), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,false,false,true,true,false] 6 (some 3370) 0 400 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3369_plain_checked⟩

def e3370 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,false,false,true,true,true], .continueTo 3⟩, .jump (some 3367), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,false,false,true,true,true] (some 3367) 0 107 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3370_plain_checked⟩

def e3371 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,false,true,false], .dec 6⟩, .dec 6 (some 3377) (some 3372), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,false,true,false] 6 (some 3377) (some 3372) 0 1 375 378 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3371_zero_checked PA211.UserCandidate.RuntimeShards.S068.s3371_positive_checked⟩

def e3372 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,false,true,true,false,false], .inc 7⟩, .inc 7 (some 3373), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,false,true,true,false,false] 7 (some 3373) 0 373 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3372_plain_checked⟩

def e3373 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 3376) (some 3374), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,false,true,true,false,true,false] 6 (some 3376) (some 3374) 0 1 393 396 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3373_zero_checked PA211.UserCandidate.RuntimeShards.S068.s3373_positive_checked⟩

def e3374 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,false,true,true,false,true,true,false], .inc 1⟩, .inc 1 (some 3375), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,false,true,true,false,true,true,false] 1 (some 3375) 0 391 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3374_plain_checked⟩

def e3375 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 3373), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,false,true,true,false,true,true,true] (some 3373) 0 107 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3375_plain_checked⟩

def e3376 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,false,true,true,true], .continueTo 3⟩, .jump (some 3367), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,false,true,true,true] (some 3367) 0 110 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3376_plain_checked⟩

def e3377 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,true,false], .dec 7⟩, .dec 7 (some 3383) (some 3378), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,true,false] 7 (some 3383) (some 3378) 0 1 360 360 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3377_zero_checked PA211.UserCandidate.RuntimeShards.S068.s3377_positive_checked⟩

def e3378 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,true,true,false,false,false], .inc 1⟩, .inc 1 (some 3379), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,true,true,false,false,false] 1 (some 3379) 0 373 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3378_plain_checked⟩

def e3379 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,true,true,false,false,true], .inc 1⟩, .inc 1 (some 3380), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,true,true,false,false,true] 1 (some 3380) 0 376 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3379_plain_checked⟩

def e3380 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,true,true,false,true,false], .inc 1⟩, .inc 1 (some 3381), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,true,true,false,true,false] 1 (some 3381) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3380_plain_checked⟩

def e3381 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,true,true,false,true,true], .inc 1⟩, .inc 1 (some 3382), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,true,true,false,true,true] 1 (some 3382) 0 388 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3381_plain_checked⟩

def e3382 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,true,true,true], .continueTo 2⟩, .jump (some 3377), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,false,true,true,true,true] (some 3377) 0 95 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3382_plain_checked⟩

def e3383 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,true,false,false,false,false], .dec 1⟩, .dec 1 (some 3386) (some 3384), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,true,false,false,false,false] 1 (some 3386) (some 3384) 0 1 363 369 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3383_zero_checked PA211.UserCandidate.RuntimeShards.S068.s3383_positive_checked⟩

def e3384 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,true,false,false,false,true,false], .inc 6⟩, .inc 6 (some 3385), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,true,false,false,false,true,false] 6 (some 3385) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3384_plain_checked⟩

def e3385 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,true,false,false,false,true,true], .continueTo 2⟩, .jump (some 3383), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,true,false,false,false,true,true] (some 3383) 0 101 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3385_plain_checked⟩

def e3386 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,true,false,false,true,false,false], .dec 2⟩, .dec 2 (some 3389) (some 3387), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,true,false,false,true,false,false] 2 (some 3389) (some 3387) 0 1 384 390 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3386_zero_checked PA211.UserCandidate.RuntimeShards.S068.s3386_positive_checked⟩

def e3387 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,true,false,false,true,false,true,false], .inc 1⟩, .inc 1 (some 3388), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,true,false,false,true,false,true,false] 1 (some 3388) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3387_plain_checked⟩

def e3388 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,true,false,false,true,false,true,true], .continueTo 2⟩, .jump (some 3386), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,true,false,false,true,false,true,true] (some 3386) 0 104 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3388_plain_checked⟩

def e3389 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,true,false,false,true,true,false,false,false], .dec 1⟩, .dec 1 (some 3393) (some 3390), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,true,false,false,true,true,false,false,false] 1 (some 3393) (some 3390) 0 1 390 396 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3389_zero_checked PA211.UserCandidate.RuntimeShards.S068.s3389_positive_checked⟩

def e3390 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,true,false,false,true,true,false,false,true,false], .inc 7⟩, .inc 7 (some 3391), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,true,false,false,true,true,false,false,true,false] 7 (some 3391) 0 409 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3390_plain_checked⟩

def e3391 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,true,false,false,true,true,false,false,true,true,false], .inc 6⟩, .inc 6 (some 3392), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true,true,true,false,false,true,true,false,false,true,true,false] 6 (some 3392) 0 436 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S068.s3391_plain_checked⟩

def entries : Array (Entry PA211.UserCandidate.Source.path 3947) := #[
  e3328,
  e3329,
  e3330,
  e3331,
  e3332,
  e3333,
  e3334,
  e3335,
  e3336,
  e3337,
  e3338,
  e3339,
  e3340,
  e3341,
  e3342,
  e3343,
  e3344,
  e3345,
  e3346,
  e3347,
  e3348,
  e3349,
  e3350,
  e3351,
  e3352,
  e3353,
  e3354,
  e3355,
  e3356,
  e3357,
  e3358,
  e3359,
  e3360,
  e3361,
  e3362,
  e3363,
  e3364,
  e3365,
  e3366,
  e3367,
  e3368,
  e3369,
  e3370,
  e3371,
  e3372,
  e3373,
  e3374,
  e3375,
  e3376,
  e3377,
  e3378,
  e3379,
  e3380,
  e3381,
  e3382,
  e3383,
  e3384,
  e3385,
  e3386,
  e3387,
  e3388,
  e3389,
  e3390,
  e3391
]
theorem sites_block : entries.toList.map (·.site) =
 (PA211.UserCandidate.Source.sites.toList.drop 3328).take 64 := by decide +kernel
theorem codes_block : entries.toList.map (·.code) =
 (PA213.SourceProgram.codes.toList.drop 3328).take 64 := by decide +kernel
end PA211.UserCandidate.CoverageShards.S052
