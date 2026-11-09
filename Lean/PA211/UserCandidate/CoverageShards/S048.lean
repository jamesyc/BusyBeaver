import User211SourceEquivalence
import PA211.UserCandidate.PrimitiveSimulation
import PA211.UserCandidate.RuntimeShards.S062
import PA211.UserCandidate.RuntimeShards.S063
set_option maxRecDepth 100000
set_option maxHeartbeats 32000000
namespace PA211.UserCandidate.CoverageShards.S048
open PA215.Source PA211.UserCandidate.PrimitiveSimulation
def e3072 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,false,true,false], .inc 1⟩, .inc 1 (some 3073), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,false,true,false] 1 (some 3073) 0 373 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3072_plain_checked⟩

def e3073 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,false,true,true], .continueTo 2⟩, .jump (some 3071), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,false,true,true] (some 3071) 0 101 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3073_plain_checked⟩

def e3074 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,true,false,false,false], .dec 1⟩, .dec 1 (some 3078) (some 3075), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,true,false,false,false] 1 (some 3078) (some 3075) 0 1 381 387 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3074_zero_checked PA211.UserCandidate.RuntimeShards.S062.s3074_positive_checked⟩

def e3075 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,true,false,false,true,false], .inc 7⟩, .inc 7 (some 3076), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,true,false,false,true,false] 7 (some 3076) 0 400 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3075_plain_checked⟩

def e3076 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,true,false,false,true,true,false], .inc 6⟩, .inc 6 (some 3077), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,true,false,false,true,true,false] 6 (some 3077) 0 427 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3076_plain_checked⟩

def e3077 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,true,false,false,true,true,true], .continueTo 3⟩, .jump (some 3074), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,true,false,false,true,true,true] (some 3074) 0 116 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3077_plain_checked⟩

def e3078 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 3084) (some 3079), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,true,false,true,false] 6 (some 3084) (some 3079) 0 1 402 405 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3078_zero_checked PA211.UserCandidate.RuntimeShards.S062.s3078_positive_checked⟩

def e3079 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,true,false,true,true,false,false], .inc 7⟩, .inc 7 (some 3080), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,true,false,true,true,false,false] 7 (some 3080) 0 400 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3079_plain_checked⟩

def e3080 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,true,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 3083) (some 3081), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,true,false,true,true,false,true,false] 6 (some 3083) (some 3081) 0 1 420 423 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3080_zero_checked PA211.UserCandidate.RuntimeShards.S062.s3080_positive_checked⟩

def e3081 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,true,false,true,true,false,true,true,false], .inc 1⟩, .inc 1 (some 3082), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,true,false,true,true,false,true,true,false] 1 (some 3082) 0 418 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3081_plain_checked⟩

def e3082 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,true,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 3080), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,true,false,true,true,false,true,true,true] (some 3080) 0 116 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3082_plain_checked⟩

def e3083 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,true,false,true,true,true], .continueTo 3⟩, .jump (some 3074), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,true,false,true,true,true] (some 3074) 0 119 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3083_plain_checked⟩

def e3084 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,true,true,false], .dec 7⟩, .dec 7 (some 3087) (some 3085), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,true,true,false] 7 (some 3087) (some 3085) 0 1 390 387 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3084_zero_checked PA211.UserCandidate.RuntimeShards.S062.s3084_positive_checked⟩

def e3085 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,true,true,true,false], .inc 2⟩, .inc 2 (some 3086), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,true,true,true,false] 2 (some 3086) 0 400 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3085_plain_checked⟩

def e3086 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,true,true,true,true], .continueTo 2⟩, .jump (some 3084), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,false,true,true,true,true,true] (some 3084) 0 107 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3086_plain_checked⟩

def e3087 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,true,false,false], .dec 5⟩, .dec 5 (some 3091) (some 3088), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,true,false,false] 5 (some 3091) (some 3088) 0 1 354 360 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3087_zero_checked PA211.UserCandidate.RuntimeShards.S062.s3087_positive_checked⟩

def e3088 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,true,false,true,false], .inc 1⟩, .inc 1 (some 3089), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,true,false,true,false] 1 (some 3089) 0 364 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3088_plain_checked⟩

def e3089 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,true,false,true,true,false], .inc 6⟩, .inc 6 (some 3090), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,true,false,true,true,false] 6 (some 3090) 0 391 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3089_plain_checked⟩

def e3090 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,true,false,true,true,true], .continueTo 3⟩, .jump (some 3087), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,true,false,true,true,true] (some 3087) 0 104 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3090_plain_checked⟩

def e3091 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,true,true,false], .dec 6⟩, .dec 6 (some 3094) (some 3092), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,true,true,false] 6 (some 3094) (some 3092) 0 1 363 360 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3091_zero_checked PA211.UserCandidate.RuntimeShards.S062.s3091_positive_checked⟩

def e3092 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,false], .inc 5⟩, .inc 5 (some 3093), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,false] 5 (some 3093) 0 391 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3092_plain_checked⟩

def e3093 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true], .continueTo 2⟩, .jump (some 3091), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,false,true,true,true,true,true] (some 3091) 0 98 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3093_plain_checked⟩

def e3094 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,false,false,false], .dec 2⟩, .dec 2 (some 3102) (some 3095), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,false,false,false] 2 (some 3102) (some 3095) 0 1 366 372 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3094_zero_checked PA211.UserCandidate.RuntimeShards.S062.s3094_positive_checked⟩

def e3095 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,false,false,true,false], .inc 7⟩, .inc 7 (some 3096), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,false,false,true,false] 7 (some 3096) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3095_plain_checked⟩

def e3096 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,false,false,true,true,false,false,false], .dec 6⟩, .dec 6 (some 3098) (some 3097), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,false,false,true,true,false,false,false] 6 (some 3098) (some 3097) 0 1 408 414 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3096_zero_checked PA211.UserCandidate.RuntimeShards.S062.s3096_positive_checked⟩

def e3097 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,false,false,true,true,false,false,true], .breakTo 1⟩, .jump (some 3101), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,false,false,true,true,false,false,true] (some 3101) 0 113 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3097_plain_checked⟩

def e3098 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,false,false,true,true,false,true,false], .dec 7⟩, .dec 7 (some 3101) (some 3099), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,false,false,true,true,false,true,false] 7 (some 3101) (some 3099) 0 1 420 423 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3098_zero_checked PA211.UserCandidate.RuntimeShards.S062.s3098_positive_checked⟩

def e3099 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,false,false,true,true,false,true,true,false], .inc 6⟩, .inc 6 (some 3100), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,false,false,true,true,false,true,true,false] 6 (some 3100) 0 427 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3099_plain_checked⟩

def e3100 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,false,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 3098), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,false,false,true,true,false,true,true,true] (some 3098) 0 116 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3100_plain_checked⟩

def e3101 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,false,false,true,true,true], .continueTo 3⟩, .jump (some 3094), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,false,false,true,true,true] (some 3094) 0 107 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3101_plain_checked⟩

def e3102 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,false,true,false], .dec 7⟩, .dec 7 (some 3105) (some 3103), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,false,true,false] 7 (some 3105) (some 3103) 0 1 366 369 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3102_zero_checked PA211.UserCandidate.RuntimeShards.S062.s3102_positive_checked⟩

def e3103 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,false,true,true,false], .inc 2⟩, .inc 2 (some 3104), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,false,true,true,false] 2 (some 3104) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S062.s3103_plain_checked⟩

def e3104 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,false,true,true,true], .continueTo 2⟩, .jump (some 3102), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,false,true,true,true] (some 3102) 0 101 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3104_plain_checked⟩

def e3105 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,false,false,false], .dec 1⟩, .dec 1 (some 3109) (some 3106), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,false,false,false] 1 (some 3109) (some 3106) 0 1 363 369 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3105_zero_checked PA211.UserCandidate.RuntimeShards.S063.s3105_positive_checked⟩

def e3106 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,false,false,true,false], .inc 7⟩, .inc 7 (some 3107), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,false,false,true,false] 7 (some 3107) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3106_plain_checked⟩

def e3107 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,false,false,true,true,false], .inc 6⟩, .inc 6 (some 3108), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,false,false,true,true,false] 6 (some 3108) 0 409 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3107_plain_checked⟩

def e3108 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,false,false,true,true,true], .continueTo 3⟩, .jump (some 3105), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,false,false,true,true,true] (some 3105) 0 110 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3108_plain_checked⟩

def e3109 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,false,true,false], .dec 6⟩, .dec 6 (some 3115) (some 3110), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,false,true,false] 6 (some 3115) (some 3110) 0 1 384 387 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3109_zero_checked PA211.UserCandidate.RuntimeShards.S063.s3109_positive_checked⟩

def e3110 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,false,true,true,false,false], .inc 7⟩, .inc 7 (some 3111), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,false,true,true,false,false] 7 (some 3111) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3110_plain_checked⟩

def e3111 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 3114) (some 3112), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,false,true,true,false,true,false] 6 (some 3114) (some 3112) 0 1 402 405 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3111_zero_checked PA211.UserCandidate.RuntimeShards.S063.s3111_positive_checked⟩

def e3112 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,false,true,true,false,true,true,false], .inc 1⟩, .inc 1 (some 3113), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,false,true,true,false,true,true,false] 1 (some 3113) 0 400 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3112_plain_checked⟩

def e3113 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 3111), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,false,true,true,false,true,true,true] (some 3111) 0 110 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3113_plain_checked⟩

def e3114 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,false,true,true,true], .continueTo 3⟩, .jump (some 3105), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,false,true,true,true] (some 3105) 0 113 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3114_plain_checked⟩

def e3115 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false], .dec 7⟩, .dec 7 (some 3121) (some 3116), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] 7 (some 3121) (some 3116) 0 1 369 369 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3115_zero_checked PA211.UserCandidate.RuntimeShards.S063.s3115_positive_checked⟩

def e3116 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,true,true,false,false,false], .inc 1⟩, .inc 1 (some 3117), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,true,true,false,false,false] 1 (some 3117) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3116_plain_checked⟩

def e3117 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,true,true,false,false,true], .inc 1⟩, .inc 1 (some 3118), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,true,true,false,false,true] 1 (some 3118) 0 385 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3117_plain_checked⟩

def e3118 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,true,true,false,true,false], .inc 1⟩, .inc 1 (some 3119), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,true,true,false,true,false] 1 (some 3119) 0 391 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3118_plain_checked⟩

def e3119 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,true,true,false,true,true], .inc 1⟩, .inc 1 (some 3120), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,true,true,false,true,true] 1 (some 3120) 0 397 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3119_plain_checked⟩

def e3120 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,true,true,true], .continueTo 2⟩, .jump (some 3115), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,false,true,true,true,true] (some 3115) 0 98 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3120_plain_checked⟩

def e3121 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true], .inc 1⟩, .inc 1 (some 3122), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,false,true,true,true] 1 (some 3122) 0 346 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3121_plain_checked⟩

def e3122 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,true,false,false,false,false,false], .dec 2⟩, .dec 2 (some 3130) (some 3123), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,true,false,false,false,false,false] 2 (some 3130) (some 3123) 0 1 357 363 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3122_zero_checked PA211.UserCandidate.RuntimeShards.S063.s3122_positive_checked⟩

def e3123 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,true,false,false,false,false,true,false], .inc 7⟩, .inc 7 (some 3124), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,true,false,false,false,false,true,false] 7 (some 3124) 0 373 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3123_plain_checked⟩

def e3124 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,true,false,false,false,false,true,true,false,false,false], .dec 6⟩, .dec 6 (some 3126) (some 3125), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,true,false,false,false,false,true,true,false,false,false] 6 (some 3126) (some 3125) 0 1 399 405 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3124_zero_checked PA211.UserCandidate.RuntimeShards.S063.s3124_positive_checked⟩

def e3125 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,true,false,false,false,false,true,true,false,false,true], .breakTo 1⟩, .jump (some 3129), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,true,false,false,false,false,true,true,false,false,true] (some 3129) 0 110 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3125_plain_checked⟩

def e3126 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,true,false,false,false,false,true,true,false,true,false], .dec 7⟩, .dec 7 (some 3129) (some 3127), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,true,false,false,false,false,true,true,false,true,false] 7 (some 3129) (some 3127) 0 1 411 414 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3126_zero_checked PA211.UserCandidate.RuntimeShards.S063.s3126_positive_checked⟩

def e3127 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,true,false,false,false,false,true,true,false,true,true,false], .inc 6⟩, .inc 6 (some 3128), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,true,false,false,false,false,true,true,false,true,true,false] 6 (some 3128) 0 418 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3127_plain_checked⟩

def e3128 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,true,false,false,false,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 3126), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,true,false,false,false,false,true,true,false,true,true,true] (some 3126) 0 113 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3128_plain_checked⟩

def e3129 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,true,false,false,false,false,true,true,true], .continueTo 3⟩, .jump (some 3122), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,true,false,false,false,false,true,true,true] (some 3122) 0 104 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3129_plain_checked⟩

def e3130 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,true,false,false,false,true,false], .dec 7⟩, .dec 7 (some 3133) (some 3131), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,true,false,false,false,true,false] 7 (some 3133) (some 3131) 0 1 357 360 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3130_zero_checked PA211.UserCandidate.RuntimeShards.S063.s3130_positive_checked⟩

def e3131 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,true,false,false,false,true,true,false], .inc 2⟩, .inc 2 (some 3132), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,true,false,false,false,true,true,false] 2 (some 3132) 0 373 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3131_plain_checked⟩

def e3132 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,true,false,false,false,true,true,true], .continueTo 2⟩, .jump (some 3130), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,true,false,false,false,true,true,true] (some 3130) 0 98 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3132_plain_checked⟩

def e3133 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,true,false,false,true,false,false,false], .dec 1⟩, .dec 1 (some 3137) (some 3134), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,true,false,false,true,false,false,false] 1 (some 3137) (some 3134) 0 1 354 360 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3133_zero_checked PA211.UserCandidate.RuntimeShards.S063.s3133_positive_checked⟩

def e3134 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,true,false,false,true,false,false,true,false], .inc 7⟩, .inc 7 (some 3135), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,true,false,false,true,false,false,true,false] 7 (some 3135) 0 373 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3134_plain_checked⟩

def e3135 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,true,false,false,true,false,false,true,true,false], .inc 6⟩, .inc 6 (some 3136), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,true,true,true,false,false,true,false,false,true,true,false] 6 (some 3136) 0 400 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S063.s3135_plain_checked⟩

def entries : Array (Entry PA211.UserCandidate.Source.path 3947) := #[
  e3072,
  e3073,
  e3074,
  e3075,
  e3076,
  e3077,
  e3078,
  e3079,
  e3080,
  e3081,
  e3082,
  e3083,
  e3084,
  e3085,
  e3086,
  e3087,
  e3088,
  e3089,
  e3090,
  e3091,
  e3092,
  e3093,
  e3094,
  e3095,
  e3096,
  e3097,
  e3098,
  e3099,
  e3100,
  e3101,
  e3102,
  e3103,
  e3104,
  e3105,
  e3106,
  e3107,
  e3108,
  e3109,
  e3110,
  e3111,
  e3112,
  e3113,
  e3114,
  e3115,
  e3116,
  e3117,
  e3118,
  e3119,
  e3120,
  e3121,
  e3122,
  e3123,
  e3124,
  e3125,
  e3126,
  e3127,
  e3128,
  e3129,
  e3130,
  e3131,
  e3132,
  e3133,
  e3134,
  e3135
]
theorem sites_block : entries.toList.map (·.site) =
 (PA211.UserCandidate.Source.sites.toList.drop 3072).take 64 := by decide +kernel
theorem codes_block : entries.toList.map (·.code) =
 (PA213.SourceProgram.codes.toList.drop 3072).take 64 := by decide +kernel
end PA211.UserCandidate.CoverageShards.S048
