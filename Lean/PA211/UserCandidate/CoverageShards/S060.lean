import User211SourceEquivalence
import PA211.UserCandidate.PrimitiveSimulation
import PA211.UserCandidate.RuntimeShards.S077
import PA211.UserCandidate.RuntimeShards.S078
import PA211.UserCandidate.RuntimeShards.S079
set_option maxRecDepth 100000
set_option maxHeartbeats 32000000
namespace PA211.UserCandidate.CoverageShards.S060
open PA215.Source PA211.UserCandidate.PrimitiveSimulation
def e3840 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,false,true,true,true,false,true,true,true], .continueTo 3⟩, .jump (some 3837), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,false,true,true,true,false,true,true,true] (some 3837) 0 80 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S077.s3840_plain_checked⟩

def e3841 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,false,true,true,true,true,false], .dec 6⟩, .dec 6 (some 3844) (some 3842), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,false,true,true,true,true,false] 6 (some 3844) (some 3842) 0 1 285 279 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3841_zero_checked PA211.UserCandidate.RuntimeShards.S078.s3841_positive_checked⟩

def e3842 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,false,true,true,true,true,true,false], .inc 4⟩, .inc 4 (some 3843), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,false,true,true,true,true,true,false] 4 (some 3843) 0 295 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3842_plain_checked⟩

def e3843 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,false,true,true,true,true,true,true], .continueTo 2⟩, .jump (some 3841), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,false,true,true,true,true,true,true] (some 3841) 0 71 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3843_plain_checked⟩

def e3844 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,true,false,false,false], .dec 2⟩, .dec 2 (some 3852) (some 3845), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,true,false,false,false] 2 (some 3852) (some 3845) 0 1 267 273 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3844_zero_checked PA211.UserCandidate.RuntimeShards.S078.s3844_positive_checked⟩

def e3845 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,true,false,false,true,false], .inc 7⟩, .inc 7 (some 3846), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,true,false,false,true,false] 7 (some 3846) 0 283 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3845_plain_checked⟩

def e3846 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,true,false,false,true,true,false,false,false], .dec 6⟩, .dec 6 (some 3848) (some 3847), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,true,false,false,true,true,false,false,false] 6 (some 3848) (some 3847) 0 1 309 315 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3846_zero_checked PA211.UserCandidate.RuntimeShards.S078.s3846_positive_checked⟩

def e3847 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,true,false,false,true,true,false,false,true], .breakTo 1⟩, .jump (some 3851), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,true,false,false,true,true,false,false,true] (some 3851) 0 80 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3847_plain_checked⟩

def e3848 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,true,false,false,true,true,false,true,false], .dec 7⟩, .dec 7 (some 3851) (some 3849), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,true,false,false,true,true,false,true,false] 7 (some 3851) (some 3849) 0 1 321 324 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3848_zero_checked PA211.UserCandidate.RuntimeShards.S078.s3848_positive_checked⟩

def e3849 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,true,false,false,true,true,false,true,true,false], .inc 6⟩, .inc 6 (some 3850), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,true,false,false,true,true,false,true,true,false] 6 (some 3850) 0 328 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3849_plain_checked⟩

def e3850 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,true,false,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 3848), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,true,false,false,true,true,false,true,true,true] (some 3848) 0 83 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3850_plain_checked⟩

def e3851 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,true,false,false,true,true,true], .continueTo 3⟩, .jump (some 3844), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,true,false,false,true,true,true] (some 3844) 0 74 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3851_plain_checked⟩

def e3852 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,true,false,true,false], .dec 7⟩, .dec 7 (some 3855) (some 3853), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,true,false,true,false] 7 (some 3855) (some 3853) 0 1 267 270 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3852_zero_checked PA211.UserCandidate.RuntimeShards.S078.s3852_positive_checked⟩

def e3853 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,true,false,true,true,false], .inc 2⟩, .inc 2 (some 3854), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,true,false,true,true,false] 2 (some 3854) 0 283 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3853_plain_checked⟩

def e3854 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,true,false,true,true,true], .continueTo 2⟩, .jump (some 3852), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,true,false,true,true,true] (some 3852) 0 68 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3854_plain_checked⟩

def e3855 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,true,true,false,false,false], .dec 1⟩, .dec 1 (some 3859) (some 3856), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,true,true,false,false,false] 1 (some 3859) (some 3856) 0 1 264 270 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3855_zero_checked PA211.UserCandidate.RuntimeShards.S078.s3855_positive_checked⟩

def e3856 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,true,true,false,false,true,false], .inc 7⟩, .inc 7 (some 3857), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,true,true,false,false,true,false] 7 (some 3857) 0 283 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3856_plain_checked⟩

def e3857 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,true,true,false,false,true,true,false], .inc 6⟩, .inc 6 (some 3858), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,true,true,false,false,true,true,false] 6 (some 3858) 0 310 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3857_plain_checked⟩

def e3858 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,true,true,false,false,true,true,true], .continueTo 3⟩, .jump (some 3855), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,true,true,false,false,true,true,true] (some 3855) 0 77 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3858_plain_checked⟩

def e3859 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 3865) (some 3860), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,true,true,false,true,false] 6 (some 3865) (some 3860) 0 1 285 288 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3859_zero_checked PA211.UserCandidate.RuntimeShards.S078.s3859_positive_checked⟩

def e3860 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,true,true,false,true,true,false,false], .inc 7⟩, .inc 7 (some 3861), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,true,true,false,true,true,false,false] 7 (some 3861) 0 283 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3860_plain_checked⟩

def e3861 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,true,true,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 3864) (some 3862), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,true,true,false,true,true,false,true,false] 6 (some 3864) (some 3862) 0 1 303 306 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3861_zero_checked PA211.UserCandidate.RuntimeShards.S078.s3861_positive_checked⟩

def e3862 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,true,true,false,true,true,false,true,true,false], .inc 1⟩, .inc 1 (some 3863), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,true,true,false,true,true,false,true,true,false] 1 (some 3863) 0 301 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3862_plain_checked⟩

def e3863 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,true,true,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 3861), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,true,true,false,true,true,false,true,true,true] (some 3861) 0 77 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3863_plain_checked⟩

def e3864 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,true,true,false,true,true,true], .continueTo 3⟩, .jump (some 3855), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,true,true,false,true,true,true] (some 3855) 0 80 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3864_plain_checked⟩

def e3865 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,true,true,true,false], .dec 7⟩, .dec 7 (some 3871) (some 3866), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,true,true,true,false] 7 (some 3871) (some 3866) 0 1 273 270 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3865_zero_checked PA211.UserCandidate.RuntimeShards.S078.s3865_positive_checked⟩

def e3866 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,true,true,true,true,false,false,false], .inc 1⟩, .inc 1 (some 3867), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,true,true,true,true,false,false,false] 1 (some 3867) 0 283 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3866_plain_checked⟩

def e3867 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,true,true,true,true,false,false,true], .inc 1⟩, .inc 1 (some 3868), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,true,true,true,true,false,false,true] 1 (some 3868) 0 286 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3867_plain_checked⟩

def e3868 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,true,true,true,true,false,true,false], .inc 1⟩, .inc 1 (some 3869), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,true,true,true,true,false,true,false] 1 (some 3869) 0 292 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3868_plain_checked⟩

def e3869 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,true,true,true,true,false,true,true], .inc 1⟩, .inc 1 (some 3870), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,true,true,true,true,false,true,true] 1 (some 3870) 0 298 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3869_plain_checked⟩

def e3870 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,false,true,true,true,true,true], .continueTo 2⟩, .jump (some 3865), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,false,true,true,true,true,true] (some 3865) 0 65 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3870_plain_checked⟩

def e3871 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,true,false], .dec 1⟩, .dec 1 (some 3874) (some 3872), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,true,false] 1 (some 3874) (some 3872) 0 1 231 234 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3871_zero_checked PA211.UserCandidate.RuntimeShards.S078.s3871_positive_checked⟩

def e3872 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,true,true,false], .inc 6⟩, .inc 6 (some 3873), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,true,true,false] 6 (some 3873) 0 247 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3872_plain_checked⟩

def e3873 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,false,true,true,true], .continueTo 2⟩, .jump (some 3871), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,false,true,true,true] (some 3871) 0 56 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3873_plain_checked⟩

def e3874 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,false,false,false,false], .dec 5⟩, .dec 5 (some 3878) (some 3875), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,false,false,false,false] 5 (some 3878) (some 3875) 0 1 255 261 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3874_zero_checked PA211.UserCandidate.RuntimeShards.S078.s3874_positive_checked⟩

def e3875 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,false,false,false,true,false,false], .dec 6⟩, .dec 6 (some 3877) (some 3876), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,false,false,false,true,false,false] 6 (some 3877) (some 3876) 0 1 273 279 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3875_zero_checked PA211.UserCandidate.RuntimeShards.S078.s3875_positive_checked⟩

def e3876 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,false,false,false,true,false,true], .continueTo 2⟩, .jump (some 3874), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,false,false,false,true,false,true] (some 3874) 0 68 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3876_plain_checked⟩

def e3877 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,false,false,false,true,true], .breakTo 1⟩, .jump (some 3879), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,false,false,false,true,true] (some 3879) 0 82 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3877_plain_checked⟩

def e3878 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,false,false,true], .dec 6⟩, .dec 6 (some 3884) (some 3879), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,false,false,true] 6 (some 3884) (some 3879) 0 1 249 255 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3878_zero_checked PA211.UserCandidate.RuntimeShards.S078.s3878_positive_checked⟩

def e3879 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,false,true,false,false], .dec 5⟩, .dec 5 (some 3881) (some 3880), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,false,true,false,false] 5 (some 3881) (some 3880) 0 1 264 270 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3879_zero_checked PA211.UserCandidate.RuntimeShards.S078.s3879_positive_checked⟩

def e3880 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,false,true,false,true], .continueTo 1⟩, .jump (some 3879), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,false,true,false,true] (some 3879) 0 62 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3880_plain_checked⟩

def e3881 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,false,true,true,false,false], .dec 6⟩, .dec 6 (some 3883) (some 3882), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,false,true,true,false,false] 6 (some 3883) (some 3882) 0 1 264 270 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3881_zero_checked PA211.UserCandidate.RuntimeShards.S078.s3881_positive_checked⟩

def e3882 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,false,true,true,false,true], .continueTo 2⟩, .jump (some 3879), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,false,true,true,false,true] (some 3879) 0 65 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3882_plain_checked⟩

def e3883 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,false,true,true,true], .breakTo 1⟩, .jump (some 3910), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,false,true,true,true] (some 3910) 0 88 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3883_plain_checked⟩

def e3884 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,true,false,false,false], .dec 1⟩, .dec 1 (some 3887) (some 3885), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,true,false,false,false] 1 (some 3887) (some 3885) 0 1 246 252 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3884_zero_checked PA211.UserCandidate.RuntimeShards.S078.s3884_positive_checked⟩

def e3885 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,true,false,false,true,false], .inc 6⟩, .inc 6 (some 3886), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,true,false,false,true,false] 6 (some 3886) 0 265 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3885_plain_checked⟩

def e3886 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,true,false,false,true,true], .continueTo 2⟩, .jump (some 3884), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,true,false,false,true,true] (some 3884) 0 62 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3886_plain_checked⟩

def e3887 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,true,false,true,false,false], .dec 2⟩, .dec 2 (some 3890) (some 3888), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,true,false,true,false,false] 2 (some 3890) (some 3888) 0 1 267 273 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S078.s3887_zero_checked PA211.UserCandidate.RuntimeShards.S078.s3887_positive_checked⟩

def e3888 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,true,false,true,false,true,false], .inc 1⟩, .inc 1 (some 3889), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,true,false,true,false,true,false] 1 (some 3889) 0 265 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S079.s3888_plain_checked⟩

def e3889 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,true,false,true,false,true,true], .continueTo 2⟩, .jump (some 3887), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,true,false,true,false,true,true] (some 3887) 0 65 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S079.s3889_plain_checked⟩

def e3890 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,true,false,true,true,false,false,false], .dec 1⟩, .dec 1 (some 3894) (some 3891), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,true,false,true,true,false,false,false] 1 (some 3894) (some 3891) 0 1 273 279 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S079.s3890_zero_checked PA211.UserCandidate.RuntimeShards.S079.s3890_positive_checked⟩

def e3891 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,true,false,true,true,false,false,true,false], .inc 7⟩, .inc 7 (some 3892), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,true,false,true,true,false,false,true,false] 7 (some 3892) 0 292 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S079.s3891_plain_checked⟩

def e3892 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,true,false,true,true,false,false,true,true,false], .inc 6⟩, .inc 6 (some 3893), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,true,false,true,true,false,false,true,true,false] 6 (some 3893) 0 319 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S079.s3892_plain_checked⟩

def e3893 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,true,false,true,true,false,false,true,true,true], .continueTo 3⟩, .jump (some 3890), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,true,false,true,true,false,false,true,true,true] (some 3890) 0 80 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S079.s3893_plain_checked⟩

def e3894 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,true,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 3900) (some 3895), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,true,false,true,true,false,true,false] 6 (some 3900) (some 3895) 0 1 294 297 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S079.s3894_zero_checked PA211.UserCandidate.RuntimeShards.S079.s3894_positive_checked⟩

def e3895 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,true,false,true,true,false,true,true,false,false], .inc 7⟩, .inc 7 (some 3896), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,true,false,true,true,false,true,true,false,false] 7 (some 3896) 0 292 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S079.s3895_plain_checked⟩

def e3896 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,true,false,true,true,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 3899) (some 3897), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,true,false,true,true,false,true,true,false,true,false] 6 (some 3899) (some 3897) 0 1 312 315 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S079.s3896_zero_checked PA211.UserCandidate.RuntimeShards.S079.s3896_positive_checked⟩

def e3897 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,true,false,true,true,false,true,true,false,true,true,false], .inc 1⟩, .inc 1 (some 3898), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,true,false,true,true,false,true,true,false,true,true,false] 1 (some 3898) 0 310 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S079.s3897_plain_checked⟩

def e3898 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,true,false,true,true,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 3896), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,true,false,true,true,false,true,true,false,true,true,true] (some 3896) 0 80 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S079.s3898_plain_checked⟩

def e3899 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,true,false,true,true,false,true,true,true], .continueTo 3⟩, .jump (some 3890), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,true,false,true,true,false,true,true,true] (some 3890) 0 83 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S079.s3899_plain_checked⟩

def e3900 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,true,false,true,true,true,false], .dec 7⟩, .dec 7 (some 3903) (some 3901), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,true,false,true,true,true,false] 7 (some 3903) (some 3901) 0 1 282 279 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S079.s3900_zero_checked PA211.UserCandidate.RuntimeShards.S079.s3900_positive_checked⟩

def e3901 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,true,false,true,true,true,true,false], .inc 2⟩, .inc 2 (some 3902), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,true,false,true,true,true,true,false] 2 (some 3902) 0 292 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S079.s3901_plain_checked⟩

def e3902 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,true,false,true,true,true,true,true], .continueTo 2⟩, .jump (some 3900), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,true,false,true,true,true,true,true] (some 3900) 0 71 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S079.s3902_plain_checked⟩

def e3903 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,true,true,false,false], .dec 4⟩, .dec 4 (some 3907) (some 3904), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,true,true,true,true,false,false] 4 (some 3907) (some 3904) 0 1 246 252 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S079.s3903_zero_checked PA211.UserCandidate.RuntimeShards.S079.s3903_positive_checked⟩

def entries : Array (Entry PA211.UserCandidate.Source.path 3947) := #[
  e3840,
  e3841,
  e3842,
  e3843,
  e3844,
  e3845,
  e3846,
  e3847,
  e3848,
  e3849,
  e3850,
  e3851,
  e3852,
  e3853,
  e3854,
  e3855,
  e3856,
  e3857,
  e3858,
  e3859,
  e3860,
  e3861,
  e3862,
  e3863,
  e3864,
  e3865,
  e3866,
  e3867,
  e3868,
  e3869,
  e3870,
  e3871,
  e3872,
  e3873,
  e3874,
  e3875,
  e3876,
  e3877,
  e3878,
  e3879,
  e3880,
  e3881,
  e3882,
  e3883,
  e3884,
  e3885,
  e3886,
  e3887,
  e3888,
  e3889,
  e3890,
  e3891,
  e3892,
  e3893,
  e3894,
  e3895,
  e3896,
  e3897,
  e3898,
  e3899,
  e3900,
  e3901,
  e3902,
  e3903
]
theorem sites_block : entries.toList.map (·.site) =
 (PA211.UserCandidate.Source.sites.toList.drop 3840).take 64 := by decide +kernel
theorem codes_block : entries.toList.map (·.code) =
 (PA213.SourceProgram.codes.toList.drop 3840).take 64 := by decide +kernel
end PA211.UserCandidate.CoverageShards.S060
