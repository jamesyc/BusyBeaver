import PA213.PrimitiveSimulation
import PA213.FastPaths
import PA213.RuntimeShards.S079
import PA213.RuntimeShards.S080
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA213.CoverageShards.S061
open PA215.Source PA213.SourceProgram PA213.PathBounds PA213.PrimitiveSimulation
def e3904 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,true,true,false,true,false], .inc 1⟩, .inc 1 (some 3905), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,true,true,true,true,false,true,false] 1 (some 3905) 0 264 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3904_plain_checked⟩
def e3905 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,true,true,false,true,true,false], .inc 6⟩, .inc 6 (some 3906), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,true,true,true,true,false,true,true,false] 6 (some 3906) 0 291 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3905_plain_checked⟩
def e3906 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,true,true,false,true,true,true], .continueTo 3⟩, .jump (some 3903), implements_jump PA213.FastPaths.path 3947 [true,false,true,false,true,true,true,true,false,true,true,true] (some 3903) 0 70 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3906_plain_checked⟩
def e3907 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,true,true,true,false], .dec 6⟩, .dec 6 (some 3910) (some 3908), implements_dec PA213.FastPaths.path 3947 [true,false,true,false,true,true,true,true,true,false] 6 (some 3910) (some 3908) 0 1 260 251 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3907_zero_checked PA213.RuntimeShards.S079.s3907_positive_checked⟩
def e3908 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,true,true,true,true,false], .inc 4⟩, .inc 4 (some 3909), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,true,true,true,true,true,true,false] 4 (some 3909) 0 267 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3908_plain_checked⟩
def e3909 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,true,true,true,true,true,true,true], .continueTo 2⟩, .jump (some 3907), implements_jump PA213.FastPaths.path 3947 [true,false,true,false,true,true,true,true,true,true,true] (some 3907) 0 61 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3909_plain_checked⟩
def e3910 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,true], .continueTo 3⟩, .jump (some 0), implements_jump PA213.FastPaths.path 3947 [true,false,true,true] (some 0) 0 40 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3910_plain_checked⟩
def e3911 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,false,false], .dec 1⟩, .dec 1 (some 3914) (some 3912), implements_dec PA213.FastPaths.path 3947 [true,true,false,false] 1 (some 3914) (some 3912) 0 1 191 197 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3911_zero_checked PA213.RuntimeShards.S079.s3911_positive_checked⟩
def e3912 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,false,true,false], .inc 6⟩, .inc 6 (some 3913), implements_inc PA213.FastPaths.path 3947 [true,true,false,true,false] 6 (some 3913) 0 210 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3912_plain_checked⟩
def e3913 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,false,true,true], .continueTo 2⟩, .jump (some 3911), implements_jump PA213.FastPaths.path 3947 [true,true,false,true,true] (some 3911) 0 43 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3913_plain_checked⟩
def e3914 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,false,false,false], .dec 5⟩, .dec 5 (some 3918) (some 3915), implements_dec PA213.FastPaths.path 3947 [true,true,true,false,false,false] 5 (some 3918) (some 3915) 0 1 209 215 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3914_zero_checked PA213.RuntimeShards.S079.s3914_positive_checked⟩
def e3915 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,false,false,true,false], .inc 1⟩, .inc 1 (some 3916), implements_inc PA213.FastPaths.path 3947 [true,true,true,false,false,true,false] 1 (some 3916) 0 219 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3915_plain_checked⟩
def e3916 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,false,false,true,true,false], .inc 6⟩, .inc 6 (some 3917), implements_inc PA213.FastPaths.path 3947 [true,true,true,false,false,true,true,false] 6 (some 3917) 0 246 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3916_plain_checked⟩
def e3917 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,false,false,true,true,true], .continueTo 3⟩, .jump (some 3914), implements_jump PA213.FastPaths.path 3947 [true,true,true,false,false,true,true,true] (some 3914) 0 55 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3917_plain_checked⟩
def e3918 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,false,true,false], .dec 6⟩, .dec 6 (some 3921) (some 3919), implements_dec PA213.FastPaths.path 3947 [true,true,true,false,true,false] 6 (some 3921) (some 3919) 0 1 212 215 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3918_zero_checked PA213.RuntimeShards.S079.s3918_positive_checked⟩
def e3919 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,false,true,true,false], .inc 5⟩, .inc 5 (some 3920), implements_inc PA213.FastPaths.path 3947 [true,true,true,false,true,true,false] 5 (some 3920) 0 246 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3919_plain_checked⟩
def e3920 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 3918), implements_jump PA213.FastPaths.path 3947 [true,true,true,false,true,true,true] (some 3918) 0 49 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3920_plain_checked⟩
def e3921 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,true,false], .inc 6⟩, .inc 6 (some 3922), implements_inc PA213.FastPaths.path 3947 [true,true,true,true,false] 6 (some 3922) 0 210 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3921_plain_checked⟩
def e3922 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,true,true,false,false,false,false,false], .dec 5⟩, .dec 5 (some 3926) (some 3923), implements_dec PA213.FastPaths.path 3947 [true,true,true,true,true,false,false,false,false,false] 5 (some 3926) (some 3923) 0 1 245 251 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3922_zero_checked PA213.RuntimeShards.S079.s3922_positive_checked⟩
def e3923 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,true,true,false,false,false,false,true,false,false], .dec 6⟩, .dec 6 (some 3925) (some 3924), implements_dec PA213.FastPaths.path 3947 [true,true,true,true,true,false,false,false,false,true,false,false] 6 (some 3925) (some 3924) 0 1 263 269 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3923_zero_checked PA213.RuntimeShards.S079.s3923_positive_checked⟩
def e3924 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,true,true,false,false,false,false,true,false,true], .continueTo 2⟩, .jump (some 3922), implements_jump PA213.FastPaths.path 3947 [true,true,true,true,true,false,false,false,false,true,false,true] (some 3922) 0 64 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3924_plain_checked⟩
def e3925 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,true,true,false,false,false,false,true,true], .breakTo 1⟩, .jump (some 3927), implements_jump PA213.FastPaths.path 3947 [true,true,true,true,true,false,false,false,false,true,true] (some 3927) 0 78 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3925_plain_checked⟩
def e3926 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,true,true,false,false,false,true], .dec 6⟩, .dec 6 (some 3932) (some 3927), implements_dec PA213.FastPaths.path 3947 [true,true,true,true,true,false,false,false,true] 6 (some 3932) (some 3927) 0 1 239 245 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3926_zero_checked PA213.RuntimeShards.S079.s3926_positive_checked⟩
def e3927 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,true,true,false,false,true,false,false], .dec 5⟩, .dec 5 (some 3929) (some 3928), implements_dec PA213.FastPaths.path 3947 [true,true,true,true,true,false,false,true,false,false] 5 (some 3929) (some 3928) 0 1 254 260 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3927_zero_checked PA213.RuntimeShards.S079.s3927_positive_checked⟩
def e3928 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,true,true,false,false,true,false,true], .continueTo 1⟩, .jump (some 3927), implements_jump PA213.FastPaths.path 3947 [true,true,true,true,true,false,false,true,false,true] (some 3927) 0 58 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3928_plain_checked⟩
def e3929 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,true,true,false,false,true,true,false,false], .dec 6⟩, .dec 6 (some 3931) (some 3930), implements_dec PA213.FastPaths.path 3947 [true,true,true,true,true,false,false,true,true,false,false] 6 (some 3931) (some 3930) 0 1 254 260 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3929_zero_checked PA213.RuntimeShards.S079.s3929_positive_checked⟩
def e3930 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,true,true,false,false,true,true,false,true], .continueTo 2⟩, .jump (some 3927), implements_jump PA213.FastPaths.path 3947 [true,true,true,true,true,false,false,true,true,false,true] (some 3927) 0 61 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3930_plain_checked⟩
def e3931 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,true,true,false,false,true,true,true], .breakTo 1⟩, .jump (some 3933), implements_jump PA213.FastPaths.path 3947 [true,true,true,true,true,false,false,true,true,true] (some 3933) 0 78 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3931_plain_checked⟩
def e3932 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,true,true,false,true], .halt⟩, .halt, implements_halt PA213.FastPaths.path 3947 [true,true,true,true,true,false,true] 8 PA213.RuntimeShards.S079.s3932_plain_checked⟩
def e3933 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,true,true,true,false,false,false], .dec 2⟩, .dec 2 (some 3941) (some 3934), implements_dec PA213.FastPaths.path 3947 [true,true,true,true,true,true,false,false,false] 2 (some 3941) (some 3934) 0 1 257 263 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3933_zero_checked PA213.RuntimeShards.S079.s3933_positive_checked⟩
def e3934 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,true,true,true,false,false,true,false], .inc 7⟩, .inc 7 (some 3935), implements_inc PA213.FastPaths.path 3947 [true,true,true,true,true,true,false,false,true,false] 7 (some 3935) 0 273 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3934_plain_checked⟩
def e3935 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,true,true,true,false,false,true,true,false,false,false], .dec 6⟩, .dec 6 (some 3937) (some 3936), implements_dec PA213.FastPaths.path 3947 [true,true,true,true,true,true,false,false,true,true,false,false,false] 6 (some 3937) (some 3936) 0 1 299 305 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S079.s3935_zero_checked PA213.RuntimeShards.S079.s3935_positive_checked⟩
def e3936 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,true,true,true,false,false,true,true,false,false,true], .breakTo 1⟩, .jump (some 3940), implements_jump PA213.FastPaths.path 3947 [true,true,true,true,true,true,false,false,true,true,false,false,true] (some 3940) 0 76 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S080.s3936_plain_checked⟩
def e3937 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,true,true,true,false,false,true,true,false,true,false], .dec 7⟩, .dec 7 (some 3940) (some 3938), implements_dec PA213.FastPaths.path 3947 [true,true,true,true,true,true,false,false,true,true,false,true,false] 7 (some 3940) (some 3938) 0 1 311 314 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S080.s3937_zero_checked PA213.RuntimeShards.S080.s3937_positive_checked⟩
def e3938 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,true,true,true,false,false,true,true,false,true,true,false], .inc 6⟩, .inc 6 (some 3939), implements_inc PA213.FastPaths.path 3947 [true,true,true,true,true,true,false,false,true,true,false,true,true,false] 6 (some 3939) 0 318 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S080.s3938_plain_checked⟩
def e3939 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,true,true,true,false,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 3937), implements_jump PA213.FastPaths.path 3947 [true,true,true,true,true,true,false,false,true,true,false,true,true,true] (some 3937) 0 79 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S080.s3939_plain_checked⟩
def e3940 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,true,true,true,false,false,true,true,true], .continueTo 3⟩, .jump (some 3933), implements_jump PA213.FastPaths.path 3947 [true,true,true,true,true,true,false,false,true,true,true] (some 3933) 0 70 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S080.s3940_plain_checked⟩
def e3941 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,true,true,true,false,true,false], .dec 7⟩, .dec 7 (some 3944) (some 3942), implements_dec PA213.FastPaths.path 3947 [true,true,true,true,true,true,false,true,false] 7 (some 3944) (some 3942) 0 1 257 260 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S080.s3941_zero_checked PA213.RuntimeShards.S080.s3941_positive_checked⟩
def e3942 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,true,true,true,false,true,true,false], .inc 2⟩, .inc 2 (some 3943), implements_inc PA213.FastPaths.path 3947 [true,true,true,true,true,true,false,true,true,false] 2 (some 3943) 0 273 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S080.s3942_plain_checked⟩
def e3943 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,true,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 3941), implements_jump PA213.FastPaths.path 3947 [true,true,true,true,true,true,false,true,true,true] (some 3941) 0 64 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S080.s3943_plain_checked⟩
def e3944 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,true,true,true,true,false], .dec 6⟩, .dec 6 none (some 3945), implements_dec PA213.FastPaths.path 3947 [true,true,true,true,true,true,true,false] 6 none (some 3945) 1 1 253 233 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S080.s3944_zero_checked PA213.RuntimeShards.S080.s3944_positive_checked⟩
def e3945 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,true,true,true,true,true,false], .inc 5⟩, .inc 5 (some 3946), implements_inc PA213.FastPaths.path 3947 [true,true,true,true,true,true,true,true,false] 5 (some 3946) 0 264 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S080.s3945_plain_checked⟩
def e3946 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,true,true,true,true,true,true,true,true], .continueTo 2⟩, .jump (some 3944), implements_jump PA213.FastPaths.path 3947 [true,true,true,true,true,true,true,true,true] (some 3944) 0 55 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S080.s3946_plain_checked⟩
def entries : Array (Entry PA213.FastPaths.path 3947) := #[
  e3904,
  e3905,
  e3906,
  e3907,
  e3908,
  e3909,
  e3910,
  e3911,
  e3912,
  e3913,
  e3914,
  e3915,
  e3916,
  e3917,
  e3918,
  e3919,
  e3920,
  e3921,
  e3922,
  e3923,
  e3924,
  e3925,
  e3926,
  e3927,
  e3928,
  e3929,
  e3930,
  e3931,
  e3932,
  e3933,
  e3934,
  e3935,
  e3936,
  e3937,
  e3938,
  e3939,
  e3940,
  e3941,
  e3942,
  e3943,
  e3944,
  e3945,
  e3946
]
theorem sites_block : entries.toList.map (·.site) =
    (sites.toList.drop 3904).take 64 := by decide +kernel
theorem codes_block : entries.toList.map (·.code) =
    (codes.toList.drop 3904).take 64 := by decide +kernel
end PA213.CoverageShards.S061
