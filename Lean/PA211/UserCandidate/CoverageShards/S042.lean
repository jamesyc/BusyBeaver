module

public import User211SourceEquivalence
public import PA211.UserCandidate.PrimitiveSimulation
public import PA211.UserCandidate.RuntimeShards.S054
public import PA211.UserCandidate.RuntimeShards.S055

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 32000000
namespace PA211.UserCandidate.CoverageShards.S042
open PA215.Source PA211.UserCandidate.PrimitiveSimulation
def e2688 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,false,true,true,false,true,false], .inc 1⟩, .inc 1 (some 2689), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,false,true,true,false,true,false] 1 (some 2689) 0 319 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S054.s2688_plain_checked⟩

def e2689 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,false,true,true,false,true,true,false], .inc 6⟩, .inc 6 (some 2690), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,false,true,true,false,true,true,false] 6 (some 2690) 0 346 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S054.s2689_plain_checked⟩

def e2690 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,false,true,true,false,true,true,true], .continueTo 3⟩, .jump (some 2687), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,false,true,true,false,true,true,true] (some 2687) 0 89 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S054.s2690_plain_checked⟩

def e2691 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,false,true,true,true,false], .dec 6⟩, .dec 6 (some 2694) (some 2692), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,false,true,true,true,false] 6 (some 2694) (some 2692) 0 1 318 315 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S054.s2691_zero_checked PA211.UserCandidate.RuntimeShards.S054.s2691_positive_checked⟩

def e2692 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,false,true,true,true,true,false], .inc 5⟩, .inc 5 (some 2693), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,false,true,true,true,true,false] 5 (some 2693) 0 346 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S054.s2692_plain_checked⟩

def e2693 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,false,true,true,true,true,true], .continueTo 2⟩, .jump (some 2691), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,false,true,true,true,true,true] (some 2691) 0 83 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S054.s2693_plain_checked⟩

def e2694 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,true,false,false,false,false], .dec 2⟩, .dec 2 (some 2702) (some 2695), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,true,false,false,false,false] 2 (some 2702) (some 2695) 0 1 321 327 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S054.s2694_zero_checked PA211.UserCandidate.RuntimeShards.S054.s2694_positive_checked⟩

def e2695 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,true,false,false,false,true,false], .inc 7⟩, .inc 7 (some 2696), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,true,false,false,false,true,false] 7 (some 2696) 0 337 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S054.s2695_plain_checked⟩

def e2696 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,true,false,false,false,true,true,false,false,false], .dec 6⟩, .dec 6 (some 2698) (some 2697), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,true,false,false,false,true,true,false,false,false] 6 (some 2698) (some 2697) 0 1 363 369 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S054.s2696_zero_checked PA211.UserCandidate.RuntimeShards.S054.s2696_positive_checked⟩

def e2697 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,true,false,false,false,true,true,false,false,true], .breakTo 1⟩, .jump (some 2701), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,true,false,false,false,true,true,false,false,true] (some 2701) 0 98 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S054.s2697_plain_checked⟩

def e2698 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,true,false,false,false,true,true,false,true,false], .dec 7⟩, .dec 7 (some 2701) (some 2699), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,true,false,false,false,true,true,false,true,false] 7 (some 2701) (some 2699) 0 1 375 378 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S054.s2698_zero_checked PA211.UserCandidate.RuntimeShards.S054.s2698_positive_checked⟩

def e2699 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,true,false,false,false,true,true,false,true,true,false], .inc 6⟩, .inc 6 (some 2700), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,true,false,false,false,true,true,false,true,true,false] 6 (some 2700) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S054.s2699_plain_checked⟩

def e2700 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,true,false,false,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 2698), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,true,false,false,false,true,true,false,true,true,true] (some 2698) 0 101 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S054.s2700_plain_checked⟩

def e2701 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,true,false,false,false,true,true,true], .continueTo 3⟩, .jump (some 2694), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,true,false,false,false,true,true,true] (some 2694) 0 92 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S054.s2701_plain_checked⟩

def e2702 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,true,false,false,true,false], .dec 7⟩, .dec 7 (some 2705) (some 2703), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,true,false,false,true,false] 7 (some 2705) (some 2703) 0 1 321 324 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S054.s2702_zero_checked PA211.UserCandidate.RuntimeShards.S054.s2702_positive_checked⟩

def e2703 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,true,false,false,true,true,false], .inc 2⟩, .inc 2 (some 2704), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,true,false,false,true,true,false] 2 (some 2704) 0 337 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S054.s2703_plain_checked⟩

def e2704 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,true,false,false,true,true,true], .continueTo 2⟩, .jump (some 2702), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,true,false,false,true,true,true] (some 2702) 0 86 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S054.s2704_plain_checked⟩

def e2705 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,false,false,false], .dec 1⟩, .dec 1 (some 2709) (some 2706), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,false,false,false] 1 (some 2709) (some 2706) 0 1 318 324 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S054.s2705_zero_checked PA211.UserCandidate.RuntimeShards.S054.s2705_positive_checked⟩

def e2706 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,false,false,true,false], .inc 7⟩, .inc 7 (some 2707), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,false,false,true,false] 7 (some 2707) 0 337 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S054.s2706_plain_checked⟩

def e2707 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,false,false,true,true,false], .inc 6⟩, .inc 6 (some 2708), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,false,false,true,true,false] 6 (some 2708) 0 364 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S054.s2707_plain_checked⟩

def e2708 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,false,false,true,true,true], .continueTo 3⟩, .jump (some 2705), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,false,false,true,true,true] (some 2705) 0 95 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S054.s2708_plain_checked⟩

def e2709 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,false,true,false], .dec 6⟩, .dec 6 (some 2715) (some 2710), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,false,true,false] 6 (some 2715) (some 2710) 0 1 339 342 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S054.s2709_zero_checked PA211.UserCandidate.RuntimeShards.S054.s2709_positive_checked⟩

def e2710 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,false,true,true,false,false], .inc 7⟩, .inc 7 (some 2711), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,false,true,true,false,false] 7 (some 2711) 0 337 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2710_plain_checked⟩

def e2711 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 2714) (some 2712), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,false,true,true,false,true,false] 6 (some 2714) (some 2712) 0 1 357 360 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2711_zero_checked PA211.UserCandidate.RuntimeShards.S055.s2711_positive_checked⟩

def e2712 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,false,true,true,false,true,true,false], .inc 1⟩, .inc 1 (some 2713), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,false,true,true,false,true,true,false] 1 (some 2713) 0 355 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2712_plain_checked⟩

def e2713 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 2711), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,false,true,true,false,true,true,true] (some 2711) 0 95 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2713_plain_checked⟩

def e2714 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,false,true,true,true], .continueTo 3⟩, .jump (some 2705), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,false,true,true,true] (some 2705) 0 98 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2714_plain_checked⟩

def e2715 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,true,false], .dec 7⟩, .dec 7 (some 2721) (some 2716), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,true,false] 7 (some 2721) (some 2716) 0 1 324 324 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2715_zero_checked PA211.UserCandidate.RuntimeShards.S055.s2715_positive_checked⟩

def e2716 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,true,true,false,false,false], .inc 1⟩, .inc 1 (some 2717), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,true,true,false,false,false] 1 (some 2717) 0 337 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2716_plain_checked⟩

def e2717 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,true,true,false,false,true], .inc 1⟩, .inc 1 (some 2718), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,true,true,false,false,true] 1 (some 2718) 0 340 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2717_plain_checked⟩

def e2718 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,true,true,false,true,false], .inc 1⟩, .inc 1 (some 2719), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,true,true,false,true,false] 1 (some 2719) 0 346 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2718_plain_checked⟩

def e2719 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,true,true,false,true,true], .inc 1⟩, .inc 1 (some 2720), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,true,true,false,true,true] 1 (some 2720) 0 352 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2719_plain_checked⟩

def e2720 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,true,true,true], .continueTo 2⟩, .jump (some 2715), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,true,false,true,true,true,true] (some 2715) 0 83 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2720_plain_checked⟩

def e2721 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,false,true,true], .inc 1⟩, .inc 1 (some 2722), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,false,true,true] 1 (some 2722) 0 298 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2721_plain_checked⟩

def e2722 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,false,false], .dec 1⟩, .dec 1 (some 2725) (some 2723), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,false,false] 1 (some 2725) (some 2723) 0 1 318 324 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2722_zero_checked PA211.UserCandidate.RuntimeShards.S055.s2722_positive_checked⟩

def e2723 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,false,true,false], .inc 6⟩, .inc 6 (some 2724), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,false,true,false] 6 (some 2724) 0 337 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2723_plain_checked⟩

def e2724 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,false,true,true], .continueTo 2⟩, .jump (some 2722), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,false,true,true] (some 2722) 0 86 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2724_plain_checked⟩

def e2725 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,false,false], .dec 2⟩, .dec 2 (some 2728) (some 2726), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,false,false] 2 (some 2728) (some 2726) 0 1 339 345 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2725_zero_checked PA211.UserCandidate.RuntimeShards.S055.s2725_positive_checked⟩

def e2726 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,false,true,false], .inc 1⟩, .inc 1 (some 2727), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,false,true,false] 1 (some 2727) 0 337 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2726_plain_checked⟩

def e2727 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,false,true,true], .continueTo 2⟩, .jump (some 2725), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,false,true,true] (some 2725) 0 89 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2727_plain_checked⟩

def e2728 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,true,false,false,false], .dec 1⟩, .dec 1 (some 2732) (some 2729), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,true,false,false,false] 1 (some 2732) (some 2729) 0 1 345 351 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2728_zero_checked PA211.UserCandidate.RuntimeShards.S055.s2728_positive_checked⟩

def e2729 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,true,false,false,true,false], .inc 7⟩, .inc 7 (some 2730), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,true,false,false,true,false] 7 (some 2730) 0 364 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2729_plain_checked⟩

def e2730 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,true,false,false,true,true,false], .inc 6⟩, .inc 6 (some 2731), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,true,false,false,true,true,false] 6 (some 2731) 0 391 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2730_plain_checked⟩

def e2731 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,true,false,false,true,true,true], .continueTo 3⟩, .jump (some 2728), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,true,false,false,true,true,true] (some 2728) 0 104 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2731_plain_checked⟩

def e2732 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 2738) (some 2733), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,true,false,true,false] 6 (some 2738) (some 2733) 0 1 366 369 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2732_zero_checked PA211.UserCandidate.RuntimeShards.S055.s2732_positive_checked⟩

def e2733 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,true,false,true,true,false,false], .inc 7⟩, .inc 7 (some 2734), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,true,false,true,true,false,false] 7 (some 2734) 0 364 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2733_plain_checked⟩

def e2734 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,true,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 2737) (some 2735), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,true,false,true,true,false,true,false] 6 (some 2737) (some 2735) 0 1 384 387 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2734_zero_checked PA211.UserCandidate.RuntimeShards.S055.s2734_positive_checked⟩

def e2735 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,true,false,true,true,false,true,true,false], .inc 1⟩, .inc 1 (some 2736), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,true,false,true,true,false,true,true,false] 1 (some 2736) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2735_plain_checked⟩

def e2736 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,true,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 2734), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,true,false,true,true,false,true,true,true] (some 2734) 0 104 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2736_plain_checked⟩

def e2737 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,true,false,true,true,true], .continueTo 3⟩, .jump (some 2728), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,true,false,true,true,true] (some 2728) 0 107 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2737_plain_checked⟩

def e2738 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,true,true,false], .dec 7⟩, .dec 7 (some 2741) (some 2739), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,true,true,false] 7 (some 2741) (some 2739) 0 1 354 351 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2738_zero_checked PA211.UserCandidate.RuntimeShards.S055.s2738_positive_checked⟩

def e2739 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,true,true,true,false], .inc 2⟩, .inc 2 (some 2740), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,true,true,true,false] 2 (some 2740) 0 364 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2739_plain_checked⟩

def e2740 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,true,true,true,true], .continueTo 2⟩, .jump (some 2738), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,false,true,true,true,true,true] (some 2738) 0 95 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2740_plain_checked⟩

def e2741 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,true,false,false], .dec 3⟩, .dec 3 (some 2745) (some 2742), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,true,false,false] 3 (some 2745) (some 2742) 0 1 318 324 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2741_zero_checked PA211.UserCandidate.RuntimeShards.S055.s2741_positive_checked⟩

def e2742 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,true,false,true,false], .inc 1⟩, .inc 1 (some 2743), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,true,false,true,false] 1 (some 2743) 0 337 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2742_plain_checked⟩

def e2743 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,true,false,true,true,false], .inc 6⟩, .inc 6 (some 2744), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,true,false,true,true,false] 6 (some 2744) 0 364 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2743_plain_checked⟩

def e2744 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,true,false,true,true,true], .continueTo 3⟩, .jump (some 2741), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,true,false,true,true,true] (some 2741) 0 95 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2744_plain_checked⟩

def e2745 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,true,true,false], .dec 6⟩, .dec 6 (some 2748) (some 2746), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,true,true,false] 6 (some 2748) (some 2746) 0 1 324 324 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2745_zero_checked PA211.UserCandidate.RuntimeShards.S055.s2745_positive_checked⟩

def e2746 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,true,true,true,false], .inc 3⟩, .inc 3 (some 2747), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,true,true,true,false] 3 (some 2747) 0 328 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2746_plain_checked⟩

def e2747 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,true,true,true,true], .continueTo 2⟩, .jump (some 2745), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,false,true,true,true,true] (some 2745) 0 86 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2747_plain_checked⟩

def e2748 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,true,false,false,false,false,false,false], .dec 1⟩, .dec 1 (some 2751) (some 2749), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,true,false,false,false,false,false,false] 1 (some 2751) (some 2749) 0 1 345 351 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2748_zero_checked PA211.UserCandidate.RuntimeShards.S055.s2748_positive_checked⟩

def e2749 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,true,false,false,false,false,false,true,false], .inc 6⟩, .inc 6 (some 2750), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,true,false,false,false,false,false,true,false] 6 (some 2750) 0 364 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2749_plain_checked⟩

def e2750 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,true,false,false,false,false,false,true,true], .continueTo 2⟩, .jump (some 2748), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,true,false,false,false,false,false,true,true] (some 2748) 0 95 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2750_plain_checked⟩

def e2751 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,true,true,false,false,true,false,false,false,false,true,false,false], .dec 2⟩, .dec 2 (some 2754) (some 2752), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,true,true,false,false,true,false,false,false,false,true,false,false] 2 (some 2754) (some 2752) 0 1 366 372 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S055.s2751_zero_checked PA211.UserCandidate.RuntimeShards.S055.s2751_positive_checked⟩

def entries : Array (Entry PA211.UserCandidate.Source.path 3947) := #[
  e2688,
  e2689,
  e2690,
  e2691,
  e2692,
  e2693,
  e2694,
  e2695,
  e2696,
  e2697,
  e2698,
  e2699,
  e2700,
  e2701,
  e2702,
  e2703,
  e2704,
  e2705,
  e2706,
  e2707,
  e2708,
  e2709,
  e2710,
  e2711,
  e2712,
  e2713,
  e2714,
  e2715,
  e2716,
  e2717,
  e2718,
  e2719,
  e2720,
  e2721,
  e2722,
  e2723,
  e2724,
  e2725,
  e2726,
  e2727,
  e2728,
  e2729,
  e2730,
  e2731,
  e2732,
  e2733,
  e2734,
  e2735,
  e2736,
  e2737,
  e2738,
  e2739,
  e2740,
  e2741,
  e2742,
  e2743,
  e2744,
  e2745,
  e2746,
  e2747,
  e2748,
  e2749,
  e2750,
  e2751
]
theorem sites_block : entries.toList.map (·.site) =
 (PA211.UserCandidate.Source.sites.toList.drop 2688).take 64 := by decide +kernel
theorem codes_block : entries.toList.map (·.code) =
 (PA213.SourceProgram.codes.toList.drop 2688).take 64 := by decide +kernel
end PA211.UserCandidate.CoverageShards.S042
