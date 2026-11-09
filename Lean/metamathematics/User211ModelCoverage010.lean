import User211SourceEquivalence
import User211PAModelPrimitive
import PA211.UserCandidate.RuntimeShards.S013
import PA211.UserCandidate.RuntimeShards.S014
set_option maxRecDepth 100000
set_option maxHeartbeats 32000000
namespace PA211.UserCandidate.PA.ModelCoverageShards.S010
open PA215.Source PA211.UserCandidate.PA.ModelPrimitive
def e0640 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,false,false], .inc 1⟩, .inc 1 (some 641), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,false,false] 1 (some 641) 0 274 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0640_plain_checked⟩

def e0641 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,false,true], .inc 1⟩, .inc 1 (some 642), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,false,true] 1 (some 642) 0 277 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0641_plain_checked⟩

def e0642 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,false,false], .dec 1⟩, .dec 1 (some 645) (some 643), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,false,false] 1 (some 645) (some 643) 0 1 336 342 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0642_zero_checked PA211.UserCandidate.RuntimeShards.S013.s0642_positive_checked⟩

def e0643 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,false,true,false], .inc 6⟩, .inc 6 (some 644), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,false,true,false] 6 (some 644) 0 355 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0643_plain_checked⟩

def e0644 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,false,true,true], .continueTo 2⟩, .jump (some 642), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,false,true,true] (some 642) 0 92 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0644_plain_checked⟩

def e0645 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,false,false], .dec 2⟩, .dec 2 (some 648) (some 646), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,false,false] 2 (some 648) (some 646) 0 1 357 363 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0645_zero_checked PA211.UserCandidate.RuntimeShards.S013.s0645_positive_checked⟩

def e0646 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,false,true,false], .inc 1⟩, .inc 1 (some 647), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,false,true,false] 1 (some 647) 0 355 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0646_plain_checked⟩

def e0647 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,false,true,true], .continueTo 2⟩, .jump (some 645), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,false,true,true] (some 645) 0 95 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0647_plain_checked⟩

def e0648 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,true,false,false,false], .dec 1⟩, .dec 1 (some 652) (some 649), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,true,false,false,false] 1 (some 652) (some 649) 0 1 363 369 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0648_zero_checked PA211.UserCandidate.RuntimeShards.S013.s0648_positive_checked⟩

def e0649 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,true,false,false,true,false], .inc 7⟩, .inc 7 (some 650), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,true,false,false,true,false] 7 (some 650) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0649_plain_checked⟩

def e0650 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,true,false,false,true,true,false], .inc 6⟩, .inc 6 (some 651), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,true,false,false,true,true,false] 6 (some 651) 0 409 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0650_plain_checked⟩

def e0651 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,true,false,false,true,true,true], .continueTo 3⟩, .jump (some 648), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,true,false,false,true,true,true] (some 648) 0 110 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0651_plain_checked⟩

def e0652 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 658) (some 653), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,true,false,true,false] 6 (some 658) (some 653) 0 1 384 387 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0652_zero_checked PA211.UserCandidate.RuntimeShards.S013.s0652_positive_checked⟩

def e0653 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,true,false,true,true,false,false], .inc 7⟩, .inc 7 (some 654), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,true,false,true,true,false,false] 7 (some 654) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0653_plain_checked⟩

def e0654 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,true,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 657) (some 655), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,true,false,true,true,false,true,false] 6 (some 657) (some 655) 0 1 402 405 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0654_zero_checked PA211.UserCandidate.RuntimeShards.S013.s0654_positive_checked⟩

def e0655 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,true,false,true,true,false,true,true,false], .inc 1⟩, .inc 1 (some 656), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,true,false,true,true,false,true,true,false] 1 (some 656) 0 400 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0655_plain_checked⟩

def e0656 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,true,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 654), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,true,false,true,true,false,true,true,true] (some 654) 0 110 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0656_plain_checked⟩

def e0657 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,true,false,true,true,true], .continueTo 3⟩, .jump (some 648), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,true,false,true,true,true] (some 648) 0 113 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0657_plain_checked⟩

def e0658 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,true,true,false], .dec 7⟩, .dec 7 (some 661) (some 659), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,true,true,false] 7 (some 661) (some 659) 0 1 372 369 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0658_zero_checked PA211.UserCandidate.RuntimeShards.S013.s0658_positive_checked⟩

def e0659 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,true,true,true,false], .inc 2⟩, .inc 2 (some 660), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,true,true,true,false] 2 (some 660) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0659_plain_checked⟩

def e0660 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,true,true,true,true], .continueTo 2⟩, .jump (some 658), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,false,true,true,true,true,true] (some 658) 0 101 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0660_plain_checked⟩

def e0661 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,true,false,false], .dec 4⟩, .dec 4 (some 665) (some 662), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,true,false,false] 4 (some 665) (some 662) 0 1 336 342 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0661_zero_checked PA211.UserCandidate.RuntimeShards.S013.s0661_positive_checked⟩

def e0662 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,true,false,true,false], .inc 1⟩, .inc 1 (some 663), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,true,false,true,false] 1 (some 663) 0 355 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0662_plain_checked⟩

def e0663 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,true,false,true,true,false], .inc 6⟩, .inc 6 (some 664), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,true,false,true,true,false] 6 (some 664) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0663_plain_checked⟩

def e0664 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,true,false,true,true,true], .continueTo 3⟩, .jump (some 661), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,true,false,true,true,true] (some 661) 0 101 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0664_plain_checked⟩

def e0665 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,true,true,false], .dec 6⟩, .dec 6 (some 668) (some 666), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,true,true,false] 6 (some 668) (some 666) 0 1 342 342 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0665_zero_checked PA211.UserCandidate.RuntimeShards.S013.s0665_positive_checked⟩

def e0666 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,true,true,true,false], .inc 4⟩, .inc 4 (some 667), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,true,true,true,false] 4 (some 667) 0 358 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0666_plain_checked⟩

def e0667 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,true,true,true,true], .continueTo 2⟩, .jump (some 665), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,false,true,true,true,true] (some 665) 0 92 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0667_plain_checked⟩

def e0668 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,false,false], .dec 1⟩, .dec 1 (some 671) (some 669), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,false,false] 1 (some 671) (some 669) 0 1 336 342 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0668_zero_checked PA211.UserCandidate.RuntimeShards.S013.s0668_positive_checked⟩

def e0669 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,false,true,false], .inc 6⟩, .inc 6 (some 670), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,false,true,false] 6 (some 670) 0 355 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0669_plain_checked⟩

def e0670 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,false,true,true], .continueTo 2⟩, .jump (some 668), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,false,true,true] (some 668) 0 92 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0670_plain_checked⟩

def e0671 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,false,false], .dec 2⟩, .dec 2 (some 674) (some 672), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,false,false] 2 (some 674) (some 672) 0 1 357 363 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0671_zero_checked PA211.UserCandidate.RuntimeShards.S013.s0671_positive_checked⟩

def e0672 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,false,true,false], .inc 1⟩, .inc 1 (some 673), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,false,true,false] 1 (some 673) 0 355 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0672_plain_checked⟩

def e0673 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,false,true,true], .continueTo 2⟩, .jump (some 671), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,false,true,true] (some 671) 0 95 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0673_plain_checked⟩

def e0674 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,true,false,false,false], .dec 1⟩, .dec 1 (some 678) (some 675), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,true,false,false,false] 1 (some 678) (some 675) 0 1 363 369 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0674_zero_checked PA211.UserCandidate.RuntimeShards.S013.s0674_positive_checked⟩

def e0675 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,true,false,false,true,false], .inc 7⟩, .inc 7 (some 676), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,true,false,false,true,false] 7 (some 676) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0675_plain_checked⟩

def e0676 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,true,false,false,true,true,false], .inc 6⟩, .inc 6 (some 677), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,true,false,false,true,true,false] 6 (some 677) 0 409 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0676_plain_checked⟩

def e0677 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,true,false,false,true,true,true], .continueTo 3⟩, .jump (some 674), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,true,false,false,true,true,true] (some 674) 0 110 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0677_plain_checked⟩

def e0678 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 684) (some 679), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,true,false,true,false] 6 (some 684) (some 679) 0 1 384 387 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0678_zero_checked PA211.UserCandidate.RuntimeShards.S013.s0678_positive_checked⟩

def e0679 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,true,false,true,true,false,false], .inc 7⟩, .inc 7 (some 680), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,true,false,true,true,false,false] 7 (some 680) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0679_plain_checked⟩

def e0680 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,true,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 683) (some 681), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,true,false,true,true,false,true,false] 6 (some 683) (some 681) 0 1 402 405 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0680_zero_checked PA211.UserCandidate.RuntimeShards.S013.s0680_positive_checked⟩

def e0681 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,true,false,true,true,false,true,true,false], .inc 1⟩, .inc 1 (some 682), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,true,false,true,true,false,true,true,false] 1 (some 682) 0 400 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0681_plain_checked⟩

def e0682 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,true,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 680), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,true,false,true,true,false,true,true,true] (some 680) 0 110 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0682_plain_checked⟩

def e0683 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,true,false,true,true,true], .continueTo 3⟩, .jump (some 674), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,true,false,true,true,true] (some 674) 0 113 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0683_plain_checked⟩

def e0684 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,true,true,false], .dec 7⟩, .dec 7 (some 687) (some 685), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,true,true,false] 7 (some 687) (some 685) 0 1 372 369 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0684_zero_checked PA211.UserCandidate.RuntimeShards.S013.s0684_positive_checked⟩

def e0685 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,true,true,true,false], .inc 2⟩, .inc 2 (some 686), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,true,true,true,false] 2 (some 686) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S013.s0685_plain_checked⟩

def e0686 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,true,true,true,true], .continueTo 2⟩, .jump (some 684), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,false,true,true,true,true,true] (some 684) 0 101 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S014.s0686_plain_checked⟩

def e0687 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,true,false,false], .dec 5⟩, .dec 5 (some 691) (some 688), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,true,false,false] 5 (some 691) (some 688) 0 1 336 342 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S014.s0687_zero_checked PA211.UserCandidate.RuntimeShards.S014.s0687_positive_checked⟩

def e0688 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,true,false,true,false], .inc 1⟩, .inc 1 (some 689), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,true,false,true,false] 1 (some 689) 0 346 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S014.s0688_plain_checked⟩

def e0689 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,true,false,true,true,false], .inc 6⟩, .inc 6 (some 690), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,true,false,true,true,false] 6 (some 690) 0 373 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S014.s0689_plain_checked⟩

def e0690 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,true,false,true,true,true], .continueTo 3⟩, .jump (some 687), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,true,false,true,true,true] (some 687) 0 98 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S014.s0690_plain_checked⟩

def e0691 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,true,true,false], .dec 6⟩, .dec 6 (some 694) (some 692), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,true,true,false] 6 (some 694) (some 692) 0 1 345 342 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S014.s0691_zero_checked PA211.UserCandidate.RuntimeShards.S014.s0691_positive_checked⟩

def e0692 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,true,true,true,false], .inc 5⟩, .inc 5 (some 693), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,true,true,true,false] 5 (some 693) 0 373 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S014.s0692_plain_checked⟩

def e0693 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,true,true,true,true], .continueTo 2⟩, .jump (some 691), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,false,true,true,true,true,true] (some 691) 0 92 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S014.s0693_plain_checked⟩

def e0694 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,true,false,false,false,false], .dec 2⟩, .dec 2 (some 702) (some 695), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,true,false,false,false,false] 2 (some 702) (some 695) 0 1 348 354 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S014.s0694_zero_checked PA211.UserCandidate.RuntimeShards.S014.s0694_positive_checked⟩

def e0695 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,true,false,false,false,true,false], .inc 7⟩, .inc 7 (some 696), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,true,false,false,false,true,false] 7 (some 696) 0 364 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S014.s0695_plain_checked⟩

def e0696 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,true,false,false,false,true,true,false,false,false], .dec 6⟩, .dec 6 (some 698) (some 697), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,true,false,false,false,true,true,false,false,false] 6 (some 698) (some 697) 0 1 390 396 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S014.s0696_zero_checked PA211.UserCandidate.RuntimeShards.S014.s0696_positive_checked⟩

def e0697 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,true,false,false,false,true,true,false,false,true], .breakTo 1⟩, .jump (some 701), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,true,false,false,false,true,true,false,false,true] (some 701) 0 107 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S014.s0697_plain_checked⟩

def e0698 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,true,false,false,false,true,true,false,true,false], .dec 7⟩, .dec 7 (some 701) (some 699), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,true,false,false,false,true,true,false,true,false] 7 (some 701) (some 699) 0 1 402 405 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S014.s0698_zero_checked PA211.UserCandidate.RuntimeShards.S014.s0698_positive_checked⟩

def e0699 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,true,false,false,false,true,true,false,true,true,false], .inc 6⟩, .inc 6 (some 700), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,true,false,false,false,true,true,false,true,true,false] 6 (some 700) 0 409 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S014.s0699_plain_checked⟩

def e0700 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,true,false,false,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 698), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,true,false,false,false,true,true,false,true,true,true] (some 698) 0 110 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S014.s0700_plain_checked⟩

def e0701 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,true,false,false,false,true,true,true], .continueTo 3⟩, .jump (some 694), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,true,false,false,false,true,true,true] (some 694) 0 101 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S014.s0701_plain_checked⟩

def e0702 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,true,false,false,true,false], .dec 7⟩, .dec 7 (some 705) (some 703), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,true,false,false,true,false] 7 (some 705) (some 703) 0 1 348 351 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S014.s0702_zero_checked PA211.UserCandidate.RuntimeShards.S014.s0702_positive_checked⟩

def e0703 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,false,false,true,false,true,false,false,true,true,false], .inc 2⟩, .inc 2 (some 704), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,false,false,false,true,false,true,false,false,true,true,false] 2 (some 704) 0 364 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S014.s0703_plain_checked⟩

def entries : Array (Entry PA211.UserCandidate.Source.path 3947) := #[
  e0640,
  e0641,
  e0642,
  e0643,
  e0644,
  e0645,
  e0646,
  e0647,
  e0648,
  e0649,
  e0650,
  e0651,
  e0652,
  e0653,
  e0654,
  e0655,
  e0656,
  e0657,
  e0658,
  e0659,
  e0660,
  e0661,
  e0662,
  e0663,
  e0664,
  e0665,
  e0666,
  e0667,
  e0668,
  e0669,
  e0670,
  e0671,
  e0672,
  e0673,
  e0674,
  e0675,
  e0676,
  e0677,
  e0678,
  e0679,
  e0680,
  e0681,
  e0682,
  e0683,
  e0684,
  e0685,
  e0686,
  e0687,
  e0688,
  e0689,
  e0690,
  e0691,
  e0692,
  e0693,
  e0694,
  e0695,
  e0696,
  e0697,
  e0698,
  e0699,
  e0700,
  e0701,
  e0702,
  e0703
]
theorem sites_block : entries.toList.map (·.site) =
 (PA211.UserCandidate.Source.sites.toList.drop 640).take 64 := by decide +kernel
theorem codes_block : entries.toList.map (·.code) =
 (PA213.SourceProgram.codes.toList.drop 640).take 64 := by decide +kernel
end PA211.UserCandidate.PA.ModelCoverageShards.S010
