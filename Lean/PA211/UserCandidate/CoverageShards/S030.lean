module

public import User211SourceEquivalence
public import PA211.UserCandidate.PrimitiveSimulation
public import PA211.UserCandidate.RuntimeShards.S038
public import PA211.UserCandidate.RuntimeShards.S039
public import PA211.UserCandidate.RuntimeShards.S040

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 32000000
namespace PA211.UserCandidate.CoverageShards.S030
open PA215.Source PA211.UserCandidate.PrimitiveSimulation
def e1920 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,false,true,false,true,true,false], .dec 7⟩, .dec 7 (some 1926) (some 1921), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,false,true,false,true,true,false] 7 (some 1926) (some 1921) 0 1 369 369 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S038.s1920_zero_checked PA211.UserCandidate.RuntimeShards.S039.s1920_positive_checked⟩

def e1921 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,false,true,false,true,true,true,false,false,false], .inc 1⟩, .inc 1 (some 1922), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,false,true,false,true,true,true,false,false,false] 1 (some 1922) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1921_plain_checked⟩

def e1922 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,false,true,false,true,true,true,false,false,true], .inc 1⟩, .inc 1 (some 1923), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,false,true,false,true,true,true,false,false,true] 1 (some 1923) 0 385 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1922_plain_checked⟩

def e1923 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,false,true,false,true,true,true,false,true,false], .inc 1⟩, .inc 1 (some 1924), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,false,true,false,true,true,true,false,true,false] 1 (some 1924) 0 391 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1923_plain_checked⟩

def e1924 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,false,true,false,true,true,true,false,true,true], .inc 1⟩, .inc 1 (some 1925), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,false,true,false,true,true,true,false,true,true] 1 (some 1925) 0 397 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1924_plain_checked⟩

def e1925 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,false,true,false,true,true,true,true], .continueTo 2⟩, .jump (some 1920), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,false,true,false,true,true,true,true] (some 1920) 0 98 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1925_plain_checked⟩

def e1926 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,false,true,true], .inc 1⟩, .inc 1 (some 1927), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,false,true,true] 1 (some 1927) 0 343 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1926_plain_checked⟩

def e1927 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,false,false], .dec 1⟩, .dec 1 (some 1930) (some 1928), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,false,false] 1 (some 1930) (some 1928) 0 1 354 360 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1927_zero_checked PA211.UserCandidate.RuntimeShards.S039.s1927_positive_checked⟩

def e1928 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,false,true,false], .inc 6⟩, .inc 6 (some 1929), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,false,true,false] 6 (some 1929) 0 373 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1928_plain_checked⟩

def e1929 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,false,true,true], .continueTo 2⟩, .jump (some 1927), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,false,true,true] (some 1927) 0 98 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1929_plain_checked⟩

def e1930 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,false,false], .dec 2⟩, .dec 2 (some 1933) (some 1931), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,false,false] 2 (some 1933) (some 1931) 0 1 375 381 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1930_zero_checked PA211.UserCandidate.RuntimeShards.S039.s1930_positive_checked⟩

def e1931 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,false,true,false], .inc 1⟩, .inc 1 (some 1932), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,false,true,false] 1 (some 1932) 0 373 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1931_plain_checked⟩

def e1932 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,false,true,true], .continueTo 2⟩, .jump (some 1930), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,false,true,true] (some 1930) 0 101 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1932_plain_checked⟩

def e1933 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,true,false,false,false], .dec 1⟩, .dec 1 (some 1937) (some 1934), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,true,false,false,false] 1 (some 1937) (some 1934) 0 1 381 387 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1933_zero_checked PA211.UserCandidate.RuntimeShards.S039.s1933_positive_checked⟩

def e1934 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,true,false,false,true,false], .inc 7⟩, .inc 7 (some 1935), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,true,false,false,true,false] 7 (some 1935) 0 400 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1934_plain_checked⟩

def e1935 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,true,false,false,true,true,false], .inc 6⟩, .inc 6 (some 1936), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,true,false,false,true,true,false] 6 (some 1936) 0 427 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1935_plain_checked⟩

def e1936 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,true,false,false,true,true,true], .continueTo 3⟩, .jump (some 1933), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,true,false,false,true,true,true] (some 1933) 0 116 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1936_plain_checked⟩

def e1937 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 1943) (some 1938), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,true,false,true,false] 6 (some 1943) (some 1938) 0 1 402 405 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1937_zero_checked PA211.UserCandidate.RuntimeShards.S039.s1937_positive_checked⟩

def e1938 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,true,false,true,true,false,false], .inc 7⟩, .inc 7 (some 1939), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,true,false,true,true,false,false] 7 (some 1939) 0 400 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1938_plain_checked⟩

def e1939 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,true,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 1942) (some 1940), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,true,false,true,true,false,true,false] 6 (some 1942) (some 1940) 0 1 420 423 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1939_zero_checked PA211.UserCandidate.RuntimeShards.S039.s1939_positive_checked⟩

def e1940 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,true,false,true,true,false,true,true,false], .inc 1⟩, .inc 1 (some 1941), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,true,false,true,true,false,true,true,false] 1 (some 1941) 0 418 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1940_plain_checked⟩

def e1941 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,true,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 1939), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,true,false,true,true,false,true,true,true] (some 1939) 0 116 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1941_plain_checked⟩

def e1942 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,true,false,true,true,true], .continueTo 3⟩, .jump (some 1933), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,true,false,true,true,true] (some 1933) 0 119 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1942_plain_checked⟩

def e1943 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,true,true,false], .dec 7⟩, .dec 7 (some 1946) (some 1944), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,true,true,false] 7 (some 1946) (some 1944) 0 1 390 387 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1943_zero_checked PA211.UserCandidate.RuntimeShards.S039.s1943_positive_checked⟩

def e1944 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,true,true,true,false], .inc 2⟩, .inc 2 (some 1945), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,true,true,true,false] 2 (some 1945) 0 400 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1944_plain_checked⟩

def e1945 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,true,true,true,true], .continueTo 2⟩, .jump (some 1943), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,false,true,true,true,true,true] (some 1943) 0 107 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1945_plain_checked⟩

def e1946 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,true,false,false], .dec 3⟩, .dec 3 (some 1950) (some 1947), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,true,false,false] 3 (some 1950) (some 1947) 0 1 354 360 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1946_zero_checked PA211.UserCandidate.RuntimeShards.S039.s1946_positive_checked⟩

def e1947 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,true,false,true,false], .inc 1⟩, .inc 1 (some 1948), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,true,false,true,false] 1 (some 1948) 0 373 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1947_plain_checked⟩

def e1948 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,true,false,true,true,false], .inc 6⟩, .inc 6 (some 1949), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,true,false,true,true,false] 6 (some 1949) 0 400 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1948_plain_checked⟩

def e1949 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,true,false,true,true,true], .continueTo 3⟩, .jump (some 1946), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,true,false,true,true,true] (some 1946) 0 107 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1949_plain_checked⟩

def e1950 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,true,true,false], .dec 6⟩, .dec 6 (some 1953) (some 1951), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,true,true,false] 6 (some 1953) (some 1951) 0 1 360 360 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1950_zero_checked PA211.UserCandidate.RuntimeShards.S039.s1950_positive_checked⟩

def e1951 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,true,true,true,false], .inc 3⟩, .inc 3 (some 1952), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,true,true,true,false] 3 (some 1952) 0 364 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1951_plain_checked⟩

def e1952 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,true,true,true,true], .continueTo 2⟩, .jump (some 1950), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,false,true,true,true,true] (some 1950) 0 98 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1952_plain_checked⟩

def e1953 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,false,false], .dec 1⟩, .dec 1 (some 1956) (some 1954), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,false,false] 1 (some 1956) (some 1954) 0 1 354 360 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1953_zero_checked PA211.UserCandidate.RuntimeShards.S039.s1953_positive_checked⟩

def e1954 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,false,true,false], .inc 6⟩, .inc 6 (some 1955), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,false,true,false] 6 (some 1955) 0 373 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1954_plain_checked⟩

def e1955 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,false,true,true], .continueTo 2⟩, .jump (some 1953), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,false,true,true] (some 1953) 0 98 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1955_plain_checked⟩

def e1956 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,false,false], .dec 2⟩, .dec 2 (some 1959) (some 1957), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,false,false] 2 (some 1959) (some 1957) 0 1 375 381 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1956_zero_checked PA211.UserCandidate.RuntimeShards.S039.s1956_positive_checked⟩

def e1957 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,false,true,false], .inc 1⟩, .inc 1 (some 1958), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,false,true,false] 1 (some 1958) 0 373 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1957_plain_checked⟩

def e1958 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,false,true,true], .continueTo 2⟩, .jump (some 1956), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,false,true,true] (some 1956) 0 101 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1958_plain_checked⟩

def e1959 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,true,false,false,false], .dec 1⟩, .dec 1 (some 1963) (some 1960), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,true,false,false,false] 1 (some 1963) (some 1960) 0 1 381 387 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1959_zero_checked PA211.UserCandidate.RuntimeShards.S039.s1959_positive_checked⟩

def e1960 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,true,false,false,true,false], .inc 7⟩, .inc 7 (some 1961), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,true,false,false,true,false] 7 (some 1961) 0 400 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1960_plain_checked⟩

def e1961 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,true,false,false,true,true,false], .inc 6⟩, .inc 6 (some 1962), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,true,false,false,true,true,false] 6 (some 1962) 0 427 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1961_plain_checked⟩

def e1962 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,true,false,false,true,true,true], .continueTo 3⟩, .jump (some 1959), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,true,false,false,true,true,true] (some 1959) 0 116 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1962_plain_checked⟩

def e1963 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 1969) (some 1964), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,true,false,true,false] 6 (some 1969) (some 1964) 0 1 402 405 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1963_zero_checked PA211.UserCandidate.RuntimeShards.S039.s1963_positive_checked⟩

def e1964 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,true,false,true,true,false,false], .inc 7⟩, .inc 7 (some 1965), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,true,false,true,true,false,false] 7 (some 1965) 0 400 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1964_plain_checked⟩

def e1965 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,true,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 1968) (some 1966), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,true,false,true,true,false,true,false] 6 (some 1968) (some 1966) 0 1 420 423 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1965_zero_checked PA211.UserCandidate.RuntimeShards.S039.s1965_positive_checked⟩

def e1966 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,true,false,true,true,false,true,true,false], .inc 1⟩, .inc 1 (some 1967), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,true,false,true,true,false,true,true,false] 1 (some 1967) 0 418 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1966_plain_checked⟩

def e1967 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,true,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 1965), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,true,false,true,true,false,true,true,true] (some 1965) 0 116 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1967_plain_checked⟩

def e1968 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,true,false,true,true,true], .continueTo 3⟩, .jump (some 1959), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,true,false,true,true,true] (some 1959) 0 119 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1968_plain_checked⟩

def e1969 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,true,true,false], .dec 7⟩, .dec 7 (some 1972) (some 1970), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,true,true,false] 7 (some 1972) (some 1970) 0 1 390 387 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S039.s1969_zero_checked PA211.UserCandidate.RuntimeShards.S039.s1969_positive_checked⟩

def e1970 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,true,true,true,false], .inc 2⟩, .inc 2 (some 1971), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,true,true,true,false] 2 (some 1971) 0 400 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1970_plain_checked⟩

def e1971 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,true,true,true,true], .continueTo 2⟩, .jump (some 1969), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,false,true,true,true,true,true] (some 1969) 0 107 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1971_plain_checked⟩

def e1972 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,true,false,false], .dec 5⟩, .dec 5 (some 1976) (some 1973), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,true,false,false] 5 (some 1976) (some 1973) 0 1 354 360 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1972_zero_checked PA211.UserCandidate.RuntimeShards.S040.s1972_positive_checked⟩

def e1973 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,true,false,true,false], .inc 1⟩, .inc 1 (some 1974), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,true,false,true,false] 1 (some 1974) 0 364 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1973_plain_checked⟩

def e1974 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,true,false,true,true,false], .inc 6⟩, .inc 6 (some 1975), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,true,false,true,true,false] 6 (some 1975) 0 391 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1974_plain_checked⟩

def e1975 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,true,false,true,true,true], .continueTo 3⟩, .jump (some 1972), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,true,false,true,true,true] (some 1972) 0 104 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1975_plain_checked⟩

def e1976 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,true,true,false], .dec 6⟩, .dec 6 (some 1979) (some 1977), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,true,true,false] 6 (some 1979) (some 1977) 0 1 363 360 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1976_zero_checked PA211.UserCandidate.RuntimeShards.S040.s1976_positive_checked⟩

def e1977 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,true,true,true,false], .inc 5⟩, .inc 5 (some 1978), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,true,true,true,false] 5 (some 1978) 0 391 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1977_plain_checked⟩

def e1978 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,true,true,true,true], .continueTo 2⟩, .jump (some 1976), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,false,true,true,true,true,true] (some 1976) 0 98 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1978_plain_checked⟩

def e1979 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,false,false,false], .dec 2⟩, .dec 2 (some 1987) (some 1980), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,false,false,false] 2 (some 1987) (some 1980) 0 1 366 372 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1979_zero_checked PA211.UserCandidate.RuntimeShards.S040.s1979_positive_checked⟩

def e1980 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,false,false,true,false], .inc 7⟩, .inc 7 (some 1981), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,false,false,true,false] 7 (some 1981) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1980_plain_checked⟩

def e1981 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,false,false,true,true,false,false,false], .dec 6⟩, .dec 6 (some 1983) (some 1982), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,false,false,true,true,false,false,false] 6 (some 1983) (some 1982) 0 1 408 414 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1981_zero_checked PA211.UserCandidate.RuntimeShards.S040.s1981_positive_checked⟩

def e1982 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,false,false,true,true,false,false,true], .breakTo 1⟩, .jump (some 1986), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,false,false,true,true,false,false,true] (some 1986) 0 113 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1982_plain_checked⟩

def e1983 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,false,false,true,true,false,true,false], .dec 7⟩, .dec 7 (some 1986) (some 1984), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,false,false,true,true,false,true,false] 7 (some 1986) (some 1984) 0 1 420 423 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1983_zero_checked PA211.UserCandidate.RuntimeShards.S040.s1983_positive_checked⟩

def entries : Array (Entry PA211.UserCandidate.Source.path 3947) := #[
  e1920,
  e1921,
  e1922,
  e1923,
  e1924,
  e1925,
  e1926,
  e1927,
  e1928,
  e1929,
  e1930,
  e1931,
  e1932,
  e1933,
  e1934,
  e1935,
  e1936,
  e1937,
  e1938,
  e1939,
  e1940,
  e1941,
  e1942,
  e1943,
  e1944,
  e1945,
  e1946,
  e1947,
  e1948,
  e1949,
  e1950,
  e1951,
  e1952,
  e1953,
  e1954,
  e1955,
  e1956,
  e1957,
  e1958,
  e1959,
  e1960,
  e1961,
  e1962,
  e1963,
  e1964,
  e1965,
  e1966,
  e1967,
  e1968,
  e1969,
  e1970,
  e1971,
  e1972,
  e1973,
  e1974,
  e1975,
  e1976,
  e1977,
  e1978,
  e1979,
  e1980,
  e1981,
  e1982,
  e1983
]
theorem sites_block : entries.toList.map (·.site) =
 (PA211.UserCandidate.Source.sites.toList.drop 1920).take 64 := by decide +kernel
theorem codes_block : entries.toList.map (·.code) =
 (PA213.SourceProgram.codes.toList.drop 1920).take 64 := by decide +kernel
end PA211.UserCandidate.CoverageShards.S030
