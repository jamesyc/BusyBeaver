import User211SourceEquivalence
import PA211.UserCandidate.PrimitiveSimulation
import PA211.UserCandidate.RuntimeShards.S040
import PA211.UserCandidate.RuntimeShards.S041
set_option maxRecDepth 100000
set_option maxHeartbeats 32000000
namespace PA211.UserCandidate.CoverageShards.S031
open PA215.Source PA211.UserCandidate.PrimitiveSimulation
def e1984 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,false,false,true,true,false,true,true,false], .inc 6⟩, .inc 6 (some 1985), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,false,false,true,true,false,true,true,false] 6 (some 1985) 0 427 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1984_plain_checked⟩

def e1985 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,false,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 1983), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,false,false,true,true,false,true,true,true] (some 1983) 0 116 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1985_plain_checked⟩

def e1986 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,false,false,true,true,true], .continueTo 3⟩, .jump (some 1979), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,false,false,true,true,true] (some 1979) 0 107 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1986_plain_checked⟩

def e1987 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,false,true,false], .dec 7⟩, .dec 7 (some 1990) (some 1988), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,false,true,false] 7 (some 1990) (some 1988) 0 1 366 369 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1987_zero_checked PA211.UserCandidate.RuntimeShards.S040.s1987_positive_checked⟩

def e1988 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,false,true,true,false], .inc 2⟩, .inc 2 (some 1989), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,false,true,true,false] 2 (some 1989) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1988_plain_checked⟩

def e1989 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,false,true,true,true], .continueTo 2⟩, .jump (some 1987), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,false,true,true,true] (some 1987) 0 101 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1989_plain_checked⟩

def e1990 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,false,false,false], .dec 1⟩, .dec 1 (some 1994) (some 1991), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,false,false,false] 1 (some 1994) (some 1991) 0 1 363 369 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1990_zero_checked PA211.UserCandidate.RuntimeShards.S040.s1990_positive_checked⟩

def e1991 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,false,false,true,false], .inc 7⟩, .inc 7 (some 1992), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,false,false,true,false] 7 (some 1992) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1991_plain_checked⟩

def e1992 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,false,false,true,true,false], .inc 6⟩, .inc 6 (some 1993), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,false,false,true,true,false] 6 (some 1993) 0 409 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1992_plain_checked⟩

def e1993 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,false,false,true,true,true], .continueTo 3⟩, .jump (some 1990), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,false,false,true,true,true] (some 1990) 0 110 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1993_plain_checked⟩

def e1994 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,false,true,false], .dec 6⟩, .dec 6 (some 2000) (some 1995), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,false,true,false] 6 (some 2000) (some 1995) 0 1 384 387 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1994_zero_checked PA211.UserCandidate.RuntimeShards.S040.s1994_positive_checked⟩

def e1995 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,false,true,true,false,false], .inc 7⟩, .inc 7 (some 1996), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,false,true,true,false,false] 7 (some 1996) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1995_plain_checked⟩

def e1996 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 1999) (some 1997), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,false,true,true,false,true,false] 6 (some 1999) (some 1997) 0 1 402 405 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1996_zero_checked PA211.UserCandidate.RuntimeShards.S040.s1996_positive_checked⟩

def e1997 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,false,true,true,false,true,true,false], .inc 1⟩, .inc 1 (some 1998), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,false,true,true,false,true,true,false] 1 (some 1998) 0 400 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1997_plain_checked⟩

def e1998 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 1996), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,false,true,true,false,true,true,true] (some 1996) 0 110 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1998_plain_checked⟩

def e1999 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,false,true,true,true], .continueTo 3⟩, .jump (some 1990), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,false,true,true,true] (some 1990) 0 113 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s1999_plain_checked⟩

def e2000 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,true,false], .dec 7⟩, .dec 7 (some 2006) (some 2001), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,true,false] 7 (some 2006) (some 2001) 0 1 369 369 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s2000_zero_checked PA211.UserCandidate.RuntimeShards.S040.s2000_positive_checked⟩

def e2001 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,true,true,false,false,false], .inc 1⟩, .inc 1 (some 2002), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,true,true,false,false,false] 1 (some 2002) 0 382 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s2001_plain_checked⟩

def e2002 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,true,true,false,false,true], .inc 1⟩, .inc 1 (some 2003), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,true,true,false,false,true] 1 (some 2003) 0 385 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s2002_plain_checked⟩

def e2003 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,true,true,false,true,false], .inc 1⟩, .inc 1 (some 2004), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,true,true,false,true,false] 1 (some 2004) 0 391 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s2003_plain_checked⟩

def e2004 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,true,true,false,true,true], .inc 1⟩, .inc 1 (some 2005), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,true,true,false,true,true] 1 (some 2005) 0 397 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s2004_plain_checked⟩

def e2005 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,true,true,true], .continueTo 2⟩, .jump (some 2000), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,false,true,true,true,true] (some 2000) 0 98 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s2005_plain_checked⟩

def e2006 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,true], .inc 1⟩, .inc 1 (some 2007), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,false,true,true,true,true] 1 (some 2007) 0 349 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s2006_plain_checked⟩

def e2007 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,false,false,false], .dec 2⟩, .dec 2 (some 2015) (some 2008), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,false,false,false] 2 (some 2015) (some 2008) 0 1 375 381 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s2007_zero_checked PA211.UserCandidate.RuntimeShards.S040.s2007_positive_checked⟩

def e2008 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,false,false,true,false], .inc 7⟩, .inc 7 (some 2009), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,false,false,true,false] 7 (some 2009) 0 391 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s2008_plain_checked⟩

def e2009 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,false,false,true,true,false,false,false], .dec 6⟩, .dec 6 (some 2011) (some 2010), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,false,false,true,true,false,false,false] 6 (some 2011) (some 2010) 0 1 417 423 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s2009_zero_checked PA211.UserCandidate.RuntimeShards.S040.s2009_positive_checked⟩

def e2010 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,false,false,true,true,false,false,true], .breakTo 1⟩, .jump (some 2014), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,false,false,true,true,false,false,true] (some 2014) 0 116 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s2010_plain_checked⟩

def e2011 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,false,false,true,true,false,true,false], .dec 7⟩, .dec 7 (some 2014) (some 2012), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,false,false,true,true,false,true,false] 7 (some 2014) (some 2012) 0 1 429 432 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s2011_zero_checked PA211.UserCandidate.RuntimeShards.S040.s2011_positive_checked⟩

def e2012 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,false,false,true,true,false,true,true,false], .inc 6⟩, .inc 6 (some 2013), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,false,false,true,true,false,true,true,false] 6 (some 2013) 0 436 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s2012_plain_checked⟩

def e2013 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,false,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 2011), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,false,false,true,true,false,true,true,true] (some 2011) 0 119 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s2013_plain_checked⟩

def e2014 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,false,false,true,true,true], .continueTo 3⟩, .jump (some 2007), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,false,false,true,true,true] (some 2007) 0 110 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s2014_plain_checked⟩

def e2015 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,false,true,false], .dec 7⟩, .dec 7 (some 2018) (some 2016), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,false,true,false] 7 (some 2018) (some 2016) 0 1 375 378 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s2015_zero_checked PA211.UserCandidate.RuntimeShards.S040.s2015_positive_checked⟩

def e2016 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,false,true,true,false], .inc 2⟩, .inc 2 (some 2017), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,false,true,true,false] 2 (some 2017) 0 391 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s2016_plain_checked⟩

def e2017 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,false,true,true,true], .continueTo 2⟩, .jump (some 2015), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,false,true,true,true] (some 2015) 0 104 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s2017_plain_checked⟩

def e2018 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,false,false,false], .dec 1⟩, .dec 1 (some 2022) (some 2019), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,false,false,false] 1 (some 2022) (some 2019) 0 1 372 378 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S040.s2018_zero_checked PA211.UserCandidate.RuntimeShards.S040.s2018_positive_checked⟩

def e2019 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,false,false,true,false], .inc 7⟩, .inc 7 (some 2020), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,false,false,true,false] 7 (some 2020) 0 391 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2019_plain_checked⟩

def e2020 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,false,false,true,true,false], .inc 6⟩, .inc 6 (some 2021), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,false,false,true,true,false] 6 (some 2021) 0 418 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2020_plain_checked⟩

def e2021 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,false,false,true,true,true], .continueTo 3⟩, .jump (some 2018), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,false,false,true,true,true] (some 2018) 0 113 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2021_plain_checked⟩

def e2022 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,false,true,false], .dec 6⟩, .dec 6 (some 2028) (some 2023), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,false,true,false] 6 (some 2028) (some 2023) 0 1 393 396 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2022_zero_checked PA211.UserCandidate.RuntimeShards.S041.s2022_positive_checked⟩

def e2023 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,false,true,true,false,false], .inc 7⟩, .inc 7 (some 2024), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,false,true,true,false,false] 7 (some 2024) 0 391 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2023_plain_checked⟩

def e2024 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 2027) (some 2025), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,false,true,true,false,true,false] 6 (some 2027) (some 2025) 0 1 411 414 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2024_zero_checked PA211.UserCandidate.RuntimeShards.S041.s2024_positive_checked⟩

def e2025 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,false,true,true,false,true,true,false], .inc 1⟩, .inc 1 (some 2026), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,false,true,true,false,true,true,false] 1 (some 2026) 0 409 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2025_plain_checked⟩

def e2026 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 2024), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,false,true,true,false,true,true,true] (some 2024) 0 113 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2026_plain_checked⟩

def e2027 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,false,true,true,true], .continueTo 3⟩, .jump (some 2018), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,false,true,true,true] (some 2018) 0 116 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2027_plain_checked⟩

def e2028 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,true,false], .dec 7⟩, .dec 7 (some 2034) (some 2029), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,true,false] 7 (some 2034) (some 2029) 0 1 378 378 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2028_zero_checked PA211.UserCandidate.RuntimeShards.S041.s2028_positive_checked⟩

def e2029 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,true,true,false,false,false], .inc 1⟩, .inc 1 (some 2030), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,true,true,false,false,false] 1 (some 2030) 0 391 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2029_plain_checked⟩

def e2030 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,true,true,false,false,true], .inc 1⟩, .inc 1 (some 2031), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,true,true,false,false,true] 1 (some 2031) 0 394 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2030_plain_checked⟩

def e2031 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,true,true,false,true,false], .inc 1⟩, .inc 1 (some 2032), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,true,true,false,true,false] 1 (some 2032) 0 400 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2031_plain_checked⟩

def e2032 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,true,true,false,true,true], .inc 1⟩, .inc 1 (some 2033), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,true,true,false,true,true] 1 (some 2033) 0 406 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2032_plain_checked⟩

def e2033 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,true,true,true], .continueTo 2⟩, .jump (some 2028), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,false,true,true,true,true] (some 2028) 0 101 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2033_plain_checked⟩

def e2034 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,false,false,false], .dec 2⟩, .dec 2 (some 2042) (some 2035), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,false,false,false] 2 (some 2042) (some 2035) 0 1 384 390 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2034_zero_checked PA211.UserCandidate.RuntimeShards.S041.s2034_positive_checked⟩

def e2035 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,false,false,true,false], .inc 7⟩, .inc 7 (some 2036), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,false,false,true,false] 7 (some 2036) 0 400 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2035_plain_checked⟩

def e2036 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,false,false,true,true,false,false,false], .dec 6⟩, .dec 6 (some 2038) (some 2037), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,false,false,true,true,false,false,false] 6 (some 2038) (some 2037) 0 1 426 432 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2036_zero_checked PA211.UserCandidate.RuntimeShards.S041.s2036_positive_checked⟩

def e2037 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,false,false,true,true,false,false,true], .breakTo 1⟩, .jump (some 2041), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,false,false,true,true,false,false,true] (some 2041) 0 119 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2037_plain_checked⟩

def e2038 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,false,false,true,true,false,true,false], .dec 7⟩, .dec 7 (some 2041) (some 2039), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,false,false,true,true,false,true,false] 7 (some 2041) (some 2039) 0 1 438 441 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2038_zero_checked PA211.UserCandidate.RuntimeShards.S041.s2038_positive_checked⟩

def e2039 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,false,false,true,true,false,true,true,false], .inc 6⟩, .inc 6 (some 2040), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,false,false,true,true,false,true,true,false] 6 (some 2040) 0 445 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2039_plain_checked⟩

def e2040 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,false,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 2038), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,false,false,true,true,false,true,true,true] (some 2038) 0 122 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2040_plain_checked⟩

def e2041 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,false,false,true,true,true], .continueTo 3⟩, .jump (some 2034), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,false,false,true,true,true] (some 2034) 0 113 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2041_plain_checked⟩

def e2042 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,false,true,false], .dec 7⟩, .dec 7 (some 2045) (some 2043), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,false,true,false] 7 (some 2045) (some 2043) 0 1 384 387 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2042_zero_checked PA211.UserCandidate.RuntimeShards.S041.s2042_positive_checked⟩

def e2043 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,false,true,true,false], .inc 2⟩, .inc 2 (some 2044), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,false,true,true,false] 2 (some 2044) 0 400 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2043_plain_checked⟩

def e2044 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,false,true,true,true], .continueTo 2⟩, .jump (some 2042), implements_jump PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,false,true,true,true] (some 2042) 0 107 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2044_plain_checked⟩

def e2045 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,true,false,false,false], .dec 1⟩, .dec 1 (some 2049) (some 2046), implements_dec PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,true,false,false,false] 1 (some 2049) (some 2046) 0 1 381 387 (by decide) (by decide) (PA211.UserCandidate.Source.path_short _) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2045_zero_checked PA211.UserCandidate.RuntimeShards.S041.s2045_positive_checked⟩

def e2046 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,true,false,false,true,false], .inc 7⟩, .inc 7 (some 2047), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,true,false,false,true,false] 7 (some 2047) 0 400 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2046_plain_checked⟩

def e2047 : Entry PA211.UserCandidate.Source.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,true,false,false,true,true,false], .inc 6⟩, .inc 6 (some 2048), implements_inc PA211.UserCandidate.Source.path 3947 [true,false,true,false,false,true,true,true,true,false,false,false,false,true,true,false,false,true,true,false,false,true,true,false] 6 (some 2048) 0 427 (by decide) (PA211.UserCandidate.Source.path_short _) PA211.UserCandidate.RuntimeShards.S041.s2047_plain_checked⟩

def entries : Array (Entry PA211.UserCandidate.Source.path 3947) := #[
  e1984,
  e1985,
  e1986,
  e1987,
  e1988,
  e1989,
  e1990,
  e1991,
  e1992,
  e1993,
  e1994,
  e1995,
  e1996,
  e1997,
  e1998,
  e1999,
  e2000,
  e2001,
  e2002,
  e2003,
  e2004,
  e2005,
  e2006,
  e2007,
  e2008,
  e2009,
  e2010,
  e2011,
  e2012,
  e2013,
  e2014,
  e2015,
  e2016,
  e2017,
  e2018,
  e2019,
  e2020,
  e2021,
  e2022,
  e2023,
  e2024,
  e2025,
  e2026,
  e2027,
  e2028,
  e2029,
  e2030,
  e2031,
  e2032,
  e2033,
  e2034,
  e2035,
  e2036,
  e2037,
  e2038,
  e2039,
  e2040,
  e2041,
  e2042,
  e2043,
  e2044,
  e2045,
  e2046,
  e2047
]
theorem sites_block : entries.toList.map (·.site) =
 (PA211.UserCandidate.Source.sites.toList.drop 1984).take 64 := by decide +kernel
theorem codes_block : entries.toList.map (·.code) =
 (PA213.SourceProgram.codes.toList.drop 1984).take 64 := by decide +kernel
end PA211.UserCandidate.CoverageShards.S031
