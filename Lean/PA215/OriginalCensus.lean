import PA215.Census.C000
import PA215.Census.C001
import PA215.Census.C002
import PA215.Census.C003
import PA215.Census.C004
import PA215.Census.C005
import PA215.Census.C006
import PA215.Census.C007
import PA215.Census.C008
import PA215.Census.C009
import PA215.Census.C010
import PA215.Census.C011
import PA215.Census.C012
import PA215.Census.C013
import PA215.Census.C014
import PA215.Census.C015
import PA215.Census.C016
import PA215.Census.C017
import PA215.Census.C018
import PA215.Census.C019
import PA215.Census.C020
import PA215.Census.C021
import PA215.Census.C022
import PA215.Census.C023
import PA215.Census.C024
import PA215.Census.C025
import PA215.Census.C026
import PA215.Census.C027
import PA215.Census.C028
import PA215.Census.C029
import PA215.Census.C030
import PA215.Census.C031
import PA215.Census.C032
import PA215.Census.C033
import PA215.Census.C034
import PA215.Census.C035
import PA215.Census.C036
import PA215.Census.C037
import PA215.Census.C038
import PA215.Census.C039
import PA215.Census.C040

namespace PA215.Census

def all : Array RawOriginal :=
  C000.records ++
  C001.records ++
  C002.records ++
  C003.records ++
  C004.records ++
  C005.records ++
  C006.records ++
  C007.records ++
  C008.records ++
  C009.records ++
  C010.records ++
  C011.records ++
  C012.records ++
  C013.records ++
  C014.records ++
  C015.records ++
  C016.records ++
  C017.records ++
  C018.records ++
  C019.records ++
  C020.records ++
  C021.records ++
  C022.records ++
  C023.records ++
  C024.records ++
  C025.records ++
  C026.records ++
  C027.records ++
  C028.records ++
  C029.records ++
  C030.records ++
  C031.records ++
  C032.records ++
  C033.records ++
  C034.records ++
  C035.records ++
  C036.records ++
  C037.records ++
  C038.records ++
  C039.records ++
  C040.records

theorem all_size : all.size = 5134 := by
  simp only [all, Array.size_append, C000.size, C001.size, C002.size, C003.size, C004.size, C005.size, C006.size, C007.size, C008.size, C009.size, C010.size, C011.size, C012.size, C013.size, C014.size, C015.size, C016.size, C017.size, C018.size, C019.size, C020.size, C021.size, C022.size, C023.size, C024.size, C025.size, C026.size, C027.size, C028.size, C029.size, C030.size, C031.size, C032.size, C033.size, C034.size, C035.size, C036.size, C037.size, C038.size, C039.size, C040.size]

theorem all_indices : all.toList.map RawOriginal.index = List.range 5134 := by
  simp only [all, Array.toList_append, List.map_append, C000.indices, C001.indices, C002.indices, C003.indices, C004.indices, C005.indices, C006.indices, C007.indices, C008.indices, C009.indices, C010.indices, C011.indices, C012.indices, C013.indices, C014.indices, C015.indices, C016.indices, C017.indices, C018.indices, C019.indices, C020.indices, C021.indices, C022.indices, C023.indices, C024.indices, C025.indices, C026.indices, C027.indices, C028.indices, C029.indices, C030.indices, C031.indices, C032.indices, C033.indices, C034.indices, C035.indices, C036.indices, C037.indices, C038.indices, C039.indices, C040.indices, List.range_eq_range']
  simp only [List.append_assoc]
  rw [show List.range' 4992 128 ++ List.range' 5120 14 = List.range' 4992 142 from List.range'_append]
  rw [show List.range' 4864 128 ++ List.range' 4992 142 = List.range' 4864 270 from List.range'_append]
  rw [show List.range' 4736 128 ++ List.range' 4864 270 = List.range' 4736 398 from List.range'_append]
  rw [show List.range' 4608 128 ++ List.range' 4736 398 = List.range' 4608 526 from List.range'_append]
  rw [show List.range' 4480 128 ++ List.range' 4608 526 = List.range' 4480 654 from List.range'_append]
  rw [show List.range' 4352 128 ++ List.range' 4480 654 = List.range' 4352 782 from List.range'_append]
  rw [show List.range' 4224 128 ++ List.range' 4352 782 = List.range' 4224 910 from List.range'_append]
  rw [show List.range' 4096 128 ++ List.range' 4224 910 = List.range' 4096 1038 from List.range'_append]
  rw [show List.range' 3968 128 ++ List.range' 4096 1038 = List.range' 3968 1166 from List.range'_append]
  rw [show List.range' 3840 128 ++ List.range' 3968 1166 = List.range' 3840 1294 from List.range'_append]
  rw [show List.range' 3712 128 ++ List.range' 3840 1294 = List.range' 3712 1422 from List.range'_append]
  rw [show List.range' 3584 128 ++ List.range' 3712 1422 = List.range' 3584 1550 from List.range'_append]
  rw [show List.range' 3456 128 ++ List.range' 3584 1550 = List.range' 3456 1678 from List.range'_append]
  rw [show List.range' 3328 128 ++ List.range' 3456 1678 = List.range' 3328 1806 from List.range'_append]
  rw [show List.range' 3200 128 ++ List.range' 3328 1806 = List.range' 3200 1934 from List.range'_append]
  rw [show List.range' 3072 128 ++ List.range' 3200 1934 = List.range' 3072 2062 from List.range'_append]
  rw [show List.range' 2944 128 ++ List.range' 3072 2062 = List.range' 2944 2190 from List.range'_append]
  rw [show List.range' 2816 128 ++ List.range' 2944 2190 = List.range' 2816 2318 from List.range'_append]
  rw [show List.range' 2688 128 ++ List.range' 2816 2318 = List.range' 2688 2446 from List.range'_append]
  rw [show List.range' 2560 128 ++ List.range' 2688 2446 = List.range' 2560 2574 from List.range'_append]
  rw [show List.range' 2432 128 ++ List.range' 2560 2574 = List.range' 2432 2702 from List.range'_append]
  rw [show List.range' 2304 128 ++ List.range' 2432 2702 = List.range' 2304 2830 from List.range'_append]
  rw [show List.range' 2176 128 ++ List.range' 2304 2830 = List.range' 2176 2958 from List.range'_append]
  rw [show List.range' 2048 128 ++ List.range' 2176 2958 = List.range' 2048 3086 from List.range'_append]
  rw [show List.range' 1920 128 ++ List.range' 2048 3086 = List.range' 1920 3214 from List.range'_append]
  rw [show List.range' 1792 128 ++ List.range' 1920 3214 = List.range' 1792 3342 from List.range'_append]
  rw [show List.range' 1664 128 ++ List.range' 1792 3342 = List.range' 1664 3470 from List.range'_append]
  rw [show List.range' 1536 128 ++ List.range' 1664 3470 = List.range' 1536 3598 from List.range'_append]
  rw [show List.range' 1408 128 ++ List.range' 1536 3598 = List.range' 1408 3726 from List.range'_append]
  rw [show List.range' 1280 128 ++ List.range' 1408 3726 = List.range' 1280 3854 from List.range'_append]
  rw [show List.range' 1152 128 ++ List.range' 1280 3854 = List.range' 1152 3982 from List.range'_append]
  rw [show List.range' 1024 128 ++ List.range' 1152 3982 = List.range' 1024 4110 from List.range'_append]
  rw [show List.range' 896 128 ++ List.range' 1024 4110 = List.range' 896 4238 from List.range'_append]
  rw [show List.range' 768 128 ++ List.range' 896 4238 = List.range' 768 4366 from List.range'_append]
  rw [show List.range' 640 128 ++ List.range' 768 4366 = List.range' 640 4494 from List.range'_append]
  rw [show List.range' 512 128 ++ List.range' 640 4494 = List.range' 512 4622 from List.range'_append]
  rw [show List.range' 384 128 ++ List.range' 512 4622 = List.range' 384 4750 from List.range'_append]
  rw [show List.range' 256 128 ++ List.range' 384 4750 = List.range' 256 4878 from List.range'_append]
  rw [show List.range' 128 128 ++ List.range' 256 4878 = List.range' 128 5006 from List.range'_append]
  rw [show List.range' 0 128 ++ List.range' 128 5006 = List.range' 0 5134 from List.range'_append]

/-- Indexing is total on the exact original5134-ID domain. -/
def originalAt (i : Fin 5134) : RawOriginal :=
  all[i.val]'(by rw [all_size]; exact i.isLt)

end PA215.Census
