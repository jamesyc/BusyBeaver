import PA215.OriginalCensus
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace PA215.Census

def terminalMetadata (r : RawOriginal) : Bool :=
  (r.isHalt == (r.index == 5114)) && (r.target.isNone == r.isHalt)

theorem C000_terminalMetadata : C000.records.toList.all terminalMetadata = true := by decide

theorem C001_terminalMetadata : C001.records.toList.all terminalMetadata = true := by decide

theorem C002_terminalMetadata : C002.records.toList.all terminalMetadata = true := by decide

theorem C003_terminalMetadata : C003.records.toList.all terminalMetadata = true := by decide

theorem C004_terminalMetadata : C004.records.toList.all terminalMetadata = true := by decide

theorem C005_terminalMetadata : C005.records.toList.all terminalMetadata = true := by decide

theorem C006_terminalMetadata : C006.records.toList.all terminalMetadata = true := by decide

theorem C007_terminalMetadata : C007.records.toList.all terminalMetadata = true := by decide

theorem C008_terminalMetadata : C008.records.toList.all terminalMetadata = true := by decide

theorem C009_terminalMetadata : C009.records.toList.all terminalMetadata = true := by decide

theorem C010_terminalMetadata : C010.records.toList.all terminalMetadata = true := by decide

theorem C011_terminalMetadata : C011.records.toList.all terminalMetadata = true := by decide

theorem C012_terminalMetadata : C012.records.toList.all terminalMetadata = true := by decide

theorem C013_terminalMetadata : C013.records.toList.all terminalMetadata = true := by decide

theorem C014_terminalMetadata : C014.records.toList.all terminalMetadata = true := by decide

theorem C015_terminalMetadata : C015.records.toList.all terminalMetadata = true := by decide

theorem C016_terminalMetadata : C016.records.toList.all terminalMetadata = true := by decide

theorem C017_terminalMetadata : C017.records.toList.all terminalMetadata = true := by decide

theorem C018_terminalMetadata : C018.records.toList.all terminalMetadata = true := by decide

theorem C019_terminalMetadata : C019.records.toList.all terminalMetadata = true := by decide

theorem C020_terminalMetadata : C020.records.toList.all terminalMetadata = true := by decide

theorem C021_terminalMetadata : C021.records.toList.all terminalMetadata = true := by decide

theorem C022_terminalMetadata : C022.records.toList.all terminalMetadata = true := by decide

theorem C023_terminalMetadata : C023.records.toList.all terminalMetadata = true := by decide

theorem C024_terminalMetadata : C024.records.toList.all terminalMetadata = true := by decide

theorem C025_terminalMetadata : C025.records.toList.all terminalMetadata = true := by decide

theorem C026_terminalMetadata : C026.records.toList.all terminalMetadata = true := by decide

theorem C027_terminalMetadata : C027.records.toList.all terminalMetadata = true := by decide

theorem C028_terminalMetadata : C028.records.toList.all terminalMetadata = true := by decide

theorem C029_terminalMetadata : C029.records.toList.all terminalMetadata = true := by decide

theorem C030_terminalMetadata : C030.records.toList.all terminalMetadata = true := by decide

theorem C031_terminalMetadata : C031.records.toList.all terminalMetadata = true := by decide

theorem C032_terminalMetadata : C032.records.toList.all terminalMetadata = true := by decide

theorem C033_terminalMetadata : C033.records.toList.all terminalMetadata = true := by decide

theorem C034_terminalMetadata : C034.records.toList.all terminalMetadata = true := by decide

theorem C035_terminalMetadata : C035.records.toList.all terminalMetadata = true := by decide

theorem C036_terminalMetadata : C036.records.toList.all terminalMetadata = true := by decide

theorem C037_terminalMetadata : C037.records.toList.all terminalMetadata = true := by decide

theorem C038_terminalMetadata : C038.records.toList.all terminalMetadata = true := by decide

theorem C039_terminalMetadata : C039.records.toList.all terminalMetadata = true := by decide

theorem C040_terminalMetadata : C040.records.toList.all terminalMetadata = true := by decide

theorem all_terminalMetadata : all.toList.all terminalMetadata = true := by
  simp only [all, Array.toList_append, List.all_append,
    C000_terminalMetadata, C001_terminalMetadata, C002_terminalMetadata, C003_terminalMetadata, C004_terminalMetadata, C005_terminalMetadata, C006_terminalMetadata, C007_terminalMetadata, C008_terminalMetadata, C009_terminalMetadata, C010_terminalMetadata, C011_terminalMetadata, C012_terminalMetadata, C013_terminalMetadata, C014_terminalMetadata, C015_terminalMetadata, C016_terminalMetadata, C017_terminalMetadata, C018_terminalMetadata, C019_terminalMetadata, C020_terminalMetadata, C021_terminalMetadata, C022_terminalMetadata, C023_terminalMetadata, C024_terminalMetadata, C025_terminalMetadata, C026_terminalMetadata, C027_terminalMetadata, C028_terminalMetadata, C029_terminalMetadata, C030_terminalMetadata, C031_terminalMetadata, C032_terminalMetadata, C033_terminalMetadata, C034_terminalMetadata, C035_terminalMetadata, C036_terminalMetadata, C037_terminalMetadata, C038_terminalMetadata, C039_terminalMetadata, C040_terminalMetadata, Bool.and_true]

attribute [local irreducible] all originalAt

theorem originalAt_index (i : Fin 5134) : (originalAt i).index = i.val := by
  have h := congrArg (fun xs : List Nat => xs[i.val]?) all_indices
  have hb : i.val < all.size := by rw [all_size]; exact i.isLt
  have he : some (originalAt i).index = some i.val := by
    simpa only [List.getElem?_map, Array.getElem?_toList,
      Array.getElem?_eq_getElem hb, Option.map_some, List.getElem?_range i.isLt,
      originalAt] using h
  exact Option.some.inj he

theorem originalAt_terminalMetadata (i : Fin 5134) : terminalMetadata (originalAt i) = true := by
  apply List.all_eq_true.mp all_terminalMetadata
  unfold originalAt
  exact Array.getElem_mem_toList _

theorem originalAt_isHalt_iff (i : Fin 5134) :
    (originalAt i).isHalt = true ↔ i.val = 5114 := by
  have h := originalAt_terminalMetadata i
  simp only [terminalMetadata, Bool.and_eq_true, beq_iff_eq] at h
  rw [h.1, originalAt_index]
  simp

theorem originalAt_target_none_iff (i : Fin 5134) :
    (originalAt i).target = none ↔ i.val = 5114 := by
  have h := originalAt_terminalMetadata i
  simp only [terminalMetadata, Bool.and_eq_true, beq_iff_eq] at h
  have ht : (originalAt i).target.isNone = true ↔ (originalAt i).isHalt = true := by rw [h.2]
  simpa using ht.trans (originalAt_isHalt_iff i)

end PA215.Census
