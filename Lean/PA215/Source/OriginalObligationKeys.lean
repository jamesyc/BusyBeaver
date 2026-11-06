import PA215.Source.ObligationCensus.K000
import PA215.Source.ObligationCensus.K001
import PA215.Source.ObligationCensus.K002
import PA215.Source.ObligationCensus.K003
import PA215.Source.ObligationCensus.K004
import PA215.Source.ObligationCensus.K005
import PA215.Source.ObligationCensus.K006
import PA215.Source.ObligationCensus.K007
import PA215.Source.ObligationCensus.K008
import PA215.Source.ObligationCensus.K009
import PA215.Source.ObligationCensus.K010
import PA215.Source.ObligationCensus.K011
import PA215.Source.ObligationCensus.K012
import PA215.Source.ObligationCensus.K013
import PA215.Source.ObligationCensus.K014
import PA215.Source.ObligationCensus.K015
import PA215.Source.ObligationCensus.K016
import PA215.Source.ObligationCensus.K017
import PA215.Source.ObligationCensus.K018
import PA215.Source.ObligationCensus.K019
import PA215.Source.ObligationCensus.K020
import PA215.Source.ObligationCensus.K021
import PA215.Source.ObligationCensus.K022
import PA215.Source.ObligationCensus.K023
import PA215.Source.ObligationCensus.K024
import PA215.Source.ObligationCensus.K025
import PA215.Source.ObligationCensus.K026
import PA215.Source.ObligationCensus.K027
import PA215.Source.ObligationCensus.K028
import PA215.Source.ObligationCensus.K029
import PA215.Source.ObligationCensus.K030
import PA215.Source.ObligationCensus.K031
import PA215.Source.ObligationCensus.K032
import PA215.Source.ObligationCensus.K033
import PA215.Source.ObligationCensus.K034
import PA215.Source.ObligationCensus.K035
import PA215.Source.ObligationCensus.K036
import PA215.Source.ObligationCensus.K037
import PA215.Source.ObligationCensus.K038
import PA215.Source.ObligationCensus.K039
import PA215.Source.ObligationCensus.K040
import PA215.Source.ExactObligationKeys
import PA215.OriginalCensus
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA215.Source.ObligationKeys
attribute [local irreducible] PA215.Census.C000.records PA215.Census.C001.records PA215.Census.C002.records PA215.Census.C003.records PA215.Census.C004.records PA215.Census.C005.records PA215.Census.C006.records PA215.Census.C007.records PA215.Census.C008.records PA215.Census.C009.records PA215.Census.C010.records PA215.Census.C011.records PA215.Census.C012.records PA215.Census.C013.records PA215.Census.C014.records PA215.Census.C015.records PA215.Census.C016.records PA215.Census.C017.records PA215.Census.C018.records PA215.Census.C019.records PA215.Census.C020.records PA215.Census.C021.records PA215.Census.C022.records PA215.Census.C023.records PA215.Census.C024.records PA215.Census.C025.records PA215.Census.C026.records PA215.Census.C027.records PA215.Census.C028.records PA215.Census.C029.records PA215.Census.C030.records PA215.Census.C031.records PA215.Census.C032.records PA215.Census.C033.records PA215.Census.C034.records PA215.Census.C035.records PA215.Census.C036.records PA215.Census.C037.records PA215.Census.C038.records PA215.Census.C039.records PA215.Census.C040.records

private theorem keys_append {a b : Array PA215.Census.RawOriginal} {ka kb : List Nat}
    (ha : a.toList.map rawKey = ka) (hb : b.toList.map rawKey = kb) :
    (a++b).toList.map rawKey = ka++kb := by
  rw [Array.toList_append,List.map_append,ha,hb]

def groupedKeys : List Nat := ObligationCensus.K000.keys ++ (ObligationCensus.K001.keys ++ (ObligationCensus.K002.keys ++ (ObligationCensus.K003.keys ++ (ObligationCensus.K004.keys ++ (ObligationCensus.K005.keys ++ (ObligationCensus.K006.keys ++ (ObligationCensus.K007.keys ++ (ObligationCensus.K008.keys ++ (ObligationCensus.K009.keys ++ (ObligationCensus.K010.keys ++ (ObligationCensus.K011.keys ++ (ObligationCensus.K012.keys ++ (ObligationCensus.K013.keys ++ (ObligationCensus.K014.keys ++ (ObligationCensus.K015.keys ++ (ObligationCensus.K016.keys ++ (ObligationCensus.K017.keys ++ (ObligationCensus.K018.keys ++ (ObligationCensus.K019.keys ++ (ObligationCensus.K020.keys ++ (ObligationCensus.K021.keys ++ (ObligationCensus.K022.keys ++ (ObligationCensus.K023.keys ++ (ObligationCensus.K024.keys ++ (ObligationCensus.K025.keys ++ (ObligationCensus.K026.keys ++ (ObligationCensus.K027.keys ++ (ObligationCensus.K028.keys ++ (ObligationCensus.K029.keys ++ (ObligationCensus.K030.keys ++ (ObligationCensus.K031.keys ++ (ObligationCensus.K032.keys ++ (ObligationCensus.K033.keys ++ (ObligationCensus.K034.keys ++ (ObligationCensus.K035.keys ++ (ObligationCensus.K036.keys ++ (ObligationCensus.K037.keys ++ (ObligationCensus.K038.keys ++ (ObligationCensus.K039.keys ++ (ObligationCensus.K040.keys))))))))))))))))))))))))))))))))))))))))

theorem original_keys_grouped : PA215.Census.all.toList.map rawKey = groupedKeys := by
  unfold PA215.Census.all
  simp only [Array.append_assoc]
  exact keys_append ObligationCensus.K000.checked (keys_append ObligationCensus.K001.checked (keys_append ObligationCensus.K002.checked (keys_append ObligationCensus.K003.checked (keys_append ObligationCensus.K004.checked (keys_append ObligationCensus.K005.checked (keys_append ObligationCensus.K006.checked (keys_append ObligationCensus.K007.checked (keys_append ObligationCensus.K008.checked (keys_append ObligationCensus.K009.checked (keys_append ObligationCensus.K010.checked (keys_append ObligationCensus.K011.checked (keys_append ObligationCensus.K012.checked (keys_append ObligationCensus.K013.checked (keys_append ObligationCensus.K014.checked (keys_append ObligationCensus.K015.checked (keys_append ObligationCensus.K016.checked (keys_append ObligationCensus.K017.checked (keys_append ObligationCensus.K018.checked (keys_append ObligationCensus.K019.checked (keys_append ObligationCensus.K020.checked (keys_append ObligationCensus.K021.checked (keys_append ObligationCensus.K022.checked (keys_append ObligationCensus.K023.checked (keys_append ObligationCensus.K024.checked (keys_append ObligationCensus.K025.checked (keys_append ObligationCensus.K026.checked (keys_append ObligationCensus.K027.checked (keys_append ObligationCensus.K028.checked (keys_append ObligationCensus.K029.checked (keys_append ObligationCensus.K030.checked (keys_append ObligationCensus.K031.checked (keys_append ObligationCensus.K032.checked (keys_append ObligationCensus.K033.checked (keys_append ObligationCensus.K034.checked (keys_append ObligationCensus.K035.checked (keys_append ObligationCensus.K036.checked (keys_append ObligationCensus.K037.checked (keys_append ObligationCensus.K038.checked (keys_append ObligationCensus.K039.checked (ObligationCensus.K040.checked))))))))))))))))))))))))))))))))))))))))

theorem grouped_expected : groupedKeys = expectedKeys := by rfl

theorem original_keys : PA215.Census.all.toList.map rawKey = expectedKeys :=
  original_keys_grouped.trans grouped_expected
#print axioms original_keys
end PA215.Source.ObligationKeys
