import PA215.Source.ContractJoinPilot
import PA215.Census.C040
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace PA215.Source.CensusJoin.J040
private def site3936 : Site := ⟨[true,true,true,true,true,true,false,false,true,true,false,false,true],.breakTo 1⟩
private theorem lookup3936 : exactSites[3936]? = some site3936 := by rfl
private def site3937 : Site := ⟨[true,true,true,true,true,true,false,false,true,true,false,true,false],.dec 7⟩
private theorem lookup3937 : exactSites[3937]? = some site3937 := by rfl
private def site3938 : Site := ⟨[true,true,true,true,true,true,false,false,true,true,false,true,true,false],.inc 6⟩
private theorem lookup3938 : exactSites[3938]? = some site3938 := by rfl
private def site3939 : Site := ⟨[true,true,true,true,true,true,false,false,true,true,false,true,true,true],.continueTo 2⟩
private theorem lookup3939 : exactSites[3939]? = some site3939 := by rfl
private def site3940 : Site := ⟨[true,true,true,true,true,true,false,false,true,true,true],.continueTo 3⟩
private theorem lookup3940 : exactSites[3940]? = some site3940 := by rfl
private def site3941 : Site := ⟨[true,true,true,true,true,true,false,true,false],.dec 7⟩
private theorem lookup3941 : exactSites[3941]? = some site3941 := by rfl
private def site3942 : Site := ⟨[true,true,true,true,true,true,false,true,true,false],.inc 2⟩
private theorem lookup3942 : exactSites[3942]? = some site3942 := by rfl
private def site3943 : Site := ⟨[true,true,true,true,true,true,false,true,true,true],.continueTo 2⟩
private theorem lookup3943 : exactSites[3943]? = some site3943 := by rfl
private def site3944 : Site := ⟨[true,true,true,true,true,true,true,false],.dec 6⟩
private theorem lookup3944 : exactSites[3944]? = some site3944 := by rfl
private def site3945 : Site := ⟨[true,true,true,true,true,true,true,true,false],.inc 5⟩
private theorem lookup3945 : exactSites[3945]? = some site3945 := by rfl
private def site3946 : Site := ⟨[true,true,true,true,true,true,true,true,true],.continueTo 2⟩
private theorem lookup3946 : exactSites[3946]? = some site3946 := by rfl
private def raw0 := PA215.Census.C040.records[0]'(by decide)
private theorem row0 : recordAgrees raw0 = true := by
  unfold recordAgrees
  rw [show raw0.siteIndex = 3936 from rfl,lookup3936]
  decide
private def raw1 := PA215.Census.C040.records[1]'(by decide)
private theorem row1 : recordAgrees raw1 = true := by
  unfold recordAgrees
  rw [show raw1.siteIndex = 3937 from rfl,lookup3937]
  decide
private def raw2 := PA215.Census.C040.records[2]'(by decide)
private theorem row2 : recordAgrees raw2 = true := by
  unfold recordAgrees
  rw [show raw2.siteIndex = 3937 from rfl,lookup3937]
  decide
private def raw3 := PA215.Census.C040.records[3]'(by decide)
private theorem row3 : recordAgrees raw3 = true := by
  unfold recordAgrees
  rw [show raw3.siteIndex = 3938 from rfl,lookup3938]
  decide
private def raw4 := PA215.Census.C040.records[4]'(by decide)
private theorem row4 : recordAgrees raw4 = true := by
  unfold recordAgrees
  rw [show raw4.siteIndex = 3939 from rfl,lookup3939]
  decide
private def raw5 := PA215.Census.C040.records[5]'(by decide)
private theorem row5 : recordAgrees raw5 = true := by
  unfold recordAgrees
  rw [show raw5.siteIndex = 3940 from rfl,lookup3940]
  decide
private def raw6 := PA215.Census.C040.records[6]'(by decide)
private theorem row6 : recordAgrees raw6 = true := by
  unfold recordAgrees
  rw [show raw6.siteIndex = 3941 from rfl,lookup3941]
  decide
private def raw7 := PA215.Census.C040.records[7]'(by decide)
private theorem row7 : recordAgrees raw7 = true := by
  unfold recordAgrees
  rw [show raw7.siteIndex = 3941 from rfl,lookup3941]
  decide
private def raw8 := PA215.Census.C040.records[8]'(by decide)
private theorem row8 : recordAgrees raw8 = true := by
  unfold recordAgrees
  rw [show raw8.siteIndex = 3942 from rfl,lookup3942]
  decide
private def raw9 := PA215.Census.C040.records[9]'(by decide)
private theorem row9 : recordAgrees raw9 = true := by
  unfold recordAgrees
  rw [show raw9.siteIndex = 3943 from rfl,lookup3943]
  decide
private def raw10 := PA215.Census.C040.records[10]'(by decide)
private theorem row10 : recordAgrees raw10 = true := by
  unfold recordAgrees
  rw [show raw10.siteIndex = 3944 from rfl,lookup3944]
  decide
private def raw11 := PA215.Census.C040.records[11]'(by decide)
private theorem row11 : recordAgrees raw11 = true := by
  unfold recordAgrees
  rw [show raw11.siteIndex = 3944 from rfl,lookup3944]
  decide
private def raw12 := PA215.Census.C040.records[12]'(by decide)
private theorem row12 : recordAgrees raw12 = true := by
  unfold recordAgrees
  rw [show raw12.siteIndex = 3945 from rfl,lookup3945]
  decide
private def raw13 := PA215.Census.C040.records[13]'(by decide)
private theorem row13 : recordAgrees raw13 = true := by
  unfold recordAgrees
  rw [show raw13.siteIndex = 3946 from rfl,lookup3946]
  decide
private theorem enumeration : PA215.Census.C040.records.toList = [raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7,raw8,raw9,raw10,raw11,raw12,raw13] := by rfl
theorem checked : PA215.Census.C040.records.toList.all recordAgrees = true := by
  rw [enumeration]
  simp only [List.all_cons,List.all_nil,row0,row1,row2,row3,row4,row5,row6,row7,row8,row9,row10,row11,row12,row13,Bool.and_self]
#print axioms checked
end PA215.Source.CensusJoin.J040
