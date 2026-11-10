import PA215.Source.DestinationCertificate
import PA215.Census.C040
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA215.Source.DestinationJoin.D040
private def site0 : Site := ⟨[false,false,false,false],.dec 8⟩
private theorem lookup0 : exactSites[0]? = some site0 := by rfl
private def site3933 : Site := ⟨[true,true,true,true,true,true,false,false,false],.dec 2⟩
private theorem lookup3933 : exactSites[3933]? = some site3933 := by rfl
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
private def inst3936 : Instruction := .jump (some 3940)
private theorem resolved3936 : resolveAt exactSites 3936 = some inst3936 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3936]
  rfl
private def inst3937 : Instruction := .dec 7 (some 3940) (some 3938)
private theorem resolved3937 : resolveAt exactSites 3937 = some inst3937 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3937]
  rfl
private def inst3938 : Instruction := .inc 6 (some 3939)
private theorem resolved3938 : resolveAt exactSites 3938 = some inst3938 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3938]
  rfl
private def inst3939 : Instruction := .jump (some 3937)
private theorem resolved3939 : resolveAt exactSites 3939 = some inst3939 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3939]
  rfl
private def inst3940 : Instruction := .jump (some 3933)
private theorem resolved3940 : resolveAt exactSites 3940 = some inst3940 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3940]
  rfl
private def inst3941 : Instruction := .dec 7 (some 3944) (some 3942)
private theorem resolved3941 : resolveAt exactSites 3941 = some inst3941 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3941]
  rfl
private def inst3942 : Instruction := .inc 2 (some 3943)
private theorem resolved3942 : resolveAt exactSites 3942 = some inst3942 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3942]
  rfl
private def inst3943 : Instruction := .jump (some 3941)
private theorem resolved3943 : resolveAt exactSites 3943 = some inst3943 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3943]
  rfl
private def inst3944 : Instruction := .dec 6 none (some 3945)
private theorem resolved3944 : resolveAt exactSites 3944 = some inst3944 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3944]
  rfl
private def inst3945 : Instruction := .inc 5 (some 3946)
private theorem resolved3945 : resolveAt exactSites 3945 = some inst3945 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3945]
  rfl
private def inst3946 : Instruction := .jump (some 3944)
private theorem resolved3946 : resolveAt exactSites 3946 = some inst3946 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3946]
  rfl
private def raw0 := PA215.Census.C040.records[0]
private theorem row0 : destinationAgrees raw0 = true := by
  apply destination_nonterminal (s := site3936) (i := inst3936)
    (p := ⟨[true,true,true,true,true,true,false,false,true,true,true],0,.none⟩) (q := (.at 3940)) (e := .none) (k := 3940) (next := site3940)
  · rw [show raw0.siteIndex = 3936 from rfl]
    exact lookup3936
  · rw [show raw0.siteIndex = 3936 from rfl]
    exact resolved3936
  · decide
  · decide
  · rfl
  · exact lookup3940
  · decide
private def raw1 := PA215.Census.C040.records[1]
private theorem row1 : destinationAgrees raw1 = true := by
  apply destination_nonterminal (s := site3937) (i := inst3937)
    (p := ⟨[true,true,true,true,true,true,false,false,true,true,true,false],0,.none⟩) (q := (.at 3940)) (e := .none) (k := 3940) (next := site3940)
  · rw [show raw1.siteIndex = 3937 from rfl]
    exact lookup3937
  · rw [show raw1.siteIndex = 3937 from rfl]
    exact resolved3937
  · decide
  · decide
  · rfl
  · exact lookup3940
  · decide
private def raw2 := PA215.Census.C040.records[2]
private theorem row2 : destinationAgrees raw2 = true := by
  apply destination_nonterminal (s := site3937) (i := inst3937)
    (p := ⟨[true,true,true,true,true,true,false,false,true,true,false,true,true],1,(.dec 5)⟩) (q := (.at 3938)) (e := (.dec 5)) (k := 3938) (next := site3938)
  · rw [show raw2.siteIndex = 3937 from rfl]
    exact lookup3937
  · rw [show raw2.siteIndex = 3937 from rfl]
    exact resolved3937
  · decide
  · decide
  · rfl
  · exact lookup3938
  · decide
private def raw3 := PA215.Census.C040.records[3]
private theorem row3 : destinationAgrees raw3 = true := by
  apply destination_nonterminal (s := site3938) (i := inst3938)
    (p := ⟨[true,true,true,true,true,true,false,false,true,true,false,true,true,true],0,(.inc 8)⟩) (q := (.at 3939)) (e := (.inc 8)) (k := 3939) (next := site3939)
  · rw [show raw3.siteIndex = 3938 from rfl]
    exact lookup3938
  · rw [show raw3.siteIndex = 3938 from rfl]
    exact resolved3938
  · decide
  · decide
  · rfl
  · exact lookup3939
  · decide
private def raw4 := PA215.Census.C040.records[4]
private theorem row4 : destinationAgrees raw4 = true := by
  apply destination_nonterminal (s := site3939) (i := inst3939)
    (p := ⟨[true,true,true,true,true,true,false,false,true,true,false,true],0,.none⟩) (q := (.at 3937)) (e := .none) (k := 3937) (next := site3937)
  · rw [show raw4.siteIndex = 3939 from rfl]
    exact lookup3939
  · rw [show raw4.siteIndex = 3939 from rfl]
    exact resolved3939
  · decide
  · decide
  · rfl
  · exact lookup3937
  · decide
private def raw5 := PA215.Census.C040.records[5]
private theorem row5 : destinationAgrees raw5 = true := by
  apply destination_nonterminal (s := site3940) (i := inst3940)
    (p := ⟨[true,true,true,true,true,true,false,false],0,.none⟩) (q := (.at 3933)) (e := .none) (k := 3933) (next := site3933)
  · rw [show raw5.siteIndex = 3940 from rfl]
    exact lookup3940
  · rw [show raw5.siteIndex = 3940 from rfl]
    exact resolved3940
  · decide
  · decide
  · rfl
  · exact lookup3933
  · decide
private def raw6 := PA215.Census.C040.records[6]
private theorem row6 : destinationAgrees raw6 = true := by
  apply destination_nonterminal (s := site3941) (i := inst3941)
    (p := ⟨[true,true,true,true,true,true,true,false],0,.none⟩) (q := (.at 3944)) (e := .none) (k := 3944) (next := site3944)
  · rw [show raw6.siteIndex = 3941 from rfl]
    exact lookup3941
  · rw [show raw6.siteIndex = 3941 from rfl]
    exact resolved3941
  · decide
  · decide
  · rfl
  · exact lookup3944
  · decide
private def raw7 := PA215.Census.C040.records[7]
private theorem row7 : destinationAgrees raw7 = true := by
  apply destination_nonterminal (s := site3941) (i := inst3941)
    (p := ⟨[true,true,true,true,true,true,false,true,true],1,(.dec 5)⟩) (q := (.at 3942)) (e := (.dec 5)) (k := 3942) (next := site3942)
  · rw [show raw7.siteIndex = 3941 from rfl]
    exact lookup3941
  · rw [show raw7.siteIndex = 3941 from rfl]
    exact resolved3941
  · decide
  · decide
  · rfl
  · exact lookup3942
  · decide
private def raw8 := PA215.Census.C040.records[8]
private theorem row8 : destinationAgrees raw8 = true := by
  apply destination_nonterminal (s := site3942) (i := inst3942)
    (p := ⟨[true,true,true,true,true,true,false,true,true,true],0,(.inc 0)⟩) (q := (.at 3943)) (e := (.inc 0)) (k := 3943) (next := site3943)
  · rw [show raw8.siteIndex = 3942 from rfl]
    exact lookup3942
  · rw [show raw8.siteIndex = 3942 from rfl]
    exact resolved3942
  · decide
  · decide
  · rfl
  · exact lookup3943
  · decide
private def raw9 := PA215.Census.C040.records[9]
private theorem row9 : destinationAgrees raw9 = true := by
  apply destination_nonterminal (s := site3943) (i := inst3943)
    (p := ⟨[true,true,true,true,true,true,false,true],0,.none⟩) (q := (.at 3941)) (e := .none) (k := 3941) (next := site3941)
  · rw [show raw9.siteIndex = 3943 from rfl]
    exact lookup3943
  · rw [show raw9.siteIndex = 3943 from rfl]
    exact resolved3943
  · decide
  · decide
  · rfl
  · exact lookup3941
  · decide
private def raw10 := PA215.Census.C040.records[10]
private theorem row10 : destinationAgrees raw10 = true := by
  apply destination_nonterminal (s := site3944) (i := inst3944)
    (p := ⟨[],1,.none⟩) (q := .exited) (e := .none) (k := 0) (next := site0)
  · rw [show raw10.siteIndex = 3944 from rfl]
    exact lookup3944
  · rw [show raw10.siteIndex = 3944 from rfl]
    exact resolved3944
  · decide
  · decide
  · rfl
  · exact lookup0
  · decide
private def raw11 := PA215.Census.C040.records[11]
private theorem row11 : destinationAgrees raw11 = true := by
  apply destination_nonterminal (s := site3944) (i := inst3944)
    (p := ⟨[true,true,true,true,true,true,true,true],1,(.dec 8)⟩) (q := (.at 3945)) (e := (.dec 8)) (k := 3945) (next := site3945)
  · rw [show raw11.siteIndex = 3944 from rfl]
    exact lookup3944
  · rw [show raw11.siteIndex = 3944 from rfl]
    exact resolved3944
  · decide
  · decide
  · rfl
  · exact lookup3945
  · decide
private def raw12 := PA215.Census.C040.records[12]
private theorem row12 : destinationAgrees raw12 = true := by
  apply destination_nonterminal (s := site3945) (i := inst3945)
    (p := ⟨[true,true,true,true,true,true,true,true,true],0,(.inc 7)⟩) (q := (.at 3946)) (e := (.inc 7)) (k := 3946) (next := site3946)
  · rw [show raw12.siteIndex = 3945 from rfl]
    exact lookup3945
  · rw [show raw12.siteIndex = 3945 from rfl]
    exact resolved3945
  · decide
  · decide
  · rfl
  · exact lookup3946
  · decide
private def raw13 := PA215.Census.C040.records[13]
private theorem row13 : destinationAgrees raw13 = true := by
  apply destination_nonterminal (s := site3946) (i := inst3946)
    (p := ⟨[true,true,true,true,true,true,true],0,.none⟩) (q := (.at 3944)) (e := .none) (k := 3944) (next := site3944)
  · rw [show raw13.siteIndex = 3946 from rfl]
    exact lookup3946
  · rw [show raw13.siteIndex = 3946 from rfl]
    exact resolved3946
  · decide
  · decide
  · rfl
  · exact lookup3944
  · decide
private theorem enumeration : PA215.Census.C040.records.toList = [raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7,raw8,raw9,raw10,raw11,raw12,raw13] := by rfl
theorem checked : PA215.Census.C040.records.toList.all destinationAgrees = true := by
  rw [enumeration]
  simp only [List.all_cons,List.all_nil,row0,row1,row2,row3,row4,row5,row6,row7,row8,row9,row10,row11,row12,row13,Bool.and_self]
#print axioms checked
end PA215.Source.DestinationJoin.D040
