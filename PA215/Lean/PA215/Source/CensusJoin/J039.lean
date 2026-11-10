import PA215.Source.ContractJoinPilot
import PA215.Census.C039
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace PA215.Source.CensusJoin.J039
private def site3841 : Site := ⟨[true,false,true,false,true,false,false,false,true,true,true,true,false],.dec 6⟩
private theorem lookup3841 : exactSites[3841]? = some site3841 := by rfl
private def site3842 : Site := ⟨[true,false,true,false,true,false,false,false,true,true,true,true,true,false],.inc 4⟩
private theorem lookup3842 : exactSites[3842]? = some site3842 := by rfl
private def site3843 : Site := ⟨[true,false,true,false,true,false,false,false,true,true,true,true,true,true],.continueTo 2⟩
private theorem lookup3843 : exactSites[3843]? = some site3843 := by rfl
private def site3844 : Site := ⟨[true,false,true,false,true,false,false,true,false,false,false],.dec 2⟩
private theorem lookup3844 : exactSites[3844]? = some site3844 := by rfl
private def site3845 : Site := ⟨[true,false,true,false,true,false,false,true,false,false,true,false],.inc 7⟩
private theorem lookup3845 : exactSites[3845]? = some site3845 := by rfl
private def site3846 : Site := ⟨[true,false,true,false,true,false,false,true,false,false,true,true,false,false,false],.dec 6⟩
private theorem lookup3846 : exactSites[3846]? = some site3846 := by rfl
private def site3847 : Site := ⟨[true,false,true,false,true,false,false,true,false,false,true,true,false,false,true],.breakTo 1⟩
private theorem lookup3847 : exactSites[3847]? = some site3847 := by rfl
private def site3848 : Site := ⟨[true,false,true,false,true,false,false,true,false,false,true,true,false,true,false],.dec 7⟩
private theorem lookup3848 : exactSites[3848]? = some site3848 := by rfl
private def site3849 : Site := ⟨[true,false,true,false,true,false,false,true,false,false,true,true,false,true,true,false],.inc 6⟩
private theorem lookup3849 : exactSites[3849]? = some site3849 := by rfl
private def site3850 : Site := ⟨[true,false,true,false,true,false,false,true,false,false,true,true,false,true,true,true],.continueTo 2⟩
private theorem lookup3850 : exactSites[3850]? = some site3850 := by rfl
private def site3851 : Site := ⟨[true,false,true,false,true,false,false,true,false,false,true,true,true],.continueTo 3⟩
private theorem lookup3851 : exactSites[3851]? = some site3851 := by rfl
private def site3852 : Site := ⟨[true,false,true,false,true,false,false,true,false,true,false],.dec 7⟩
private theorem lookup3852 : exactSites[3852]? = some site3852 := by rfl
private def site3853 : Site := ⟨[true,false,true,false,true,false,false,true,false,true,true,false],.inc 2⟩
private theorem lookup3853 : exactSites[3853]? = some site3853 := by rfl
private def site3854 : Site := ⟨[true,false,true,false,true,false,false,true,false,true,true,true],.continueTo 2⟩
private theorem lookup3854 : exactSites[3854]? = some site3854 := by rfl
private def site3855 : Site := ⟨[true,false,true,false,true,false,false,true,true,false,false,false],.dec 1⟩
private theorem lookup3855 : exactSites[3855]? = some site3855 := by rfl
private def site3856 : Site := ⟨[true,false,true,false,true,false,false,true,true,false,false,true,false],.inc 7⟩
private theorem lookup3856 : exactSites[3856]? = some site3856 := by rfl
private def site3857 : Site := ⟨[true,false,true,false,true,false,false,true,true,false,false,true,true,false],.inc 6⟩
private theorem lookup3857 : exactSites[3857]? = some site3857 := by rfl
private def site3858 : Site := ⟨[true,false,true,false,true,false,false,true,true,false,false,true,true,true],.continueTo 3⟩
private theorem lookup3858 : exactSites[3858]? = some site3858 := by rfl
private def site3859 : Site := ⟨[true,false,true,false,true,false,false,true,true,false,true,false],.dec 6⟩
private theorem lookup3859 : exactSites[3859]? = some site3859 := by rfl
private def site3860 : Site := ⟨[true,false,true,false,true,false,false,true,true,false,true,true,false,false],.inc 7⟩
private theorem lookup3860 : exactSites[3860]? = some site3860 := by rfl
private def site3861 : Site := ⟨[true,false,true,false,true,false,false,true,true,false,true,true,false,true,false],.dec 6⟩
private theorem lookup3861 : exactSites[3861]? = some site3861 := by rfl
private def site3862 : Site := ⟨[true,false,true,false,true,false,false,true,true,false,true,true,false,true,true,false],.inc 1⟩
private theorem lookup3862 : exactSites[3862]? = some site3862 := by rfl
private def site3863 : Site := ⟨[true,false,true,false,true,false,false,true,true,false,true,true,false,true,true,true],.continueTo 2⟩
private theorem lookup3863 : exactSites[3863]? = some site3863 := by rfl
private def site3864 : Site := ⟨[true,false,true,false,true,false,false,true,true,false,true,true,true],.continueTo 3⟩
private theorem lookup3864 : exactSites[3864]? = some site3864 := by rfl
private def site3865 : Site := ⟨[true,false,true,false,true,false,false,true,true,true,false],.dec 7⟩
private theorem lookup3865 : exactSites[3865]? = some site3865 := by rfl
private def site3866 : Site := ⟨[true,false,true,false,true,false,false,true,true,true,true,false,false,false],.inc 1⟩
private theorem lookup3866 : exactSites[3866]? = some site3866 := by rfl
private def site3867 : Site := ⟨[true,false,true,false,true,false,false,true,true,true,true,false,false,true],.inc 1⟩
private theorem lookup3867 : exactSites[3867]? = some site3867 := by rfl
private def site3868 : Site := ⟨[true,false,true,false,true,false,false,true,true,true,true,false,true,false],.inc 1⟩
private theorem lookup3868 : exactSites[3868]? = some site3868 := by rfl
private def site3869 : Site := ⟨[true,false,true,false,true,false,false,true,true,true,true,false,true,true],.inc 1⟩
private theorem lookup3869 : exactSites[3869]? = some site3869 := by rfl
private def site3870 : Site := ⟨[true,false,true,false,true,false,false,true,true,true,true,true],.continueTo 2⟩
private theorem lookup3870 : exactSites[3870]? = some site3870 := by rfl
private def site3871 : Site := ⟨[true,false,true,false,true,false,true,false],.dec 1⟩
private theorem lookup3871 : exactSites[3871]? = some site3871 := by rfl
private def site3872 : Site := ⟨[true,false,true,false,true,false,true,true,false],.inc 6⟩
private theorem lookup3872 : exactSites[3872]? = some site3872 := by rfl
private def site3873 : Site := ⟨[true,false,true,false,true,false,true,true,true],.continueTo 2⟩
private theorem lookup3873 : exactSites[3873]? = some site3873 := by rfl
private def site3874 : Site := ⟨[true,false,true,false,true,true,false,false,false,false],.dec 5⟩
private theorem lookup3874 : exactSites[3874]? = some site3874 := by rfl
private def site3875 : Site := ⟨[true,false,true,false,true,true,false,false,false,true,false,false],.dec 6⟩
private theorem lookup3875 : exactSites[3875]? = some site3875 := by rfl
private def site3876 : Site := ⟨[true,false,true,false,true,true,false,false,false,true,false,true],.continueTo 2⟩
private theorem lookup3876 : exactSites[3876]? = some site3876 := by rfl
private def site3877 : Site := ⟨[true,false,true,false,true,true,false,false,false,true,true],.breakTo 1⟩
private theorem lookup3877 : exactSites[3877]? = some site3877 := by rfl
private def site3878 : Site := ⟨[true,false,true,false,true,true,false,false,true],.dec 6⟩
private theorem lookup3878 : exactSites[3878]? = some site3878 := by rfl
private def site3879 : Site := ⟨[true,false,true,false,true,true,false,true,false,false],.dec 5⟩
private theorem lookup3879 : exactSites[3879]? = some site3879 := by rfl
private def site3880 : Site := ⟨[true,false,true,false,true,true,false,true,false,true],.continueTo 1⟩
private theorem lookup3880 : exactSites[3880]? = some site3880 := by rfl
private def site3881 : Site := ⟨[true,false,true,false,true,true,false,true,true,false,false],.dec 6⟩
private theorem lookup3881 : exactSites[3881]? = some site3881 := by rfl
private def site3882 : Site := ⟨[true,false,true,false,true,true,false,true,true,false,true],.continueTo 2⟩
private theorem lookup3882 : exactSites[3882]? = some site3882 := by rfl
private def site3883 : Site := ⟨[true,false,true,false,true,true,false,true,true,true],.breakTo 1⟩
private theorem lookup3883 : exactSites[3883]? = some site3883 := by rfl
private def site3884 : Site := ⟨[true,false,true,false,true,true,true,false,false,false],.dec 1⟩
private theorem lookup3884 : exactSites[3884]? = some site3884 := by rfl
private def site3885 : Site := ⟨[true,false,true,false,true,true,true,false,false,true,false],.inc 6⟩
private theorem lookup3885 : exactSites[3885]? = some site3885 := by rfl
private def site3886 : Site := ⟨[true,false,true,false,true,true,true,false,false,true,true],.continueTo 2⟩
private theorem lookup3886 : exactSites[3886]? = some site3886 := by rfl
private def site3887 : Site := ⟨[true,false,true,false,true,true,true,false,true,false,false],.dec 2⟩
private theorem lookup3887 : exactSites[3887]? = some site3887 := by rfl
private def site3888 : Site := ⟨[true,false,true,false,true,true,true,false,true,false,true,false],.inc 1⟩
private theorem lookup3888 : exactSites[3888]? = some site3888 := by rfl
private def site3889 : Site := ⟨[true,false,true,false,true,true,true,false,true,false,true,true],.continueTo 2⟩
private theorem lookup3889 : exactSites[3889]? = some site3889 := by rfl
private def site3890 : Site := ⟨[true,false,true,false,true,true,true,false,true,true,false,false,false],.dec 1⟩
private theorem lookup3890 : exactSites[3890]? = some site3890 := by rfl
private def site3891 : Site := ⟨[true,false,true,false,true,true,true,false,true,true,false,false,true,false],.inc 7⟩
private theorem lookup3891 : exactSites[3891]? = some site3891 := by rfl
private def site3892 : Site := ⟨[true,false,true,false,true,true,true,false,true,true,false,false,true,true,false],.inc 6⟩
private theorem lookup3892 : exactSites[3892]? = some site3892 := by rfl
private def site3893 : Site := ⟨[true,false,true,false,true,true,true,false,true,true,false,false,true,true,true],.continueTo 3⟩
private theorem lookup3893 : exactSites[3893]? = some site3893 := by rfl
private def site3894 : Site := ⟨[true,false,true,false,true,true,true,false,true,true,false,true,false],.dec 6⟩
private theorem lookup3894 : exactSites[3894]? = some site3894 := by rfl
private def site3895 : Site := ⟨[true,false,true,false,true,true,true,false,true,true,false,true,true,false,false],.inc 7⟩
private theorem lookup3895 : exactSites[3895]? = some site3895 := by rfl
private def site3896 : Site := ⟨[true,false,true,false,true,true,true,false,true,true,false,true,true,false,true,false],.dec 6⟩
private theorem lookup3896 : exactSites[3896]? = some site3896 := by rfl
private def site3897 : Site := ⟨[true,false,true,false,true,true,true,false,true,true,false,true,true,false,true,true,false],.inc 1⟩
private theorem lookup3897 : exactSites[3897]? = some site3897 := by rfl
private def site3898 : Site := ⟨[true,false,true,false,true,true,true,false,true,true,false,true,true,false,true,true,true],.continueTo 2⟩
private theorem lookup3898 : exactSites[3898]? = some site3898 := by rfl
private def site3899 : Site := ⟨[true,false,true,false,true,true,true,false,true,true,false,true,true,true],.continueTo 3⟩
private theorem lookup3899 : exactSites[3899]? = some site3899 := by rfl
private def site3900 : Site := ⟨[true,false,true,false,true,true,true,false,true,true,true,false],.dec 7⟩
private theorem lookup3900 : exactSites[3900]? = some site3900 := by rfl
private def site3901 : Site := ⟨[true,false,true,false,true,true,true,false,true,true,true,true,false],.inc 2⟩
private theorem lookup3901 : exactSites[3901]? = some site3901 := by rfl
private def site3902 : Site := ⟨[true,false,true,false,true,true,true,false,true,true,true,true,true],.continueTo 2⟩
private theorem lookup3902 : exactSites[3902]? = some site3902 := by rfl
private def site3903 : Site := ⟨[true,false,true,false,true,true,true,true,false,false],.dec 4⟩
private theorem lookup3903 : exactSites[3903]? = some site3903 := by rfl
private def site3904 : Site := ⟨[true,false,true,false,true,true,true,true,false,true,false],.inc 1⟩
private theorem lookup3904 : exactSites[3904]? = some site3904 := by rfl
private def site3905 : Site := ⟨[true,false,true,false,true,true,true,true,false,true,true,false],.inc 6⟩
private theorem lookup3905 : exactSites[3905]? = some site3905 := by rfl
private def site3906 : Site := ⟨[true,false,true,false,true,true,true,true,false,true,true,true],.continueTo 3⟩
private theorem lookup3906 : exactSites[3906]? = some site3906 := by rfl
private def site3907 : Site := ⟨[true,false,true,false,true,true,true,true,true,false],.dec 6⟩
private theorem lookup3907 : exactSites[3907]? = some site3907 := by rfl
private def site3908 : Site := ⟨[true,false,true,false,true,true,true,true,true,true,false],.inc 4⟩
private theorem lookup3908 : exactSites[3908]? = some site3908 := by rfl
private def site3909 : Site := ⟨[true,false,true,false,true,true,true,true,true,true,true],.continueTo 2⟩
private theorem lookup3909 : exactSites[3909]? = some site3909 := by rfl
private def site3910 : Site := ⟨[true,false,true,true],.continueTo 3⟩
private theorem lookup3910 : exactSites[3910]? = some site3910 := by rfl
private def site3911 : Site := ⟨[true,true,false,false],.dec 1⟩
private theorem lookup3911 : exactSites[3911]? = some site3911 := by rfl
private def site3912 : Site := ⟨[true,true,false,true,false],.inc 6⟩
private theorem lookup3912 : exactSites[3912]? = some site3912 := by rfl
private def site3913 : Site := ⟨[true,true,false,true,true],.continueTo 2⟩
private theorem lookup3913 : exactSites[3913]? = some site3913 := by rfl
private def site3914 : Site := ⟨[true,true,true,false,false,false],.dec 5⟩
private theorem lookup3914 : exactSites[3914]? = some site3914 := by rfl
private def site3915 : Site := ⟨[true,true,true,false,false,true,false],.inc 1⟩
private theorem lookup3915 : exactSites[3915]? = some site3915 := by rfl
private def site3916 : Site := ⟨[true,true,true,false,false,true,true,false],.inc 6⟩
private theorem lookup3916 : exactSites[3916]? = some site3916 := by rfl
private def site3917 : Site := ⟨[true,true,true,false,false,true,true,true],.continueTo 3⟩
private theorem lookup3917 : exactSites[3917]? = some site3917 := by rfl
private def site3918 : Site := ⟨[true,true,true,false,true,false],.dec 6⟩
private theorem lookup3918 : exactSites[3918]? = some site3918 := by rfl
private def site3919 : Site := ⟨[true,true,true,false,true,true,false],.inc 5⟩
private theorem lookup3919 : exactSites[3919]? = some site3919 := by rfl
private def site3920 : Site := ⟨[true,true,true,false,true,true,true],.continueTo 2⟩
private theorem lookup3920 : exactSites[3920]? = some site3920 := by rfl
private def site3921 : Site := ⟨[true,true,true,true,false],.inc 6⟩
private theorem lookup3921 : exactSites[3921]? = some site3921 := by rfl
private def site3922 : Site := ⟨[true,true,true,true,true,false,false,false,false,false],.dec 5⟩
private theorem lookup3922 : exactSites[3922]? = some site3922 := by rfl
private def site3923 : Site := ⟨[true,true,true,true,true,false,false,false,false,true,false,false],.dec 6⟩
private theorem lookup3923 : exactSites[3923]? = some site3923 := by rfl
private def site3924 : Site := ⟨[true,true,true,true,true,false,false,false,false,true,false,true],.continueTo 2⟩
private theorem lookup3924 : exactSites[3924]? = some site3924 := by rfl
private def site3925 : Site := ⟨[true,true,true,true,true,false,false,false,false,true,true],.breakTo 1⟩
private theorem lookup3925 : exactSites[3925]? = some site3925 := by rfl
private def site3926 : Site := ⟨[true,true,true,true,true,false,false,false,true],.dec 6⟩
private theorem lookup3926 : exactSites[3926]? = some site3926 := by rfl
private def site3927 : Site := ⟨[true,true,true,true,true,false,false,true,false,false],.dec 5⟩
private theorem lookup3927 : exactSites[3927]? = some site3927 := by rfl
private def site3928 : Site := ⟨[true,true,true,true,true,false,false,true,false,true],.continueTo 1⟩
private theorem lookup3928 : exactSites[3928]? = some site3928 := by rfl
private def site3929 : Site := ⟨[true,true,true,true,true,false,false,true,true,false,false],.dec 6⟩
private theorem lookup3929 : exactSites[3929]? = some site3929 := by rfl
private def site3930 : Site := ⟨[true,true,true,true,true,false,false,true,true,false,true],.continueTo 2⟩
private theorem lookup3930 : exactSites[3930]? = some site3930 := by rfl
private def site3931 : Site := ⟨[true,true,true,true,true,false,false,true,true,true],.breakTo 1⟩
private theorem lookup3931 : exactSites[3931]? = some site3931 := by rfl
private def site3932 : Site := ⟨[true,true,true,true,true,false,true],.halt⟩
private theorem lookup3932 : exactSites[3932]? = some site3932 := by rfl
private def site3933 : Site := ⟨[true,true,true,true,true,true,false,false,false],.dec 2⟩
private theorem lookup3933 : exactSites[3933]? = some site3933 := by rfl
private def site3934 : Site := ⟨[true,true,true,true,true,true,false,false,true,false],.inc 7⟩
private theorem lookup3934 : exactSites[3934]? = some site3934 := by rfl
private def site3935 : Site := ⟨[true,true,true,true,true,true,false,false,true,true,false,false,false],.dec 6⟩
private theorem lookup3935 : exactSites[3935]? = some site3935 := by rfl
private def raw0 := PA215.Census.C039.records[0]'(by decide)
private theorem row0 : recordAgrees raw0 = true := by
  unfold recordAgrees
  rw [show raw0.siteIndex = 3841 from rfl,lookup3841]
  decide
private def raw1 := PA215.Census.C039.records[1]'(by decide)
private theorem row1 : recordAgrees raw1 = true := by
  unfold recordAgrees
  rw [show raw1.siteIndex = 3841 from rfl,lookup3841]
  decide
private def raw2 := PA215.Census.C039.records[2]'(by decide)
private theorem row2 : recordAgrees raw2 = true := by
  unfold recordAgrees
  rw [show raw2.siteIndex = 3842 from rfl,lookup3842]
  decide
private def raw3 := PA215.Census.C039.records[3]'(by decide)
private theorem row3 : recordAgrees raw3 = true := by
  unfold recordAgrees
  rw [show raw3.siteIndex = 3843 from rfl,lookup3843]
  decide
private def raw4 := PA215.Census.C039.records[4]'(by decide)
private theorem row4 : recordAgrees raw4 = true := by
  unfold recordAgrees
  rw [show raw4.siteIndex = 3844 from rfl,lookup3844]
  decide
private def raw5 := PA215.Census.C039.records[5]'(by decide)
private theorem row5 : recordAgrees raw5 = true := by
  unfold recordAgrees
  rw [show raw5.siteIndex = 3844 from rfl,lookup3844]
  decide
private def raw6 := PA215.Census.C039.records[6]'(by decide)
private theorem row6 : recordAgrees raw6 = true := by
  unfold recordAgrees
  rw [show raw6.siteIndex = 3845 from rfl,lookup3845]
  decide
private def raw7 := PA215.Census.C039.records[7]'(by decide)
private theorem row7 : recordAgrees raw7 = true := by
  unfold recordAgrees
  rw [show raw7.siteIndex = 3846 from rfl,lookup3846]
  decide
private def raw8 := PA215.Census.C039.records[8]'(by decide)
private theorem row8 : recordAgrees raw8 = true := by
  unfold recordAgrees
  rw [show raw8.siteIndex = 3846 from rfl,lookup3846]
  decide
private def raw9 := PA215.Census.C039.records[9]'(by decide)
private theorem row9 : recordAgrees raw9 = true := by
  unfold recordAgrees
  rw [show raw9.siteIndex = 3847 from rfl,lookup3847]
  decide
private def raw10 := PA215.Census.C039.records[10]'(by decide)
private theorem row10 : recordAgrees raw10 = true := by
  unfold recordAgrees
  rw [show raw10.siteIndex = 3848 from rfl,lookup3848]
  decide
private def raw11 := PA215.Census.C039.records[11]'(by decide)
private theorem row11 : recordAgrees raw11 = true := by
  unfold recordAgrees
  rw [show raw11.siteIndex = 3848 from rfl,lookup3848]
  decide
private def raw12 := PA215.Census.C039.records[12]'(by decide)
private theorem row12 : recordAgrees raw12 = true := by
  unfold recordAgrees
  rw [show raw12.siteIndex = 3849 from rfl,lookup3849]
  decide
private def raw13 := PA215.Census.C039.records[13]'(by decide)
private theorem row13 : recordAgrees raw13 = true := by
  unfold recordAgrees
  rw [show raw13.siteIndex = 3850 from rfl,lookup3850]
  decide
private def raw14 := PA215.Census.C039.records[14]'(by decide)
private theorem row14 : recordAgrees raw14 = true := by
  unfold recordAgrees
  rw [show raw14.siteIndex = 3851 from rfl,lookup3851]
  decide
private def raw15 := PA215.Census.C039.records[15]'(by decide)
private theorem row15 : recordAgrees raw15 = true := by
  unfold recordAgrees
  rw [show raw15.siteIndex = 3852 from rfl,lookup3852]
  decide
private def raw16 := PA215.Census.C039.records[16]'(by decide)
private theorem row16 : recordAgrees raw16 = true := by
  unfold recordAgrees
  rw [show raw16.siteIndex = 3852 from rfl,lookup3852]
  decide
private def raw17 := PA215.Census.C039.records[17]'(by decide)
private theorem row17 : recordAgrees raw17 = true := by
  unfold recordAgrees
  rw [show raw17.siteIndex = 3853 from rfl,lookup3853]
  decide
private def raw18 := PA215.Census.C039.records[18]'(by decide)
private theorem row18 : recordAgrees raw18 = true := by
  unfold recordAgrees
  rw [show raw18.siteIndex = 3854 from rfl,lookup3854]
  decide
private def raw19 := PA215.Census.C039.records[19]'(by decide)
private theorem row19 : recordAgrees raw19 = true := by
  unfold recordAgrees
  rw [show raw19.siteIndex = 3855 from rfl,lookup3855]
  decide
private def raw20 := PA215.Census.C039.records[20]'(by decide)
private theorem row20 : recordAgrees raw20 = true := by
  unfold recordAgrees
  rw [show raw20.siteIndex = 3855 from rfl,lookup3855]
  decide
private def raw21 := PA215.Census.C039.records[21]'(by decide)
private theorem row21 : recordAgrees raw21 = true := by
  unfold recordAgrees
  rw [show raw21.siteIndex = 3856 from rfl,lookup3856]
  decide
private def raw22 := PA215.Census.C039.records[22]'(by decide)
private theorem row22 : recordAgrees raw22 = true := by
  unfold recordAgrees
  rw [show raw22.siteIndex = 3857 from rfl,lookup3857]
  decide
private def raw23 := PA215.Census.C039.records[23]'(by decide)
private theorem row23 : recordAgrees raw23 = true := by
  unfold recordAgrees
  rw [show raw23.siteIndex = 3858 from rfl,lookup3858]
  decide
private def raw24 := PA215.Census.C039.records[24]'(by decide)
private theorem row24 : recordAgrees raw24 = true := by
  unfold recordAgrees
  rw [show raw24.siteIndex = 3859 from rfl,lookup3859]
  decide
private def raw25 := PA215.Census.C039.records[25]'(by decide)
private theorem row25 : recordAgrees raw25 = true := by
  unfold recordAgrees
  rw [show raw25.siteIndex = 3859 from rfl,lookup3859]
  decide
private def raw26 := PA215.Census.C039.records[26]'(by decide)
private theorem row26 : recordAgrees raw26 = true := by
  unfold recordAgrees
  rw [show raw26.siteIndex = 3860 from rfl,lookup3860]
  decide
private def raw27 := PA215.Census.C039.records[27]'(by decide)
private theorem row27 : recordAgrees raw27 = true := by
  unfold recordAgrees
  rw [show raw27.siteIndex = 3861 from rfl,lookup3861]
  decide
private def raw28 := PA215.Census.C039.records[28]'(by decide)
private theorem row28 : recordAgrees raw28 = true := by
  unfold recordAgrees
  rw [show raw28.siteIndex = 3861 from rfl,lookup3861]
  decide
private def raw29 := PA215.Census.C039.records[29]'(by decide)
private theorem row29 : recordAgrees raw29 = true := by
  unfold recordAgrees
  rw [show raw29.siteIndex = 3862 from rfl,lookup3862]
  decide
private def raw30 := PA215.Census.C039.records[30]'(by decide)
private theorem row30 : recordAgrees raw30 = true := by
  unfold recordAgrees
  rw [show raw30.siteIndex = 3863 from rfl,lookup3863]
  decide
private def raw31 := PA215.Census.C039.records[31]'(by decide)
private theorem row31 : recordAgrees raw31 = true := by
  unfold recordAgrees
  rw [show raw31.siteIndex = 3864 from rfl,lookup3864]
  decide
private def raw32 := PA215.Census.C039.records[32]'(by decide)
private theorem row32 : recordAgrees raw32 = true := by
  unfold recordAgrees
  rw [show raw32.siteIndex = 3865 from rfl,lookup3865]
  decide
private def raw33 := PA215.Census.C039.records[33]'(by decide)
private theorem row33 : recordAgrees raw33 = true := by
  unfold recordAgrees
  rw [show raw33.siteIndex = 3865 from rfl,lookup3865]
  decide
private def raw34 := PA215.Census.C039.records[34]'(by decide)
private theorem row34 : recordAgrees raw34 = true := by
  unfold recordAgrees
  rw [show raw34.siteIndex = 3866 from rfl,lookup3866]
  decide
private def raw35 := PA215.Census.C039.records[35]'(by decide)
private theorem row35 : recordAgrees raw35 = true := by
  unfold recordAgrees
  rw [show raw35.siteIndex = 3867 from rfl,lookup3867]
  decide
private def raw36 := PA215.Census.C039.records[36]'(by decide)
private theorem row36 : recordAgrees raw36 = true := by
  unfold recordAgrees
  rw [show raw36.siteIndex = 3868 from rfl,lookup3868]
  decide
private def raw37 := PA215.Census.C039.records[37]'(by decide)
private theorem row37 : recordAgrees raw37 = true := by
  unfold recordAgrees
  rw [show raw37.siteIndex = 3869 from rfl,lookup3869]
  decide
private def raw38 := PA215.Census.C039.records[38]'(by decide)
private theorem row38 : recordAgrees raw38 = true := by
  unfold recordAgrees
  rw [show raw38.siteIndex = 3870 from rfl,lookup3870]
  decide
private def raw39 := PA215.Census.C039.records[39]'(by decide)
private theorem row39 : recordAgrees raw39 = true := by
  unfold recordAgrees
  rw [show raw39.siteIndex = 3871 from rfl,lookup3871]
  decide
private def raw40 := PA215.Census.C039.records[40]'(by decide)
private theorem row40 : recordAgrees raw40 = true := by
  unfold recordAgrees
  rw [show raw40.siteIndex = 3871 from rfl,lookup3871]
  decide
private def raw41 := PA215.Census.C039.records[41]'(by decide)
private theorem row41 : recordAgrees raw41 = true := by
  unfold recordAgrees
  rw [show raw41.siteIndex = 3872 from rfl,lookup3872]
  decide
private def raw42 := PA215.Census.C039.records[42]'(by decide)
private theorem row42 : recordAgrees raw42 = true := by
  unfold recordAgrees
  rw [show raw42.siteIndex = 3873 from rfl,lookup3873]
  decide
private def raw43 := PA215.Census.C039.records[43]'(by decide)
private theorem row43 : recordAgrees raw43 = true := by
  unfold recordAgrees
  rw [show raw43.siteIndex = 3874 from rfl,lookup3874]
  decide
private def raw44 := PA215.Census.C039.records[44]'(by decide)
private theorem row44 : recordAgrees raw44 = true := by
  unfold recordAgrees
  rw [show raw44.siteIndex = 3874 from rfl,lookup3874]
  decide
private def raw45 := PA215.Census.C039.records[45]'(by decide)
private theorem row45 : recordAgrees raw45 = true := by
  unfold recordAgrees
  rw [show raw45.siteIndex = 3875 from rfl,lookup3875]
  decide
private def raw46 := PA215.Census.C039.records[46]'(by decide)
private theorem row46 : recordAgrees raw46 = true := by
  unfold recordAgrees
  rw [show raw46.siteIndex = 3875 from rfl,lookup3875]
  decide
private def raw47 := PA215.Census.C039.records[47]'(by decide)
private theorem row47 : recordAgrees raw47 = true := by
  unfold recordAgrees
  rw [show raw47.siteIndex = 3876 from rfl,lookup3876]
  decide
private def raw48 := PA215.Census.C039.records[48]'(by decide)
private theorem row48 : recordAgrees raw48 = true := by
  unfold recordAgrees
  rw [show raw48.siteIndex = 3877 from rfl,lookup3877]
  decide
private def raw49 := PA215.Census.C039.records[49]'(by decide)
private theorem row49 : recordAgrees raw49 = true := by
  unfold recordAgrees
  rw [show raw49.siteIndex = 3878 from rfl,lookup3878]
  decide
private def raw50 := PA215.Census.C039.records[50]'(by decide)
private theorem row50 : recordAgrees raw50 = true := by
  unfold recordAgrees
  rw [show raw50.siteIndex = 3878 from rfl,lookup3878]
  decide
private def raw51 := PA215.Census.C039.records[51]'(by decide)
private theorem row51 : recordAgrees raw51 = true := by
  unfold recordAgrees
  rw [show raw51.siteIndex = 3879 from rfl,lookup3879]
  decide
private def raw52 := PA215.Census.C039.records[52]'(by decide)
private theorem row52 : recordAgrees raw52 = true := by
  unfold recordAgrees
  rw [show raw52.siteIndex = 3879 from rfl,lookup3879]
  decide
private def raw53 := PA215.Census.C039.records[53]'(by decide)
private theorem row53 : recordAgrees raw53 = true := by
  unfold recordAgrees
  rw [show raw53.siteIndex = 3880 from rfl,lookup3880]
  decide
private def raw54 := PA215.Census.C039.records[54]'(by decide)
private theorem row54 : recordAgrees raw54 = true := by
  unfold recordAgrees
  rw [show raw54.siteIndex = 3881 from rfl,lookup3881]
  decide
private def raw55 := PA215.Census.C039.records[55]'(by decide)
private theorem row55 : recordAgrees raw55 = true := by
  unfold recordAgrees
  rw [show raw55.siteIndex = 3881 from rfl,lookup3881]
  decide
private def raw56 := PA215.Census.C039.records[56]'(by decide)
private theorem row56 : recordAgrees raw56 = true := by
  unfold recordAgrees
  rw [show raw56.siteIndex = 3882 from rfl,lookup3882]
  decide
private def raw57 := PA215.Census.C039.records[57]'(by decide)
private theorem row57 : recordAgrees raw57 = true := by
  unfold recordAgrees
  rw [show raw57.siteIndex = 3883 from rfl,lookup3883]
  decide
private def raw58 := PA215.Census.C039.records[58]'(by decide)
private theorem row58 : recordAgrees raw58 = true := by
  unfold recordAgrees
  rw [show raw58.siteIndex = 3884 from rfl,lookup3884]
  decide
private def raw59 := PA215.Census.C039.records[59]'(by decide)
private theorem row59 : recordAgrees raw59 = true := by
  unfold recordAgrees
  rw [show raw59.siteIndex = 3884 from rfl,lookup3884]
  decide
private def raw60 := PA215.Census.C039.records[60]'(by decide)
private theorem row60 : recordAgrees raw60 = true := by
  unfold recordAgrees
  rw [show raw60.siteIndex = 3885 from rfl,lookup3885]
  decide
private def raw61 := PA215.Census.C039.records[61]'(by decide)
private theorem row61 : recordAgrees raw61 = true := by
  unfold recordAgrees
  rw [show raw61.siteIndex = 3886 from rfl,lookup3886]
  decide
private def raw62 := PA215.Census.C039.records[62]'(by decide)
private theorem row62 : recordAgrees raw62 = true := by
  unfold recordAgrees
  rw [show raw62.siteIndex = 3887 from rfl,lookup3887]
  decide
private def raw63 := PA215.Census.C039.records[63]'(by decide)
private theorem row63 : recordAgrees raw63 = true := by
  unfold recordAgrees
  rw [show raw63.siteIndex = 3887 from rfl,lookup3887]
  decide
private def raw64 := PA215.Census.C039.records[64]'(by decide)
private theorem row64 : recordAgrees raw64 = true := by
  unfold recordAgrees
  rw [show raw64.siteIndex = 3888 from rfl,lookup3888]
  decide
private def raw65 := PA215.Census.C039.records[65]'(by decide)
private theorem row65 : recordAgrees raw65 = true := by
  unfold recordAgrees
  rw [show raw65.siteIndex = 3889 from rfl,lookup3889]
  decide
private def raw66 := PA215.Census.C039.records[66]'(by decide)
private theorem row66 : recordAgrees raw66 = true := by
  unfold recordAgrees
  rw [show raw66.siteIndex = 3890 from rfl,lookup3890]
  decide
private def raw67 := PA215.Census.C039.records[67]'(by decide)
private theorem row67 : recordAgrees raw67 = true := by
  unfold recordAgrees
  rw [show raw67.siteIndex = 3890 from rfl,lookup3890]
  decide
private def raw68 := PA215.Census.C039.records[68]'(by decide)
private theorem row68 : recordAgrees raw68 = true := by
  unfold recordAgrees
  rw [show raw68.siteIndex = 3891 from rfl,lookup3891]
  decide
private def raw69 := PA215.Census.C039.records[69]'(by decide)
private theorem row69 : recordAgrees raw69 = true := by
  unfold recordAgrees
  rw [show raw69.siteIndex = 3892 from rfl,lookup3892]
  decide
private def raw70 := PA215.Census.C039.records[70]'(by decide)
private theorem row70 : recordAgrees raw70 = true := by
  unfold recordAgrees
  rw [show raw70.siteIndex = 3893 from rfl,lookup3893]
  decide
private def raw71 := PA215.Census.C039.records[71]'(by decide)
private theorem row71 : recordAgrees raw71 = true := by
  unfold recordAgrees
  rw [show raw71.siteIndex = 3894 from rfl,lookup3894]
  decide
private def raw72 := PA215.Census.C039.records[72]'(by decide)
private theorem row72 : recordAgrees raw72 = true := by
  unfold recordAgrees
  rw [show raw72.siteIndex = 3894 from rfl,lookup3894]
  decide
private def raw73 := PA215.Census.C039.records[73]'(by decide)
private theorem row73 : recordAgrees raw73 = true := by
  unfold recordAgrees
  rw [show raw73.siteIndex = 3895 from rfl,lookup3895]
  decide
private def raw74 := PA215.Census.C039.records[74]'(by decide)
private theorem row74 : recordAgrees raw74 = true := by
  unfold recordAgrees
  rw [show raw74.siteIndex = 3896 from rfl,lookup3896]
  decide
private def raw75 := PA215.Census.C039.records[75]'(by decide)
private theorem row75 : recordAgrees raw75 = true := by
  unfold recordAgrees
  rw [show raw75.siteIndex = 3896 from rfl,lookup3896]
  decide
private def raw76 := PA215.Census.C039.records[76]'(by decide)
private theorem row76 : recordAgrees raw76 = true := by
  unfold recordAgrees
  rw [show raw76.siteIndex = 3897 from rfl,lookup3897]
  decide
private def raw77 := PA215.Census.C039.records[77]'(by decide)
private theorem row77 : recordAgrees raw77 = true := by
  unfold recordAgrees
  rw [show raw77.siteIndex = 3898 from rfl,lookup3898]
  decide
private def raw78 := PA215.Census.C039.records[78]'(by decide)
private theorem row78 : recordAgrees raw78 = true := by
  unfold recordAgrees
  rw [show raw78.siteIndex = 3899 from rfl,lookup3899]
  decide
private def raw79 := PA215.Census.C039.records[79]'(by decide)
private theorem row79 : recordAgrees raw79 = true := by
  unfold recordAgrees
  rw [show raw79.siteIndex = 3900 from rfl,lookup3900]
  decide
private def raw80 := PA215.Census.C039.records[80]'(by decide)
private theorem row80 : recordAgrees raw80 = true := by
  unfold recordAgrees
  rw [show raw80.siteIndex = 3900 from rfl,lookup3900]
  decide
private def raw81 := PA215.Census.C039.records[81]'(by decide)
private theorem row81 : recordAgrees raw81 = true := by
  unfold recordAgrees
  rw [show raw81.siteIndex = 3901 from rfl,lookup3901]
  decide
private def raw82 := PA215.Census.C039.records[82]'(by decide)
private theorem row82 : recordAgrees raw82 = true := by
  unfold recordAgrees
  rw [show raw82.siteIndex = 3902 from rfl,lookup3902]
  decide
private def raw83 := PA215.Census.C039.records[83]'(by decide)
private theorem row83 : recordAgrees raw83 = true := by
  unfold recordAgrees
  rw [show raw83.siteIndex = 3903 from rfl,lookup3903]
  decide
private def raw84 := PA215.Census.C039.records[84]'(by decide)
private theorem row84 : recordAgrees raw84 = true := by
  unfold recordAgrees
  rw [show raw84.siteIndex = 3903 from rfl,lookup3903]
  decide
private def raw85 := PA215.Census.C039.records[85]'(by decide)
private theorem row85 : recordAgrees raw85 = true := by
  unfold recordAgrees
  rw [show raw85.siteIndex = 3904 from rfl,lookup3904]
  decide
private def raw86 := PA215.Census.C039.records[86]'(by decide)
private theorem row86 : recordAgrees raw86 = true := by
  unfold recordAgrees
  rw [show raw86.siteIndex = 3905 from rfl,lookup3905]
  decide
private def raw87 := PA215.Census.C039.records[87]'(by decide)
private theorem row87 : recordAgrees raw87 = true := by
  unfold recordAgrees
  rw [show raw87.siteIndex = 3906 from rfl,lookup3906]
  decide
private def raw88 := PA215.Census.C039.records[88]'(by decide)
private theorem row88 : recordAgrees raw88 = true := by
  unfold recordAgrees
  rw [show raw88.siteIndex = 3907 from rfl,lookup3907]
  decide
private def raw89 := PA215.Census.C039.records[89]'(by decide)
private theorem row89 : recordAgrees raw89 = true := by
  unfold recordAgrees
  rw [show raw89.siteIndex = 3907 from rfl,lookup3907]
  decide
private def raw90 := PA215.Census.C039.records[90]'(by decide)
private theorem row90 : recordAgrees raw90 = true := by
  unfold recordAgrees
  rw [show raw90.siteIndex = 3908 from rfl,lookup3908]
  decide
private def raw91 := PA215.Census.C039.records[91]'(by decide)
private theorem row91 : recordAgrees raw91 = true := by
  unfold recordAgrees
  rw [show raw91.siteIndex = 3909 from rfl,lookup3909]
  decide
private def raw92 := PA215.Census.C039.records[92]'(by decide)
private theorem row92 : recordAgrees raw92 = true := by
  unfold recordAgrees
  rw [show raw92.siteIndex = 3910 from rfl,lookup3910]
  decide
private def raw93 := PA215.Census.C039.records[93]'(by decide)
private theorem row93 : recordAgrees raw93 = true := by
  unfold recordAgrees
  rw [show raw93.siteIndex = 3911 from rfl,lookup3911]
  decide
private def raw94 := PA215.Census.C039.records[94]'(by decide)
private theorem row94 : recordAgrees raw94 = true := by
  unfold recordAgrees
  rw [show raw94.siteIndex = 3911 from rfl,lookup3911]
  decide
private def raw95 := PA215.Census.C039.records[95]'(by decide)
private theorem row95 : recordAgrees raw95 = true := by
  unfold recordAgrees
  rw [show raw95.siteIndex = 3912 from rfl,lookup3912]
  decide
private def raw96 := PA215.Census.C039.records[96]'(by decide)
private theorem row96 : recordAgrees raw96 = true := by
  unfold recordAgrees
  rw [show raw96.siteIndex = 3913 from rfl,lookup3913]
  decide
private def raw97 := PA215.Census.C039.records[97]'(by decide)
private theorem row97 : recordAgrees raw97 = true := by
  unfold recordAgrees
  rw [show raw97.siteIndex = 3914 from rfl,lookup3914]
  decide
private def raw98 := PA215.Census.C039.records[98]'(by decide)
private theorem row98 : recordAgrees raw98 = true := by
  unfold recordAgrees
  rw [show raw98.siteIndex = 3914 from rfl,lookup3914]
  decide
private def raw99 := PA215.Census.C039.records[99]'(by decide)
private theorem row99 : recordAgrees raw99 = true := by
  unfold recordAgrees
  rw [show raw99.siteIndex = 3915 from rfl,lookup3915]
  decide
private def raw100 := PA215.Census.C039.records[100]'(by decide)
private theorem row100 : recordAgrees raw100 = true := by
  unfold recordAgrees
  rw [show raw100.siteIndex = 3916 from rfl,lookup3916]
  decide
private def raw101 := PA215.Census.C039.records[101]'(by decide)
private theorem row101 : recordAgrees raw101 = true := by
  unfold recordAgrees
  rw [show raw101.siteIndex = 3917 from rfl,lookup3917]
  decide
private def raw102 := PA215.Census.C039.records[102]'(by decide)
private theorem row102 : recordAgrees raw102 = true := by
  unfold recordAgrees
  rw [show raw102.siteIndex = 3918 from rfl,lookup3918]
  decide
private def raw103 := PA215.Census.C039.records[103]'(by decide)
private theorem row103 : recordAgrees raw103 = true := by
  unfold recordAgrees
  rw [show raw103.siteIndex = 3918 from rfl,lookup3918]
  decide
private def raw104 := PA215.Census.C039.records[104]'(by decide)
private theorem row104 : recordAgrees raw104 = true := by
  unfold recordAgrees
  rw [show raw104.siteIndex = 3919 from rfl,lookup3919]
  decide
private def raw105 := PA215.Census.C039.records[105]'(by decide)
private theorem row105 : recordAgrees raw105 = true := by
  unfold recordAgrees
  rw [show raw105.siteIndex = 3920 from rfl,lookup3920]
  decide
private def raw106 := PA215.Census.C039.records[106]'(by decide)
private theorem row106 : recordAgrees raw106 = true := by
  unfold recordAgrees
  rw [show raw106.siteIndex = 3921 from rfl,lookup3921]
  decide
private def raw107 := PA215.Census.C039.records[107]'(by decide)
private theorem row107 : recordAgrees raw107 = true := by
  unfold recordAgrees
  rw [show raw107.siteIndex = 3922 from rfl,lookup3922]
  decide
private def raw108 := PA215.Census.C039.records[108]'(by decide)
private theorem row108 : recordAgrees raw108 = true := by
  unfold recordAgrees
  rw [show raw108.siteIndex = 3922 from rfl,lookup3922]
  decide
private def raw109 := PA215.Census.C039.records[109]'(by decide)
private theorem row109 : recordAgrees raw109 = true := by
  unfold recordAgrees
  rw [show raw109.siteIndex = 3923 from rfl,lookup3923]
  decide
private def raw110 := PA215.Census.C039.records[110]'(by decide)
private theorem row110 : recordAgrees raw110 = true := by
  unfold recordAgrees
  rw [show raw110.siteIndex = 3923 from rfl,lookup3923]
  decide
private def raw111 := PA215.Census.C039.records[111]'(by decide)
private theorem row111 : recordAgrees raw111 = true := by
  unfold recordAgrees
  rw [show raw111.siteIndex = 3924 from rfl,lookup3924]
  decide
private def raw112 := PA215.Census.C039.records[112]'(by decide)
private theorem row112 : recordAgrees raw112 = true := by
  unfold recordAgrees
  rw [show raw112.siteIndex = 3925 from rfl,lookup3925]
  decide
private def raw113 := PA215.Census.C039.records[113]'(by decide)
private theorem row113 : recordAgrees raw113 = true := by
  unfold recordAgrees
  rw [show raw113.siteIndex = 3926 from rfl,lookup3926]
  decide
private def raw114 := PA215.Census.C039.records[114]'(by decide)
private theorem row114 : recordAgrees raw114 = true := by
  unfold recordAgrees
  rw [show raw114.siteIndex = 3926 from rfl,lookup3926]
  decide
private def raw115 := PA215.Census.C039.records[115]'(by decide)
private theorem row115 : recordAgrees raw115 = true := by
  unfold recordAgrees
  rw [show raw115.siteIndex = 3927 from rfl,lookup3927]
  decide
private def raw116 := PA215.Census.C039.records[116]'(by decide)
private theorem row116 : recordAgrees raw116 = true := by
  unfold recordAgrees
  rw [show raw116.siteIndex = 3927 from rfl,lookup3927]
  decide
private def raw117 := PA215.Census.C039.records[117]'(by decide)
private theorem row117 : recordAgrees raw117 = true := by
  unfold recordAgrees
  rw [show raw117.siteIndex = 3928 from rfl,lookup3928]
  decide
private def raw118 := PA215.Census.C039.records[118]'(by decide)
private theorem row118 : recordAgrees raw118 = true := by
  unfold recordAgrees
  rw [show raw118.siteIndex = 3929 from rfl,lookup3929]
  decide
private def raw119 := PA215.Census.C039.records[119]'(by decide)
private theorem row119 : recordAgrees raw119 = true := by
  unfold recordAgrees
  rw [show raw119.siteIndex = 3929 from rfl,lookup3929]
  decide
private def raw120 := PA215.Census.C039.records[120]'(by decide)
private theorem row120 : recordAgrees raw120 = true := by
  unfold recordAgrees
  rw [show raw120.siteIndex = 3930 from rfl,lookup3930]
  decide
private def raw121 := PA215.Census.C039.records[121]'(by decide)
private theorem row121 : recordAgrees raw121 = true := by
  unfold recordAgrees
  rw [show raw121.siteIndex = 3931 from rfl,lookup3931]
  decide
private def raw122 := PA215.Census.C039.records[122]'(by decide)
private theorem row122 : recordAgrees raw122 = true := by
  unfold recordAgrees
  rw [show raw122.siteIndex = 3932 from rfl,lookup3932]
  decide
private def raw123 := PA215.Census.C039.records[123]'(by decide)
private theorem row123 : recordAgrees raw123 = true := by
  unfold recordAgrees
  rw [show raw123.siteIndex = 3933 from rfl,lookup3933]
  decide
private def raw124 := PA215.Census.C039.records[124]'(by decide)
private theorem row124 : recordAgrees raw124 = true := by
  unfold recordAgrees
  rw [show raw124.siteIndex = 3933 from rfl,lookup3933]
  decide
private def raw125 := PA215.Census.C039.records[125]'(by decide)
private theorem row125 : recordAgrees raw125 = true := by
  unfold recordAgrees
  rw [show raw125.siteIndex = 3934 from rfl,lookup3934]
  decide
private def raw126 := PA215.Census.C039.records[126]'(by decide)
private theorem row126 : recordAgrees raw126 = true := by
  unfold recordAgrees
  rw [show raw126.siteIndex = 3935 from rfl,lookup3935]
  decide
private def raw127 := PA215.Census.C039.records[127]'(by decide)
private theorem row127 : recordAgrees raw127 = true := by
  unfold recordAgrees
  rw [show raw127.siteIndex = 3935 from rfl,lookup3935]
  decide
private theorem enumeration : PA215.Census.C039.records.toList = [raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7,raw8,raw9,raw10,raw11,raw12,raw13,raw14,raw15,raw16,raw17,raw18,raw19,raw20,raw21,raw22,raw23,raw24,raw25,raw26,raw27,raw28,raw29,raw30,raw31,raw32,raw33,raw34,raw35,raw36,raw37,raw38,raw39,raw40,raw41,raw42,raw43,raw44,raw45,raw46,raw47,raw48,raw49,raw50,raw51,raw52,raw53,raw54,raw55,raw56,raw57,raw58,raw59,raw60,raw61,raw62,raw63,raw64,raw65,raw66,raw67,raw68,raw69,raw70,raw71,raw72,raw73,raw74,raw75,raw76,raw77,raw78,raw79,raw80,raw81,raw82,raw83,raw84,raw85,raw86,raw87,raw88,raw89,raw90,raw91,raw92,raw93,raw94,raw95,raw96,raw97,raw98,raw99,raw100,raw101,raw102,raw103,raw104,raw105,raw106,raw107,raw108,raw109,raw110,raw111,raw112,raw113,raw114,raw115,raw116,raw117,raw118,raw119,raw120,raw121,raw122,raw123,raw124,raw125,raw126,raw127] := by rfl
theorem checked : PA215.Census.C039.records.toList.all recordAgrees = true := by
  rw [enumeration]
  simp only [List.all_cons,List.all_nil,row0,row1,row2,row3,row4,row5,row6,row7,row8,row9,row10,row11,row12,row13,row14,row15,row16,row17,row18,row19,row20,row21,row22,row23,row24,row25,row26,row27,row28,row29,row30,row31,row32,row33,row34,row35,row36,row37,row38,row39,row40,row41,row42,row43,row44,row45,row46,row47,row48,row49,row50,row51,row52,row53,row54,row55,row56,row57,row58,row59,row60,row61,row62,row63,row64,row65,row66,row67,row68,row69,row70,row71,row72,row73,row74,row75,row76,row77,row78,row79,row80,row81,row82,row83,row84,row85,row86,row87,row88,row89,row90,row91,row92,row93,row94,row95,row96,row97,row98,row99,row100,row101,row102,row103,row104,row105,row106,row107,row108,row109,row110,row111,row112,row113,row114,row115,row116,row117,row118,row119,row120,row121,row122,row123,row124,row125,row126,row127,Bool.and_self]
#print axioms checked
end PA215.Source.CensusJoin.J039
