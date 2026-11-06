import PA215.Source.DestinationCertificate
import PA215.Census.C039
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA215.Source.DestinationJoin.D039
private def site0 : Site := ⟨[false,false,false,false],.dec 8⟩
private theorem lookup0 : exactSites[0]? = some site0 := by rfl
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
private def site3936 : Site := ⟨[true,true,true,true,true,true,false,false,true,true,false,false,true],.breakTo 1⟩
private theorem lookup3936 : exactSites[3936]? = some site3936 := by rfl
private def site3937 : Site := ⟨[true,true,true,true,true,true,false,false,true,true,false,true,false],.dec 7⟩
private theorem lookup3937 : exactSites[3937]? = some site3937 := by rfl
private def site3941 : Site := ⟨[true,true,true,true,true,true,false,true,false],.dec 7⟩
private theorem lookup3941 : exactSites[3941]? = some site3941 := by rfl
private def inst3841 : Instruction := .dec 6 (some 3844) (some 3842)
private theorem resolved3841 : resolveAt exactSites 3841 = some inst3841 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3841]
  rfl
private def inst3842 : Instruction := .inc 4 (some 3843)
private theorem resolved3842 : resolveAt exactSites 3842 = some inst3842 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3842]
  rfl
private def inst3843 : Instruction := .jump (some 3841)
private theorem resolved3843 : resolveAt exactSites 3843 = some inst3843 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3843]
  rfl
private def inst3844 : Instruction := .dec 2 (some 3852) (some 3845)
private theorem resolved3844 : resolveAt exactSites 3844 = some inst3844 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3844]
  rfl
private def inst3845 : Instruction := .inc 7 (some 3846)
private theorem resolved3845 : resolveAt exactSites 3845 = some inst3845 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3845]
  rfl
private def inst3846 : Instruction := .dec 6 (some 3848) (some 3847)
private theorem resolved3846 : resolveAt exactSites 3846 = some inst3846 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3846]
  rfl
private def inst3847 : Instruction := .jump (some 3851)
private theorem resolved3847 : resolveAt exactSites 3847 = some inst3847 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3847]
  rfl
private def inst3848 : Instruction := .dec 7 (some 3851) (some 3849)
private theorem resolved3848 : resolveAt exactSites 3848 = some inst3848 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3848]
  rfl
private def inst3849 : Instruction := .inc 6 (some 3850)
private theorem resolved3849 : resolveAt exactSites 3849 = some inst3849 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3849]
  rfl
private def inst3850 : Instruction := .jump (some 3848)
private theorem resolved3850 : resolveAt exactSites 3850 = some inst3850 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3850]
  rfl
private def inst3851 : Instruction := .jump (some 3844)
private theorem resolved3851 : resolveAt exactSites 3851 = some inst3851 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3851]
  rfl
private def inst3852 : Instruction := .dec 7 (some 3855) (some 3853)
private theorem resolved3852 : resolveAt exactSites 3852 = some inst3852 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3852]
  rfl
private def inst3853 : Instruction := .inc 2 (some 3854)
private theorem resolved3853 : resolveAt exactSites 3853 = some inst3853 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3853]
  rfl
private def inst3854 : Instruction := .jump (some 3852)
private theorem resolved3854 : resolveAt exactSites 3854 = some inst3854 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3854]
  rfl
private def inst3855 : Instruction := .dec 1 (some 3859) (some 3856)
private theorem resolved3855 : resolveAt exactSites 3855 = some inst3855 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3855]
  rfl
private def inst3856 : Instruction := .inc 7 (some 3857)
private theorem resolved3856 : resolveAt exactSites 3856 = some inst3856 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3856]
  rfl
private def inst3857 : Instruction := .inc 6 (some 3858)
private theorem resolved3857 : resolveAt exactSites 3857 = some inst3857 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3857]
  rfl
private def inst3858 : Instruction := .jump (some 3855)
private theorem resolved3858 : resolveAt exactSites 3858 = some inst3858 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3858]
  rfl
private def inst3859 : Instruction := .dec 6 (some 3865) (some 3860)
private theorem resolved3859 : resolveAt exactSites 3859 = some inst3859 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3859]
  rfl
private def inst3860 : Instruction := .inc 7 (some 3861)
private theorem resolved3860 : resolveAt exactSites 3860 = some inst3860 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3860]
  rfl
private def inst3861 : Instruction := .dec 6 (some 3864) (some 3862)
private theorem resolved3861 : resolveAt exactSites 3861 = some inst3861 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3861]
  rfl
private def inst3862 : Instruction := .inc 1 (some 3863)
private theorem resolved3862 : resolveAt exactSites 3862 = some inst3862 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3862]
  rfl
private def inst3863 : Instruction := .jump (some 3861)
private theorem resolved3863 : resolveAt exactSites 3863 = some inst3863 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3863]
  rfl
private def inst3864 : Instruction := .jump (some 3855)
private theorem resolved3864 : resolveAt exactSites 3864 = some inst3864 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3864]
  rfl
private def inst3865 : Instruction := .dec 7 (some 3871) (some 3866)
private theorem resolved3865 : resolveAt exactSites 3865 = some inst3865 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3865]
  rfl
private def inst3866 : Instruction := .inc 1 (some 3867)
private theorem resolved3866 : resolveAt exactSites 3866 = some inst3866 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3866]
  rfl
private def inst3867 : Instruction := .inc 1 (some 3868)
private theorem resolved3867 : resolveAt exactSites 3867 = some inst3867 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3867]
  rfl
private def inst3868 : Instruction := .inc 1 (some 3869)
private theorem resolved3868 : resolveAt exactSites 3868 = some inst3868 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3868]
  rfl
private def inst3869 : Instruction := .inc 1 (some 3870)
private theorem resolved3869 : resolveAt exactSites 3869 = some inst3869 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3869]
  rfl
private def inst3870 : Instruction := .jump (some 3865)
private theorem resolved3870 : resolveAt exactSites 3870 = some inst3870 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3870]
  rfl
private def inst3871 : Instruction := .dec 1 (some 3874) (some 3872)
private theorem resolved3871 : resolveAt exactSites 3871 = some inst3871 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3871]
  rfl
private def inst3872 : Instruction := .inc 6 (some 3873)
private theorem resolved3872 : resolveAt exactSites 3872 = some inst3872 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3872]
  rfl
private def inst3873 : Instruction := .jump (some 3871)
private theorem resolved3873 : resolveAt exactSites 3873 = some inst3873 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3873]
  rfl
private def inst3874 : Instruction := .dec 5 (some 3878) (some 3875)
private theorem resolved3874 : resolveAt exactSites 3874 = some inst3874 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3874]
  rfl
private def inst3875 : Instruction := .dec 6 (some 3877) (some 3876)
private theorem resolved3875 : resolveAt exactSites 3875 = some inst3875 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3875]
  rfl
private def inst3876 : Instruction := .jump (some 3874)
private theorem resolved3876 : resolveAt exactSites 3876 = some inst3876 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3876]
  rfl
private def inst3877 : Instruction := .jump (some 3879)
private theorem resolved3877 : resolveAt exactSites 3877 = some inst3877 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3877]
  rfl
private def inst3878 : Instruction := .dec 6 (some 3884) (some 3879)
private theorem resolved3878 : resolveAt exactSites 3878 = some inst3878 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3878]
  rfl
private def inst3879 : Instruction := .dec 5 (some 3881) (some 3880)
private theorem resolved3879 : resolveAt exactSites 3879 = some inst3879 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3879]
  rfl
private def inst3880 : Instruction := .jump (some 3879)
private theorem resolved3880 : resolveAt exactSites 3880 = some inst3880 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3880]
  rfl
private def inst3881 : Instruction := .dec 6 (some 3883) (some 3882)
private theorem resolved3881 : resolveAt exactSites 3881 = some inst3881 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3881]
  rfl
private def inst3882 : Instruction := .jump (some 3879)
private theorem resolved3882 : resolveAt exactSites 3882 = some inst3882 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3882]
  rfl
private def inst3883 : Instruction := .jump (some 3910)
private theorem resolved3883 : resolveAt exactSites 3883 = some inst3883 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3883]
  rfl
private def inst3884 : Instruction := .dec 1 (some 3887) (some 3885)
private theorem resolved3884 : resolveAt exactSites 3884 = some inst3884 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3884]
  rfl
private def inst3885 : Instruction := .inc 6 (some 3886)
private theorem resolved3885 : resolveAt exactSites 3885 = some inst3885 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3885]
  rfl
private def inst3886 : Instruction := .jump (some 3884)
private theorem resolved3886 : resolveAt exactSites 3886 = some inst3886 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3886]
  rfl
private def inst3887 : Instruction := .dec 2 (some 3890) (some 3888)
private theorem resolved3887 : resolveAt exactSites 3887 = some inst3887 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3887]
  rfl
private def inst3888 : Instruction := .inc 1 (some 3889)
private theorem resolved3888 : resolveAt exactSites 3888 = some inst3888 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3888]
  rfl
private def inst3889 : Instruction := .jump (some 3887)
private theorem resolved3889 : resolveAt exactSites 3889 = some inst3889 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3889]
  rfl
private def inst3890 : Instruction := .dec 1 (some 3894) (some 3891)
private theorem resolved3890 : resolveAt exactSites 3890 = some inst3890 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3890]
  rfl
private def inst3891 : Instruction := .inc 7 (some 3892)
private theorem resolved3891 : resolveAt exactSites 3891 = some inst3891 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3891]
  rfl
private def inst3892 : Instruction := .inc 6 (some 3893)
private theorem resolved3892 : resolveAt exactSites 3892 = some inst3892 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3892]
  rfl
private def inst3893 : Instruction := .jump (some 3890)
private theorem resolved3893 : resolveAt exactSites 3893 = some inst3893 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3893]
  rfl
private def inst3894 : Instruction := .dec 6 (some 3900) (some 3895)
private theorem resolved3894 : resolveAt exactSites 3894 = some inst3894 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3894]
  rfl
private def inst3895 : Instruction := .inc 7 (some 3896)
private theorem resolved3895 : resolveAt exactSites 3895 = some inst3895 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3895]
  rfl
private def inst3896 : Instruction := .dec 6 (some 3899) (some 3897)
private theorem resolved3896 : resolveAt exactSites 3896 = some inst3896 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3896]
  rfl
private def inst3897 : Instruction := .inc 1 (some 3898)
private theorem resolved3897 : resolveAt exactSites 3897 = some inst3897 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3897]
  rfl
private def inst3898 : Instruction := .jump (some 3896)
private theorem resolved3898 : resolveAt exactSites 3898 = some inst3898 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3898]
  rfl
private def inst3899 : Instruction := .jump (some 3890)
private theorem resolved3899 : resolveAt exactSites 3899 = some inst3899 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3899]
  rfl
private def inst3900 : Instruction := .dec 7 (some 3903) (some 3901)
private theorem resolved3900 : resolveAt exactSites 3900 = some inst3900 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3900]
  rfl
private def inst3901 : Instruction := .inc 2 (some 3902)
private theorem resolved3901 : resolveAt exactSites 3901 = some inst3901 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3901]
  rfl
private def inst3902 : Instruction := .jump (some 3900)
private theorem resolved3902 : resolveAt exactSites 3902 = some inst3902 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3902]
  rfl
private def inst3903 : Instruction := .dec 4 (some 3907) (some 3904)
private theorem resolved3903 : resolveAt exactSites 3903 = some inst3903 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3903]
  rfl
private def inst3904 : Instruction := .inc 1 (some 3905)
private theorem resolved3904 : resolveAt exactSites 3904 = some inst3904 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3904]
  rfl
private def inst3905 : Instruction := .inc 6 (some 3906)
private theorem resolved3905 : resolveAt exactSites 3905 = some inst3905 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3905]
  rfl
private def inst3906 : Instruction := .jump (some 3903)
private theorem resolved3906 : resolveAt exactSites 3906 = some inst3906 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3906]
  rfl
private def inst3907 : Instruction := .dec 6 (some 3910) (some 3908)
private theorem resolved3907 : resolveAt exactSites 3907 = some inst3907 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3907]
  rfl
private def inst3908 : Instruction := .inc 4 (some 3909)
private theorem resolved3908 : resolveAt exactSites 3908 = some inst3908 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3908]
  rfl
private def inst3909 : Instruction := .jump (some 3907)
private theorem resolved3909 : resolveAt exactSites 3909 = some inst3909 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3909]
  rfl
private def inst3910 : Instruction := .jump (some 0)
private theorem resolved3910 : resolveAt exactSites 3910 = some inst3910 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3910]
  rfl
private def inst3911 : Instruction := .dec 1 (some 3914) (some 3912)
private theorem resolved3911 : resolveAt exactSites 3911 = some inst3911 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3911]
  rfl
private def inst3912 : Instruction := .inc 6 (some 3913)
private theorem resolved3912 : resolveAt exactSites 3912 = some inst3912 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3912]
  rfl
private def inst3913 : Instruction := .jump (some 3911)
private theorem resolved3913 : resolveAt exactSites 3913 = some inst3913 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3913]
  rfl
private def inst3914 : Instruction := .dec 5 (some 3918) (some 3915)
private theorem resolved3914 : resolveAt exactSites 3914 = some inst3914 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3914]
  rfl
private def inst3915 : Instruction := .inc 1 (some 3916)
private theorem resolved3915 : resolveAt exactSites 3915 = some inst3915 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3915]
  rfl
private def inst3916 : Instruction := .inc 6 (some 3917)
private theorem resolved3916 : resolveAt exactSites 3916 = some inst3916 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3916]
  rfl
private def inst3917 : Instruction := .jump (some 3914)
private theorem resolved3917 : resolveAt exactSites 3917 = some inst3917 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3917]
  rfl
private def inst3918 : Instruction := .dec 6 (some 3921) (some 3919)
private theorem resolved3918 : resolveAt exactSites 3918 = some inst3918 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3918]
  rfl
private def inst3919 : Instruction := .inc 5 (some 3920)
private theorem resolved3919 : resolveAt exactSites 3919 = some inst3919 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3919]
  rfl
private def inst3920 : Instruction := .jump (some 3918)
private theorem resolved3920 : resolveAt exactSites 3920 = some inst3920 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3920]
  rfl
private def inst3921 : Instruction := .inc 6 (some 3922)
private theorem resolved3921 : resolveAt exactSites 3921 = some inst3921 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3921]
  rfl
private def inst3922 : Instruction := .dec 5 (some 3926) (some 3923)
private theorem resolved3922 : resolveAt exactSites 3922 = some inst3922 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3922]
  rfl
private def inst3923 : Instruction := .dec 6 (some 3925) (some 3924)
private theorem resolved3923 : resolveAt exactSites 3923 = some inst3923 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3923]
  rfl
private def inst3924 : Instruction := .jump (some 3922)
private theorem resolved3924 : resolveAt exactSites 3924 = some inst3924 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3924]
  rfl
private def inst3925 : Instruction := .jump (some 3927)
private theorem resolved3925 : resolveAt exactSites 3925 = some inst3925 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3925]
  rfl
private def inst3926 : Instruction := .dec 6 (some 3932) (some 3927)
private theorem resolved3926 : resolveAt exactSites 3926 = some inst3926 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3926]
  rfl
private def inst3927 : Instruction := .dec 5 (some 3929) (some 3928)
private theorem resolved3927 : resolveAt exactSites 3927 = some inst3927 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3927]
  rfl
private def inst3928 : Instruction := .jump (some 3927)
private theorem resolved3928 : resolveAt exactSites 3928 = some inst3928 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3928]
  rfl
private def inst3929 : Instruction := .dec 6 (some 3931) (some 3930)
private theorem resolved3929 : resolveAt exactSites 3929 = some inst3929 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3929]
  rfl
private def inst3930 : Instruction := .jump (some 3927)
private theorem resolved3930 : resolveAt exactSites 3930 = some inst3930 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3930]
  rfl
private def inst3931 : Instruction := .jump (some 3933)
private theorem resolved3931 : resolveAt exactSites 3931 = some inst3931 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3931]
  rfl
private def inst3932 : Instruction := .halt
private theorem resolved3932 : resolveAt exactSites 3932 = some inst3932 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3932]
  rfl
private def inst3933 : Instruction := .dec 2 (some 3941) (some 3934)
private theorem resolved3933 : resolveAt exactSites 3933 = some inst3933 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3933]
  rfl
private def inst3934 : Instruction := .inc 7 (some 3935)
private theorem resolved3934 : resolveAt exactSites 3934 = some inst3934 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3934]
  rfl
private def inst3935 : Instruction := .dec 6 (some 3937) (some 3936)
private theorem resolved3935 : resolveAt exactSites 3935 = some inst3935 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3935]
  rfl
private def raw0 := PA215.Census.C039.records[0]
private theorem row0 : destinationAgrees raw0 = true := by
  apply destination_nonterminal (s := site3841) (i := inst3841)
    (p := ⟨[true,false,true,false,true,false,false,true,false,false,false,false],0,.none⟩) (q := (.at 3844)) (e := .none) (k := 3844) (next := site3844)
  · rw [show raw0.siteIndex = 3841 from rfl]
    exact lookup3841
  · rw [show raw0.siteIndex = 3841 from rfl]
    exact resolved3841
  · decide
  · decide
  · rfl
  · exact lookup3844
  · decide
private def raw1 := PA215.Census.C039.records[1]
private theorem row1 : destinationAgrees raw1 = true := by
  apply destination_nonterminal (s := site3841) (i := inst3841)
    (p := ⟨[true,false,true,false,true,false,false,false,true,true,true,true,true],1,(.dec 8)⟩) (q := (.at 3842)) (e := (.dec 8)) (k := 3842) (next := site3842)
  · rw [show raw1.siteIndex = 3841 from rfl]
    exact lookup3841
  · rw [show raw1.siteIndex = 3841 from rfl]
    exact resolved3841
  · decide
  · decide
  · rfl
  · exact lookup3842
  · decide
private def raw2 := PA215.Census.C039.records[2]
private theorem row2 : destinationAgrees raw2 = true := by
  apply destination_nonterminal (s := site3842) (i := inst3842)
    (p := ⟨[true,false,true,false,true,false,false,false,true,true,true,true,true,true],0,(.inc 3)⟩) (q := (.at 3843)) (e := (.inc 3)) (k := 3843) (next := site3843)
  · rw [show raw2.siteIndex = 3842 from rfl]
    exact lookup3842
  · rw [show raw2.siteIndex = 3842 from rfl]
    exact resolved3842
  · decide
  · decide
  · rfl
  · exact lookup3843
  · decide
private def raw3 := PA215.Census.C039.records[3]
private theorem row3 : destinationAgrees raw3 = true := by
  apply destination_nonterminal (s := site3843) (i := inst3843)
    (p := ⟨[true,false,true,false,true,false,false,false,true,true,true,true],0,.none⟩) (q := (.at 3841)) (e := .none) (k := 3841) (next := site3841)
  · rw [show raw3.siteIndex = 3843 from rfl]
    exact lookup3843
  · rw [show raw3.siteIndex = 3843 from rfl]
    exact resolved3843
  · decide
  · decide
  · rfl
  · exact lookup3841
  · decide
private def raw4 := PA215.Census.C039.records[4]
private theorem row4 : destinationAgrees raw4 = true := by
  apply destination_nonterminal (s := site3844) (i := inst3844)
    (p := ⟨[true,false,true,false,true,false,false,true,false,true],0,.none⟩) (q := (.at 3852)) (e := .none) (k := 3852) (next := site3852)
  · rw [show raw4.siteIndex = 3844 from rfl]
    exact lookup3844
  · rw [show raw4.siteIndex = 3844 from rfl]
    exact resolved3844
  · decide
  · decide
  · rfl
  · exact lookup3852
  · decide
private def raw5 := PA215.Census.C039.records[5]
private theorem row5 : destinationAgrees raw5 = true := by
  apply destination_nonterminal (s := site3844) (i := inst3844)
    (p := ⟨[true,false,true,false,true,false,false,true,false,false,true],1,(.dec 0)⟩) (q := (.at 3845)) (e := (.dec 0)) (k := 3845) (next := site3845)
  · rw [show raw5.siteIndex = 3844 from rfl]
    exact lookup3844
  · rw [show raw5.siteIndex = 3844 from rfl]
    exact resolved3844
  · decide
  · decide
  · rfl
  · exact lookup3845
  · decide
private def raw6 := PA215.Census.C039.records[6]
private theorem row6 : destinationAgrees raw6 = true := by
  apply destination_nonterminal (s := site3845) (i := inst3845)
    (p := ⟨[true,false,true,false,true,false,false,true,false,false,true,true],0,(.inc 5)⟩) (q := (.at 3846)) (e := (.inc 5)) (k := 3846) (next := site3846)
  · rw [show raw6.siteIndex = 3845 from rfl]
    exact lookup3845
  · rw [show raw6.siteIndex = 3845 from rfl]
    exact resolved3845
  · decide
  · decide
  · rfl
  · exact lookup3846
  · decide
private def raw7 := PA215.Census.C039.records[7]
private theorem row7 : destinationAgrees raw7 = true := by
  apply destination_nonterminal (s := site3846) (i := inst3846)
    (p := ⟨[true,false,true,false,true,false,false,true,false,false,true,true,false,true],0,.none⟩) (q := (.at 3848)) (e := .none) (k := 3848) (next := site3848)
  · rw [show raw7.siteIndex = 3846 from rfl]
    exact lookup3846
  · rw [show raw7.siteIndex = 3846 from rfl]
    exact resolved3846
  · decide
  · decide
  · rfl
  · exact lookup3848
  · decide
private def raw8 := PA215.Census.C039.records[8]
private theorem row8 : destinationAgrees raw8 = true := by
  apply destination_nonterminal (s := site3846) (i := inst3846)
    (p := ⟨[true,false,true,false,true,false,false,true,false,false,true,true,false,false,true],1,(.dec 8)⟩) (q := (.at 3847)) (e := (.dec 8)) (k := 3847) (next := site3847)
  · rw [show raw8.siteIndex = 3846 from rfl]
    exact lookup3846
  · rw [show raw8.siteIndex = 3846 from rfl]
    exact resolved3846
  · decide
  · decide
  · rfl
  · exact lookup3847
  · decide
private def raw9 := PA215.Census.C039.records[9]
private theorem row9 : destinationAgrees raw9 = true := by
  apply destination_nonterminal (s := site3847) (i := inst3847)
    (p := ⟨[true,false,true,false,true,false,false,true,false,false,true,true,true],0,.none⟩) (q := (.at 3851)) (e := .none) (k := 3851) (next := site3851)
  · rw [show raw9.siteIndex = 3847 from rfl]
    exact lookup3847
  · rw [show raw9.siteIndex = 3847 from rfl]
    exact resolved3847
  · decide
  · decide
  · rfl
  · exact lookup3851
  · decide
private def raw10 := PA215.Census.C039.records[10]
private theorem row10 : destinationAgrees raw10 = true := by
  apply destination_nonterminal (s := site3848) (i := inst3848)
    (p := ⟨[true,false,true,false,true,false,false,true,false,false,true,true,true,false],0,.none⟩) (q := (.at 3851)) (e := .none) (k := 3851) (next := site3851)
  · rw [show raw10.siteIndex = 3848 from rfl]
    exact lookup3848
  · rw [show raw10.siteIndex = 3848 from rfl]
    exact resolved3848
  · decide
  · decide
  · rfl
  · exact lookup3851
  · decide
private def raw11 := PA215.Census.C039.records[11]
private theorem row11 : destinationAgrees raw11 = true := by
  apply destination_nonterminal (s := site3848) (i := inst3848)
    (p := ⟨[true,false,true,false,true,false,false,true,false,false,true,true,false,true,true],1,(.dec 5)⟩) (q := (.at 3849)) (e := (.dec 5)) (k := 3849) (next := site3849)
  · rw [show raw11.siteIndex = 3848 from rfl]
    exact lookup3848
  · rw [show raw11.siteIndex = 3848 from rfl]
    exact resolved3848
  · decide
  · decide
  · rfl
  · exact lookup3849
  · decide
private def raw12 := PA215.Census.C039.records[12]
private theorem row12 : destinationAgrees raw12 = true := by
  apply destination_nonterminal (s := site3849) (i := inst3849)
    (p := ⟨[true,false,true,false,true,false,false,true,false,false,true,true,false,true,true,true],0,(.inc 8)⟩) (q := (.at 3850)) (e := (.inc 8)) (k := 3850) (next := site3850)
  · rw [show raw12.siteIndex = 3849 from rfl]
    exact lookup3849
  · rw [show raw12.siteIndex = 3849 from rfl]
    exact resolved3849
  · decide
  · decide
  · rfl
  · exact lookup3850
  · decide
private def raw13 := PA215.Census.C039.records[13]
private theorem row13 : destinationAgrees raw13 = true := by
  apply destination_nonterminal (s := site3850) (i := inst3850)
    (p := ⟨[true,false,true,false,true,false,false,true,false,false,true,true,false,true],0,.none⟩) (q := (.at 3848)) (e := .none) (k := 3848) (next := site3848)
  · rw [show raw13.siteIndex = 3850 from rfl]
    exact lookup3850
  · rw [show raw13.siteIndex = 3850 from rfl]
    exact resolved3850
  · decide
  · decide
  · rfl
  · exact lookup3848
  · decide
private def raw14 := PA215.Census.C039.records[14]
private theorem row14 : destinationAgrees raw14 = true := by
  apply destination_nonterminal (s := site3851) (i := inst3851)
    (p := ⟨[true,false,true,false,true,false,false,true,false,false],0,.none⟩) (q := (.at 3844)) (e := .none) (k := 3844) (next := site3844)
  · rw [show raw14.siteIndex = 3851 from rfl]
    exact lookup3851
  · rw [show raw14.siteIndex = 3851 from rfl]
    exact resolved3851
  · decide
  · decide
  · rfl
  · exact lookup3844
  · decide
private def raw15 := PA215.Census.C039.records[15]
private theorem row15 : destinationAgrees raw15 = true := by
  apply destination_nonterminal (s := site3852) (i := inst3852)
    (p := ⟨[true,false,true,false,true,false,false,true,true,false],0,.none⟩) (q := (.at 3855)) (e := .none) (k := 3855) (next := site3855)
  · rw [show raw15.siteIndex = 3852 from rfl]
    exact lookup3852
  · rw [show raw15.siteIndex = 3852 from rfl]
    exact resolved3852
  · decide
  · decide
  · rfl
  · exact lookup3855
  · decide
private def raw16 := PA215.Census.C039.records[16]
private theorem row16 : destinationAgrees raw16 = true := by
  apply destination_nonterminal (s := site3852) (i := inst3852)
    (p := ⟨[true,false,true,false,true,false,false,true,false,true,true],1,(.dec 5)⟩) (q := (.at 3853)) (e := (.dec 5)) (k := 3853) (next := site3853)
  · rw [show raw16.siteIndex = 3852 from rfl]
    exact lookup3852
  · rw [show raw16.siteIndex = 3852 from rfl]
    exact resolved3852
  · decide
  · decide
  · rfl
  · exact lookup3853
  · decide
private def raw17 := PA215.Census.C039.records[17]
private theorem row17 : destinationAgrees raw17 = true := by
  apply destination_nonterminal (s := site3853) (i := inst3853)
    (p := ⟨[true,false,true,false,true,false,false,true,false,true,true,true],0,(.inc 0)⟩) (q := (.at 3854)) (e := (.inc 0)) (k := 3854) (next := site3854)
  · rw [show raw17.siteIndex = 3853 from rfl]
    exact lookup3853
  · rw [show raw17.siteIndex = 3853 from rfl]
    exact resolved3853
  · decide
  · decide
  · rfl
  · exact lookup3854
  · decide
private def raw18 := PA215.Census.C039.records[18]
private theorem row18 : destinationAgrees raw18 = true := by
  apply destination_nonterminal (s := site3854) (i := inst3854)
    (p := ⟨[true,false,true,false,true,false,false,true,false,true],0,.none⟩) (q := (.at 3852)) (e := .none) (k := 3852) (next := site3852)
  · rw [show raw18.siteIndex = 3854 from rfl]
    exact lookup3854
  · rw [show raw18.siteIndex = 3854 from rfl]
    exact resolved3854
  · decide
  · decide
  · rfl
  · exact lookup3852
  · decide
private def raw19 := PA215.Census.C039.records[19]
private theorem row19 : destinationAgrees raw19 = true := by
  apply destination_nonterminal (s := site3855) (i := inst3855)
    (p := ⟨[true,false,true,false,true,false,false,true,true,false,true],0,.none⟩) (q := (.at 3859)) (e := .none) (k := 3859) (next := site3859)
  · rw [show raw19.siteIndex = 3855 from rfl]
    exact lookup3855
  · rw [show raw19.siteIndex = 3855 from rfl]
    exact resolved3855
  · decide
  · decide
  · rfl
  · exact lookup3859
  · decide
private def raw20 := PA215.Census.C039.records[20]
private theorem row20 : destinationAgrees raw20 = true := by
  apply destination_nonterminal (s := site3855) (i := inst3855)
    (p := ⟨[true,false,true,false,true,false,false,true,true,false,false,true],1,(.dec 2)⟩) (q := (.at 3856)) (e := (.dec 2)) (k := 3856) (next := site3856)
  · rw [show raw20.siteIndex = 3855 from rfl]
    exact lookup3855
  · rw [show raw20.siteIndex = 3855 from rfl]
    exact resolved3855
  · decide
  · decide
  · rfl
  · exact lookup3856
  · decide
private def raw21 := PA215.Census.C039.records[21]
private theorem row21 : destinationAgrees raw21 = true := by
  apply destination_nonterminal (s := site3856) (i := inst3856)
    (p := ⟨[true,false,true,false,true,false,false,true,true,false,false,true,true],0,(.inc 5)⟩) (q := (.at 3857)) (e := (.inc 5)) (k := 3857) (next := site3857)
  · rw [show raw21.siteIndex = 3856 from rfl]
    exact lookup3856
  · rw [show raw21.siteIndex = 3856 from rfl]
    exact resolved3856
  · decide
  · decide
  · rfl
  · exact lookup3857
  · decide
private def raw22 := PA215.Census.C039.records[22]
private theorem row22 : destinationAgrees raw22 = true := by
  apply destination_nonterminal (s := site3857) (i := inst3857)
    (p := ⟨[true,false,true,false,true,false,false,true,true,false,false,true,true,true],0,(.inc 8)⟩) (q := (.at 3858)) (e := (.inc 8)) (k := 3858) (next := site3858)
  · rw [show raw22.siteIndex = 3857 from rfl]
    exact lookup3857
  · rw [show raw22.siteIndex = 3857 from rfl]
    exact resolved3857
  · decide
  · decide
  · rfl
  · exact lookup3858
  · decide
private def raw23 := PA215.Census.C039.records[23]
private theorem row23 : destinationAgrees raw23 = true := by
  apply destination_nonterminal (s := site3858) (i := inst3858)
    (p := ⟨[true,false,true,false,true,false,false,true,true,false,false],0,.none⟩) (q := (.at 3855)) (e := .none) (k := 3855) (next := site3855)
  · rw [show raw23.siteIndex = 3858 from rfl]
    exact lookup3858
  · rw [show raw23.siteIndex = 3858 from rfl]
    exact resolved3858
  · decide
  · decide
  · rfl
  · exact lookup3855
  · decide
private def raw24 := PA215.Census.C039.records[24]
private theorem row24 : destinationAgrees raw24 = true := by
  apply destination_nonterminal (s := site3859) (i := inst3859)
    (p := ⟨[true,false,true,false,true,false,false,true,true,true,false],0,.none⟩) (q := (.at 3865)) (e := .none) (k := 3865) (next := site3865)
  · rw [show raw24.siteIndex = 3859 from rfl]
    exact lookup3859
  · rw [show raw24.siteIndex = 3859 from rfl]
    exact resolved3859
  · decide
  · decide
  · rfl
  · exact lookup3865
  · decide
private def raw25 := PA215.Census.C039.records[25]
private theorem row25 : destinationAgrees raw25 = true := by
  apply destination_nonterminal (s := site3859) (i := inst3859)
    (p := ⟨[true,false,true,false,true,false,false,true,true,false,true,true],1,(.dec 8)⟩) (q := (.at 3860)) (e := (.dec 8)) (k := 3860) (next := site3860)
  · rw [show raw25.siteIndex = 3859 from rfl]
    exact lookup3859
  · rw [show raw25.siteIndex = 3859 from rfl]
    exact resolved3859
  · decide
  · decide
  · rfl
  · exact lookup3860
  · decide
private def raw26 := PA215.Census.C039.records[26]
private theorem row26 : destinationAgrees raw26 = true := by
  apply destination_nonterminal (s := site3860) (i := inst3860)
    (p := ⟨[true,false,true,false,true,false,false,true,true,false,true,true,false,true],0,(.inc 5)⟩) (q := (.at 3861)) (e := (.inc 5)) (k := 3861) (next := site3861)
  · rw [show raw26.siteIndex = 3860 from rfl]
    exact lookup3860
  · rw [show raw26.siteIndex = 3860 from rfl]
    exact resolved3860
  · decide
  · decide
  · rfl
  · exact lookup3861
  · decide
private def raw27 := PA215.Census.C039.records[27]
private theorem row27 : destinationAgrees raw27 = true := by
  apply destination_nonterminal (s := site3861) (i := inst3861)
    (p := ⟨[true,false,true,false,true,false,false,true,true,false,true,true,true,false],0,.none⟩) (q := (.at 3864)) (e := .none) (k := 3864) (next := site3864)
  · rw [show raw27.siteIndex = 3861 from rfl]
    exact lookup3861
  · rw [show raw27.siteIndex = 3861 from rfl]
    exact resolved3861
  · decide
  · decide
  · rfl
  · exact lookup3864
  · decide
private def raw28 := PA215.Census.C039.records[28]
private theorem row28 : destinationAgrees raw28 = true := by
  apply destination_nonterminal (s := site3861) (i := inst3861)
    (p := ⟨[true,false,true,false,true,false,false,true,true,false,true,true,false,true,true],1,(.dec 8)⟩) (q := (.at 3862)) (e := (.dec 8)) (k := 3862) (next := site3862)
  · rw [show raw28.siteIndex = 3861 from rfl]
    exact lookup3861
  · rw [show raw28.siteIndex = 3861 from rfl]
    exact resolved3861
  · decide
  · decide
  · rfl
  · exact lookup3862
  · decide
private def raw29 := PA215.Census.C039.records[29]
private theorem row29 : destinationAgrees raw29 = true := by
  apply destination_nonterminal (s := site3862) (i := inst3862)
    (p := ⟨[true,false,true,false,true,false,false,true,true,false,true,true,false,true,true,true],0,(.inc 2)⟩) (q := (.at 3863)) (e := (.inc 2)) (k := 3863) (next := site3863)
  · rw [show raw29.siteIndex = 3862 from rfl]
    exact lookup3862
  · rw [show raw29.siteIndex = 3862 from rfl]
    exact resolved3862
  · decide
  · decide
  · rfl
  · exact lookup3863
  · decide
private def raw30 := PA215.Census.C039.records[30]
private theorem row30 : destinationAgrees raw30 = true := by
  apply destination_nonterminal (s := site3863) (i := inst3863)
    (p := ⟨[true,false,true,false,true,false,false,true,true,false,true,true,false,true],0,.none⟩) (q := (.at 3861)) (e := .none) (k := 3861) (next := site3861)
  · rw [show raw30.siteIndex = 3863 from rfl]
    exact lookup3863
  · rw [show raw30.siteIndex = 3863 from rfl]
    exact resolved3863
  · decide
  · decide
  · rfl
  · exact lookup3861
  · decide
private def raw31 := PA215.Census.C039.records[31]
private theorem row31 : destinationAgrees raw31 = true := by
  apply destination_nonterminal (s := site3864) (i := inst3864)
    (p := ⟨[true,false,true,false,true,false,false,true,true,false],0,.none⟩) (q := (.at 3855)) (e := .none) (k := 3855) (next := site3855)
  · rw [show raw31.siteIndex = 3864 from rfl]
    exact lookup3864
  · rw [show raw31.siteIndex = 3864 from rfl]
    exact resolved3864
  · decide
  · decide
  · rfl
  · exact lookup3855
  · decide
private def raw32 := PA215.Census.C039.records[32]
private theorem row32 : destinationAgrees raw32 = true := by
  apply destination_nonterminal (s := site3865) (i := inst3865)
    (p := ⟨[true,false,true,false,true,false,true,false,false,false],0,.none⟩) (q := (.at 3871)) (e := .none) (k := 3871) (next := site3871)
  · rw [show raw32.siteIndex = 3865 from rfl]
    exact lookup3865
  · rw [show raw32.siteIndex = 3865 from rfl]
    exact resolved3865
  · decide
  · decide
  · rfl
  · exact lookup3871
  · decide
private def raw33 := PA215.Census.C039.records[33]
private theorem row33 : destinationAgrees raw33 = true := by
  apply destination_nonterminal (s := site3865) (i := inst3865)
    (p := ⟨[true,false,true,false,true,false,false,true,true,true,true],1,(.dec 5)⟩) (q := (.at 3866)) (e := (.dec 5)) (k := 3866) (next := site3866)
  · rw [show raw33.siteIndex = 3865 from rfl]
    exact lookup3865
  · rw [show raw33.siteIndex = 3865 from rfl]
    exact resolved3865
  · decide
  · decide
  · rfl
  · exact lookup3866
  · decide
private def raw34 := PA215.Census.C039.records[34]
private theorem row34 : destinationAgrees raw34 = true := by
  apply destination_nonterminal (s := site3866) (i := inst3866)
    (p := ⟨[true,false,true,false,true,false,false,true,true,true,true,false,false,true],0,(.inc 2)⟩) (q := (.at 3867)) (e := (.inc 2)) (k := 3867) (next := site3867)
  · rw [show raw34.siteIndex = 3866 from rfl]
    exact lookup3866
  · rw [show raw34.siteIndex = 3866 from rfl]
    exact resolved3866
  · decide
  · decide
  · rfl
  · exact lookup3867
  · decide
private def raw35 := PA215.Census.C039.records[35]
private theorem row35 : destinationAgrees raw35 = true := by
  apply destination_nonterminal (s := site3867) (i := inst3867)
    (p := ⟨[true,false,true,false,true,false,false,true,true,true,true,false,true,false],0,(.inc 2)⟩) (q := (.at 3868)) (e := (.inc 2)) (k := 3868) (next := site3868)
  · rw [show raw35.siteIndex = 3867 from rfl]
    exact lookup3867
  · rw [show raw35.siteIndex = 3867 from rfl]
    exact resolved3867
  · decide
  · decide
  · rfl
  · exact lookup3868
  · decide
private def raw36 := PA215.Census.C039.records[36]
private theorem row36 : destinationAgrees raw36 = true := by
  apply destination_nonterminal (s := site3868) (i := inst3868)
    (p := ⟨[true,false,true,false,true,false,false,true,true,true,true,false,true,true],0,(.inc 2)⟩) (q := (.at 3869)) (e := (.inc 2)) (k := 3869) (next := site3869)
  · rw [show raw36.siteIndex = 3868 from rfl]
    exact lookup3868
  · rw [show raw36.siteIndex = 3868 from rfl]
    exact resolved3868
  · decide
  · decide
  · rfl
  · exact lookup3869
  · decide
private def raw37 := PA215.Census.C039.records[37]
private theorem row37 : destinationAgrees raw37 = true := by
  apply destination_nonterminal (s := site3869) (i := inst3869)
    (p := ⟨[true,false,true,false,true,false,false,true,true,true,true,true,false,false],0,(.inc 2)⟩) (q := (.at 3870)) (e := (.inc 2)) (k := 3870) (next := site3870)
  · rw [show raw37.siteIndex = 3869 from rfl]
    exact lookup3869
  · rw [show raw37.siteIndex = 3869 from rfl]
    exact resolved3869
  · decide
  · decide
  · rfl
  · exact lookup3870
  · decide
private def raw38 := PA215.Census.C039.records[38]
private theorem row38 : destinationAgrees raw38 = true := by
  apply destination_nonterminal (s := site3870) (i := inst3870)
    (p := ⟨[true,false,true,false,true,false,false,true,true,true],0,.none⟩) (q := (.at 3865)) (e := .none) (k := 3865) (next := site3865)
  · rw [show raw38.siteIndex = 3870 from rfl]
    exact lookup3870
  · rw [show raw38.siteIndex = 3870 from rfl]
    exact resolved3870
  · decide
  · decide
  · rfl
  · exact lookup3865
  · decide
private def raw39 := PA215.Census.C039.records[39]
private theorem row39 : destinationAgrees raw39 = true := by
  apply destination_nonterminal (s := site3871) (i := inst3871)
    (p := ⟨[true,false,true,false,true,true,false],0,.none⟩) (q := (.at 3874)) (e := .none) (k := 3874) (next := site3874)
  · rw [show raw39.siteIndex = 3871 from rfl]
    exact lookup3871
  · rw [show raw39.siteIndex = 3871 from rfl]
    exact resolved3871
  · decide
  · decide
  · rfl
  · exact lookup3874
  · decide
private def raw40 := PA215.Census.C039.records[40]
private theorem row40 : destinationAgrees raw40 = true := by
  apply destination_nonterminal (s := site3871) (i := inst3871)
    (p := ⟨[true,false,true,false,true,false,true,true],1,(.dec 2)⟩) (q := (.at 3872)) (e := (.dec 2)) (k := 3872) (next := site3872)
  · rw [show raw40.siteIndex = 3871 from rfl]
    exact lookup3871
  · rw [show raw40.siteIndex = 3871 from rfl]
    exact resolved3871
  · decide
  · decide
  · rfl
  · exact lookup3872
  · decide
private def raw41 := PA215.Census.C039.records[41]
private theorem row41 : destinationAgrees raw41 = true := by
  apply destination_nonterminal (s := site3872) (i := inst3872)
    (p := ⟨[true,false,true,false,true,false,true,true,true],0,(.inc 8)⟩) (q := (.at 3873)) (e := (.inc 8)) (k := 3873) (next := site3873)
  · rw [show raw41.siteIndex = 3872 from rfl]
    exact lookup3872
  · rw [show raw41.siteIndex = 3872 from rfl]
    exact resolved3872
  · decide
  · decide
  · rfl
  · exact lookup3873
  · decide
private def raw42 := PA215.Census.C039.records[42]
private theorem row42 : destinationAgrees raw42 = true := by
  apply destination_nonterminal (s := site3873) (i := inst3873)
    (p := ⟨[true,false,true,false,true,false,true],0,.none⟩) (q := (.at 3871)) (e := .none) (k := 3871) (next := site3871)
  · rw [show raw42.siteIndex = 3873 from rfl]
    exact lookup3873
  · rw [show raw42.siteIndex = 3873 from rfl]
    exact resolved3873
  · decide
  · decide
  · rfl
  · exact lookup3871
  · decide
private def raw43 := PA215.Census.C039.records[43]
private theorem row43 : destinationAgrees raw43 = true := by
  apply destination_nonterminal (s := site3874) (i := inst3874)
    (p := ⟨[true,false,true,false,true,true,false,false,true],0,.none⟩) (q := (.at 3878)) (e := .none) (k := 3878) (next := site3878)
  · rw [show raw43.siteIndex = 3874 from rfl]
    exact lookup3874
  · rw [show raw43.siteIndex = 3874 from rfl]
    exact resolved3874
  · decide
  · decide
  · rfl
  · exact lookup3878
  · decide
private def raw44 := PA215.Census.C039.records[44]
private theorem row44 : destinationAgrees raw44 = true := by
  apply destination_nonterminal (s := site3874) (i := inst3874)
    (p := ⟨[true,false,true,false,true,true,false,false,false,true],1,(.dec 7)⟩) (q := (.at 3875)) (e := (.dec 7)) (k := 3875) (next := site3875)
  · rw [show raw44.siteIndex = 3874 from rfl]
    exact lookup3874
  · rw [show raw44.siteIndex = 3874 from rfl]
    exact resolved3874
  · decide
  · decide
  · rfl
  · exact lookup3875
  · decide
private def raw45 := PA215.Census.C039.records[45]
private theorem row45 : destinationAgrees raw45 = true := by
  apply destination_nonterminal (s := site3875) (i := inst3875)
    (p := ⟨[true,false,true,false,true,true,false,false,false,true,true],0,.none⟩) (q := (.at 3877)) (e := .none) (k := 3877) (next := site3877)
  · rw [show raw45.siteIndex = 3875 from rfl]
    exact lookup3875
  · rw [show raw45.siteIndex = 3875 from rfl]
    exact resolved3875
  · decide
  · decide
  · rfl
  · exact lookup3877
  · decide
private def raw46 := PA215.Census.C039.records[46]
private theorem row46 : destinationAgrees raw46 = true := by
  apply destination_nonterminal (s := site3875) (i := inst3875)
    (p := ⟨[true,false,true,false,true,true,false,false,false,true,false,true],1,(.dec 8)⟩) (q := (.at 3876)) (e := (.dec 8)) (k := 3876) (next := site3876)
  · rw [show raw46.siteIndex = 3875 from rfl]
    exact lookup3875
  · rw [show raw46.siteIndex = 3875 from rfl]
    exact resolved3875
  · decide
  · decide
  · rfl
  · exact lookup3876
  · decide
private def raw47 := PA215.Census.C039.records[47]
private theorem row47 : destinationAgrees raw47 = true := by
  apply destination_nonterminal (s := site3876) (i := inst3876)
    (p := ⟨[true,false,true,false,true,true,false,false,false],0,.none⟩) (q := (.at 3874)) (e := .none) (k := 3874) (next := site3874)
  · rw [show raw47.siteIndex = 3876 from rfl]
    exact lookup3876
  · rw [show raw47.siteIndex = 3876 from rfl]
    exact resolved3876
  · decide
  · decide
  · rfl
  · exact lookup3874
  · decide
private def raw48 := PA215.Census.C039.records[48]
private theorem row48 : destinationAgrees raw48 = true := by
  apply destination_nonterminal (s := site3877) (i := inst3877)
    (p := ⟨[true,false,true,false,true,true,false,true],0,.none⟩) (q := (.at 3879)) (e := .none) (k := 3879) (next := site3879)
  · rw [show raw48.siteIndex = 3877 from rfl]
    exact lookup3877
  · rw [show raw48.siteIndex = 3877 from rfl]
    exact resolved3877
  · decide
  · decide
  · rfl
  · exact lookup3879
  · decide
private def raw49 := PA215.Census.C039.records[49]
private theorem row49 : destinationAgrees raw49 = true := by
  apply destination_nonterminal (s := site3878) (i := inst3878)
    (p := ⟨[true,false,true,false,true,true,true],0,.none⟩) (q := (.at 3884)) (e := .none) (k := 3884) (next := site3884)
  · rw [show raw49.siteIndex = 3878 from rfl]
    exact lookup3878
  · rw [show raw49.siteIndex = 3878 from rfl]
    exact resolved3878
  · decide
  · decide
  · rfl
  · exact lookup3884
  · decide
private def raw50 := PA215.Census.C039.records[50]
private theorem row50 : destinationAgrees raw50 = true := by
  apply destination_nonterminal (s := site3878) (i := inst3878)
    (p := ⟨[true,false,true,false,true,true,false,true,false],1,(.dec 8)⟩) (q := (.at 3879)) (e := (.dec 8)) (k := 3879) (next := site3879)
  · rw [show raw50.siteIndex = 3878 from rfl]
    exact lookup3878
  · rw [show raw50.siteIndex = 3878 from rfl]
    exact resolved3878
  · decide
  · decide
  · rfl
  · exact lookup3879
  · decide
private def raw51 := PA215.Census.C039.records[51]
private theorem row51 : destinationAgrees raw51 = true := by
  apply destination_nonterminal (s := site3879) (i := inst3879)
    (p := ⟨[true,false,true,false,true,true,false,true,true],0,.none⟩) (q := (.at 3881)) (e := .none) (k := 3881) (next := site3881)
  · rw [show raw51.siteIndex = 3879 from rfl]
    exact lookup3879
  · rw [show raw51.siteIndex = 3879 from rfl]
    exact resolved3879
  · decide
  · decide
  · rfl
  · exact lookup3881
  · decide
private def raw52 := PA215.Census.C039.records[52]
private theorem row52 : destinationAgrees raw52 = true := by
  apply destination_nonterminal (s := site3879) (i := inst3879)
    (p := ⟨[true,false,true,false,true,true,false,true,false,true],1,(.dec 7)⟩) (q := (.at 3880)) (e := (.dec 7)) (k := 3880) (next := site3880)
  · rw [show raw52.siteIndex = 3879 from rfl]
    exact lookup3879
  · rw [show raw52.siteIndex = 3879 from rfl]
    exact resolved3879
  · decide
  · decide
  · rfl
  · exact lookup3880
  · decide
private def raw53 := PA215.Census.C039.records[53]
private theorem row53 : destinationAgrees raw53 = true := by
  apply destination_nonterminal (s := site3880) (i := inst3880)
    (p := ⟨[true,false,true,false,true,true,false,true,false],0,.none⟩) (q := (.at 3879)) (e := .none) (k := 3879) (next := site3879)
  · rw [show raw53.siteIndex = 3880 from rfl]
    exact lookup3880
  · rw [show raw53.siteIndex = 3880 from rfl]
    exact resolved3880
  · decide
  · decide
  · rfl
  · exact lookup3879
  · decide
private def raw54 := PA215.Census.C039.records[54]
private theorem row54 : destinationAgrees raw54 = true := by
  apply destination_nonterminal (s := site3881) (i := inst3881)
    (p := ⟨[true,false,true,false,true,true,false,true,true,true],0,.none⟩) (q := (.at 3883)) (e := .none) (k := 3883) (next := site3883)
  · rw [show raw54.siteIndex = 3881 from rfl]
    exact lookup3881
  · rw [show raw54.siteIndex = 3881 from rfl]
    exact resolved3881
  · decide
  · decide
  · rfl
  · exact lookup3883
  · decide
private def raw55 := PA215.Census.C039.records[55]
private theorem row55 : destinationAgrees raw55 = true := by
  apply destination_nonterminal (s := site3881) (i := inst3881)
    (p := ⟨[true,false,true,false,true,true,false,true,true,false,true],1,(.dec 8)⟩) (q := (.at 3882)) (e := (.dec 8)) (k := 3882) (next := site3882)
  · rw [show raw55.siteIndex = 3881 from rfl]
    exact lookup3881
  · rw [show raw55.siteIndex = 3881 from rfl]
    exact resolved3881
  · decide
  · decide
  · rfl
  · exact lookup3882
  · decide
private def raw56 := PA215.Census.C039.records[56]
private theorem row56 : destinationAgrees raw56 = true := by
  apply destination_nonterminal (s := site3882) (i := inst3882)
    (p := ⟨[true,false,true,false,true,true,false,true],0,.none⟩) (q := (.at 3879)) (e := .none) (k := 3879) (next := site3879)
  · rw [show raw56.siteIndex = 3882 from rfl]
    exact lookup3882
  · rw [show raw56.siteIndex = 3882 from rfl]
    exact resolved3882
  · decide
  · decide
  · rfl
  · exact lookup3879
  · decide
private def raw57 := PA215.Census.C039.records[57]
private theorem row57 : destinationAgrees raw57 = true := by
  apply destination_nonterminal (s := site3883) (i := inst3883)
    (p := ⟨[true,false,true,true,false,false],0,.none⟩) (q := (.at 3910)) (e := .none) (k := 3910) (next := site3910)
  · rw [show raw57.siteIndex = 3883 from rfl]
    exact lookup3883
  · rw [show raw57.siteIndex = 3883 from rfl]
    exact resolved3883
  · decide
  · decide
  · rfl
  · exact lookup3910
  · decide
private def raw58 := PA215.Census.C039.records[58]
private theorem row58 : destinationAgrees raw58 = true := by
  apply destination_nonterminal (s := site3884) (i := inst3884)
    (p := ⟨[true,false,true,false,true,true,true,false,true],0,.none⟩) (q := (.at 3887)) (e := .none) (k := 3887) (next := site3887)
  · rw [show raw58.siteIndex = 3884 from rfl]
    exact lookup3884
  · rw [show raw58.siteIndex = 3884 from rfl]
    exact resolved3884
  · decide
  · decide
  · rfl
  · exact lookup3887
  · decide
private def raw59 := PA215.Census.C039.records[59]
private theorem row59 : destinationAgrees raw59 = true := by
  apply destination_nonterminal (s := site3884) (i := inst3884)
    (p := ⟨[true,false,true,false,true,true,true,false,false,true],1,(.dec 2)⟩) (q := (.at 3885)) (e := (.dec 2)) (k := 3885) (next := site3885)
  · rw [show raw59.siteIndex = 3884 from rfl]
    exact lookup3884
  · rw [show raw59.siteIndex = 3884 from rfl]
    exact resolved3884
  · decide
  · decide
  · rfl
  · exact lookup3885
  · decide
private def raw60 := PA215.Census.C039.records[60]
private theorem row60 : destinationAgrees raw60 = true := by
  apply destination_nonterminal (s := site3885) (i := inst3885)
    (p := ⟨[true,false,true,false,true,true,true,false,false,true,true],0,(.inc 8)⟩) (q := (.at 3886)) (e := (.inc 8)) (k := 3886) (next := site3886)
  · rw [show raw60.siteIndex = 3885 from rfl]
    exact lookup3885
  · rw [show raw60.siteIndex = 3885 from rfl]
    exact resolved3885
  · decide
  · decide
  · rfl
  · exact lookup3886
  · decide
private def raw61 := PA215.Census.C039.records[61]
private theorem row61 : destinationAgrees raw61 = true := by
  apply destination_nonterminal (s := site3886) (i := inst3886)
    (p := ⟨[true,false,true,false,true,true,true,false,false],0,.none⟩) (q := (.at 3884)) (e := .none) (k := 3884) (next := site3884)
  · rw [show raw61.siteIndex = 3886 from rfl]
    exact lookup3886
  · rw [show raw61.siteIndex = 3886 from rfl]
    exact resolved3886
  · decide
  · decide
  · rfl
  · exact lookup3884
  · decide
private def raw62 := PA215.Census.C039.records[62]
private theorem row62 : destinationAgrees raw62 = true := by
  apply destination_nonterminal (s := site3887) (i := inst3887)
    (p := ⟨[true,false,true,false,true,true,true,false,true,true],0,.none⟩) (q := (.at 3890)) (e := .none) (k := 3890) (next := site3890)
  · rw [show raw62.siteIndex = 3887 from rfl]
    exact lookup3887
  · rw [show raw62.siteIndex = 3887 from rfl]
    exact resolved3887
  · decide
  · decide
  · rfl
  · exact lookup3890
  · decide
private def raw63 := PA215.Census.C039.records[63]
private theorem row63 : destinationAgrees raw63 = true := by
  apply destination_nonterminal (s := site3887) (i := inst3887)
    (p := ⟨[true,false,true,false,true,true,true,false,true,false,true],1,(.dec 0)⟩) (q := (.at 3888)) (e := (.dec 0)) (k := 3888) (next := site3888)
  · rw [show raw63.siteIndex = 3887 from rfl]
    exact lookup3887
  · rw [show raw63.siteIndex = 3887 from rfl]
    exact resolved3887
  · decide
  · decide
  · rfl
  · exact lookup3888
  · decide
private def raw64 := PA215.Census.C039.records[64]
private theorem row64 : destinationAgrees raw64 = true := by
  apply destination_nonterminal (s := site3888) (i := inst3888)
    (p := ⟨[true,false,true,false,true,true,true,false,true,false,true,true],0,(.inc 2)⟩) (q := (.at 3889)) (e := (.inc 2)) (k := 3889) (next := site3889)
  · rw [show raw64.siteIndex = 3888 from rfl]
    exact lookup3888
  · rw [show raw64.siteIndex = 3888 from rfl]
    exact resolved3888
  · decide
  · decide
  · rfl
  · exact lookup3889
  · decide
private def raw65 := PA215.Census.C039.records[65]
private theorem row65 : destinationAgrees raw65 = true := by
  apply destination_nonterminal (s := site3889) (i := inst3889)
    (p := ⟨[true,false,true,false,true,true,true,false,true,false],0,.none⟩) (q := (.at 3887)) (e := .none) (k := 3887) (next := site3887)
  · rw [show raw65.siteIndex = 3889 from rfl]
    exact lookup3889
  · rw [show raw65.siteIndex = 3889 from rfl]
    exact resolved3889
  · decide
  · decide
  · rfl
  · exact lookup3887
  · decide
private def raw66 := PA215.Census.C039.records[66]
private theorem row66 : destinationAgrees raw66 = true := by
  apply destination_nonterminal (s := site3890) (i := inst3890)
    (p := ⟨[true,false,true,false,true,true,true,false,true,true,false,true],0,.none⟩) (q := (.at 3894)) (e := .none) (k := 3894) (next := site3894)
  · rw [show raw66.siteIndex = 3890 from rfl]
    exact lookup3890
  · rw [show raw66.siteIndex = 3890 from rfl]
    exact resolved3890
  · decide
  · decide
  · rfl
  · exact lookup3894
  · decide
private def raw67 := PA215.Census.C039.records[67]
private theorem row67 : destinationAgrees raw67 = true := by
  apply destination_nonterminal (s := site3890) (i := inst3890)
    (p := ⟨[true,false,true,false,true,true,true,false,true,true,false,false,true],1,(.dec 2)⟩) (q := (.at 3891)) (e := (.dec 2)) (k := 3891) (next := site3891)
  · rw [show raw67.siteIndex = 3890 from rfl]
    exact lookup3890
  · rw [show raw67.siteIndex = 3890 from rfl]
    exact resolved3890
  · decide
  · decide
  · rfl
  · exact lookup3891
  · decide
private def raw68 := PA215.Census.C039.records[68]
private theorem row68 : destinationAgrees raw68 = true := by
  apply destination_nonterminal (s := site3891) (i := inst3891)
    (p := ⟨[true,false,true,false,true,true,true,false,true,true,false,false,true,true],0,(.inc 5)⟩) (q := (.at 3892)) (e := (.inc 5)) (k := 3892) (next := site3892)
  · rw [show raw68.siteIndex = 3891 from rfl]
    exact lookup3891
  · rw [show raw68.siteIndex = 3891 from rfl]
    exact resolved3891
  · decide
  · decide
  · rfl
  · exact lookup3892
  · decide
private def raw69 := PA215.Census.C039.records[69]
private theorem row69 : destinationAgrees raw69 = true := by
  apply destination_nonterminal (s := site3892) (i := inst3892)
    (p := ⟨[true,false,true,false,true,true,true,false,true,true,false,false,true,true,true],0,(.inc 8)⟩) (q := (.at 3893)) (e := (.inc 8)) (k := 3893) (next := site3893)
  · rw [show raw69.siteIndex = 3892 from rfl]
    exact lookup3892
  · rw [show raw69.siteIndex = 3892 from rfl]
    exact resolved3892
  · decide
  · decide
  · rfl
  · exact lookup3893
  · decide
private def raw70 := PA215.Census.C039.records[70]
private theorem row70 : destinationAgrees raw70 = true := by
  apply destination_nonterminal (s := site3893) (i := inst3893)
    (p := ⟨[true,false,true,false,true,true,true,false,true,true,false,false],0,.none⟩) (q := (.at 3890)) (e := .none) (k := 3890) (next := site3890)
  · rw [show raw70.siteIndex = 3893 from rfl]
    exact lookup3893
  · rw [show raw70.siteIndex = 3893 from rfl]
    exact resolved3893
  · decide
  · decide
  · rfl
  · exact lookup3890
  · decide
private def raw71 := PA215.Census.C039.records[71]
private theorem row71 : destinationAgrees raw71 = true := by
  apply destination_nonterminal (s := site3894) (i := inst3894)
    (p := ⟨[true,false,true,false,true,true,true,false,true,true,true,false],0,.none⟩) (q := (.at 3900)) (e := .none) (k := 3900) (next := site3900)
  · rw [show raw71.siteIndex = 3894 from rfl]
    exact lookup3894
  · rw [show raw71.siteIndex = 3894 from rfl]
    exact resolved3894
  · decide
  · decide
  · rfl
  · exact lookup3900
  · decide
private def raw72 := PA215.Census.C039.records[72]
private theorem row72 : destinationAgrees raw72 = true := by
  apply destination_nonterminal (s := site3894) (i := inst3894)
    (p := ⟨[true,false,true,false,true,true,true,false,true,true,false,true,true],1,(.dec 8)⟩) (q := (.at 3895)) (e := (.dec 8)) (k := 3895) (next := site3895)
  · rw [show raw72.siteIndex = 3894 from rfl]
    exact lookup3894
  · rw [show raw72.siteIndex = 3894 from rfl]
    exact resolved3894
  · decide
  · decide
  · rfl
  · exact lookup3895
  · decide
private def raw73 := PA215.Census.C039.records[73]
private theorem row73 : destinationAgrees raw73 = true := by
  apply destination_nonterminal (s := site3895) (i := inst3895)
    (p := ⟨[true,false,true,false,true,true,true,false,true,true,false,true,true,false,true],0,(.inc 5)⟩) (q := (.at 3896)) (e := (.inc 5)) (k := 3896) (next := site3896)
  · rw [show raw73.siteIndex = 3895 from rfl]
    exact lookup3895
  · rw [show raw73.siteIndex = 3895 from rfl]
    exact resolved3895
  · decide
  · decide
  · rfl
  · exact lookup3896
  · decide
private def raw74 := PA215.Census.C039.records[74]
private theorem row74 : destinationAgrees raw74 = true := by
  apply destination_nonterminal (s := site3896) (i := inst3896)
    (p := ⟨[true,false,true,false,true,true,true,false,true,true,false,true,true,true,false],0,.none⟩) (q := (.at 3899)) (e := .none) (k := 3899) (next := site3899)
  · rw [show raw74.siteIndex = 3896 from rfl]
    exact lookup3896
  · rw [show raw74.siteIndex = 3896 from rfl]
    exact resolved3896
  · decide
  · decide
  · rfl
  · exact lookup3899
  · decide
private def raw75 := PA215.Census.C039.records[75]
private theorem row75 : destinationAgrees raw75 = true := by
  apply destination_nonterminal (s := site3896) (i := inst3896)
    (p := ⟨[true,false,true,false,true,true,true,false,true,true,false,true,true,false,true,true],1,(.dec 8)⟩) (q := (.at 3897)) (e := (.dec 8)) (k := 3897) (next := site3897)
  · rw [show raw75.siteIndex = 3896 from rfl]
    exact lookup3896
  · rw [show raw75.siteIndex = 3896 from rfl]
    exact resolved3896
  · decide
  · decide
  · rfl
  · exact lookup3897
  · decide
private def raw76 := PA215.Census.C039.records[76]
private theorem row76 : destinationAgrees raw76 = true := by
  apply destination_nonterminal (s := site3897) (i := inst3897)
    (p := ⟨[true,false,true,false,true,true,true,false,true,true,false,true,true,false,true,true,true],0,(.inc 2)⟩) (q := (.at 3898)) (e := (.inc 2)) (k := 3898) (next := site3898)
  · rw [show raw76.siteIndex = 3897 from rfl]
    exact lookup3897
  · rw [show raw76.siteIndex = 3897 from rfl]
    exact resolved3897
  · decide
  · decide
  · rfl
  · exact lookup3898
  · decide
private def raw77 := PA215.Census.C039.records[77]
private theorem row77 : destinationAgrees raw77 = true := by
  apply destination_nonterminal (s := site3898) (i := inst3898)
    (p := ⟨[true,false,true,false,true,true,true,false,true,true,false,true,true,false,true],0,.none⟩) (q := (.at 3896)) (e := .none) (k := 3896) (next := site3896)
  · rw [show raw77.siteIndex = 3898 from rfl]
    exact lookup3898
  · rw [show raw77.siteIndex = 3898 from rfl]
    exact resolved3898
  · decide
  · decide
  · rfl
  · exact lookup3896
  · decide
private def raw78 := PA215.Census.C039.records[78]
private theorem row78 : destinationAgrees raw78 = true := by
  apply destination_nonterminal (s := site3899) (i := inst3899)
    (p := ⟨[true,false,true,false,true,true,true,false,true,true,false],0,.none⟩) (q := (.at 3890)) (e := .none) (k := 3890) (next := site3890)
  · rw [show raw78.siteIndex = 3899 from rfl]
    exact lookup3899
  · rw [show raw78.siteIndex = 3899 from rfl]
    exact resolved3899
  · decide
  · decide
  · rfl
  · exact lookup3890
  · decide
private def raw79 := PA215.Census.C039.records[79]
private theorem row79 : destinationAgrees raw79 = true := by
  apply destination_nonterminal (s := site3900) (i := inst3900)
    (p := ⟨[true,false,true,false,true,true,true,true,false,false,false],0,.none⟩) (q := (.at 3903)) (e := .none) (k := 3903) (next := site3903)
  · rw [show raw79.siteIndex = 3900 from rfl]
    exact lookup3900
  · rw [show raw79.siteIndex = 3900 from rfl]
    exact resolved3900
  · decide
  · decide
  · rfl
  · exact lookup3903
  · decide
private def raw80 := PA215.Census.C039.records[80]
private theorem row80 : destinationAgrees raw80 = true := by
  apply destination_nonterminal (s := site3900) (i := inst3900)
    (p := ⟨[true,false,true,false,true,true,true,false,true,true,true,true],1,(.dec 5)⟩) (q := (.at 3901)) (e := (.dec 5)) (k := 3901) (next := site3901)
  · rw [show raw80.siteIndex = 3900 from rfl]
    exact lookup3900
  · rw [show raw80.siteIndex = 3900 from rfl]
    exact resolved3900
  · decide
  · decide
  · rfl
  · exact lookup3901
  · decide
private def raw81 := PA215.Census.C039.records[81]
private theorem row81 : destinationAgrees raw81 = true := by
  apply destination_nonterminal (s := site3901) (i := inst3901)
    (p := ⟨[true,false,true,false,true,true,true,false,true,true,true,true,true],0,(.inc 0)⟩) (q := (.at 3902)) (e := (.inc 0)) (k := 3902) (next := site3902)
  · rw [show raw81.siteIndex = 3901 from rfl]
    exact lookup3901
  · rw [show raw81.siteIndex = 3901 from rfl]
    exact resolved3901
  · decide
  · decide
  · rfl
  · exact lookup3902
  · decide
private def raw82 := PA215.Census.C039.records[82]
private theorem row82 : destinationAgrees raw82 = true := by
  apply destination_nonterminal (s := site3902) (i := inst3902)
    (p := ⟨[true,false,true,false,true,true,true,false,true,true,true],0,.none⟩) (q := (.at 3900)) (e := .none) (k := 3900) (next := site3900)
  · rw [show raw82.siteIndex = 3902 from rfl]
    exact lookup3902
  · rw [show raw82.siteIndex = 3902 from rfl]
    exact resolved3902
  · decide
  · decide
  · rfl
  · exact lookup3900
  · decide
private def raw83 := PA215.Census.C039.records[83]
private theorem row83 : destinationAgrees raw83 = true := by
  apply destination_nonterminal (s := site3903) (i := inst3903)
    (p := ⟨[true,false,true,false,true,true,true,true,true],0,.none⟩) (q := (.at 3907)) (e := .none) (k := 3907) (next := site3907)
  · rw [show raw83.siteIndex = 3903 from rfl]
    exact lookup3903
  · rw [show raw83.siteIndex = 3903 from rfl]
    exact resolved3903
  · decide
  · decide
  · rfl
  · exact lookup3907
  · decide
private def raw84 := PA215.Census.C039.records[84]
private theorem row84 : destinationAgrees raw84 = true := by
  apply destination_nonterminal (s := site3903) (i := inst3903)
    (p := ⟨[true,false,true,false,true,true,true,true,false,true],1,(.dec 3)⟩) (q := (.at 3904)) (e := (.dec 3)) (k := 3904) (next := site3904)
  · rw [show raw84.siteIndex = 3903 from rfl]
    exact lookup3903
  · rw [show raw84.siteIndex = 3903 from rfl]
    exact resolved3903
  · decide
  · decide
  · rfl
  · exact lookup3904
  · decide
private def raw85 := PA215.Census.C039.records[85]
private theorem row85 : destinationAgrees raw85 = true := by
  apply destination_nonterminal (s := site3904) (i := inst3904)
    (p := ⟨[true,false,true,false,true,true,true,true,false,true,true],0,(.inc 2)⟩) (q := (.at 3905)) (e := (.inc 2)) (k := 3905) (next := site3905)
  · rw [show raw85.siteIndex = 3904 from rfl]
    exact lookup3904
  · rw [show raw85.siteIndex = 3904 from rfl]
    exact resolved3904
  · decide
  · decide
  · rfl
  · exact lookup3905
  · decide
private def raw86 := PA215.Census.C039.records[86]
private theorem row86 : destinationAgrees raw86 = true := by
  apply destination_nonterminal (s := site3905) (i := inst3905)
    (p := ⟨[true,false,true,false,true,true,true,true,false,true,true,true],0,(.inc 8)⟩) (q := (.at 3906)) (e := (.inc 8)) (k := 3906) (next := site3906)
  · rw [show raw86.siteIndex = 3905 from rfl]
    exact lookup3905
  · rw [show raw86.siteIndex = 3905 from rfl]
    exact resolved3905
  · decide
  · decide
  · rfl
  · exact lookup3906
  · decide
private def raw87 := PA215.Census.C039.records[87]
private theorem row87 : destinationAgrees raw87 = true := by
  apply destination_nonterminal (s := site3906) (i := inst3906)
    (p := ⟨[true,false,true,false,true,true,true,true,false],0,.none⟩) (q := (.at 3903)) (e := .none) (k := 3903) (next := site3903)
  · rw [show raw87.siteIndex = 3906 from rfl]
    exact lookup3906
  · rw [show raw87.siteIndex = 3906 from rfl]
    exact resolved3906
  · decide
  · decide
  · rfl
  · exact lookup3903
  · decide
private def raw88 := PA215.Census.C039.records[88]
private theorem row88 : destinationAgrees raw88 = true := by
  apply destination_nonterminal (s := site3907) (i := inst3907)
    (p := ⟨[true,false,true,true,false,false,false,false,false],0,.none⟩) (q := (.at 3910)) (e := .none) (k := 3910) (next := site3910)
  · rw [show raw88.siteIndex = 3907 from rfl]
    exact lookup3907
  · rw [show raw88.siteIndex = 3907 from rfl]
    exact resolved3907
  · decide
  · decide
  · rfl
  · exact lookup3910
  · decide
private def raw89 := PA215.Census.C039.records[89]
private theorem row89 : destinationAgrees raw89 = true := by
  apply destination_nonterminal (s := site3907) (i := inst3907)
    (p := ⟨[true,false,true,false,true,true,true,true,true,true],1,(.dec 8)⟩) (q := (.at 3908)) (e := (.dec 8)) (k := 3908) (next := site3908)
  · rw [show raw89.siteIndex = 3907 from rfl]
    exact lookup3907
  · rw [show raw89.siteIndex = 3907 from rfl]
    exact resolved3907
  · decide
  · decide
  · rfl
  · exact lookup3908
  · decide
private def raw90 := PA215.Census.C039.records[90]
private theorem row90 : destinationAgrees raw90 = true := by
  apply destination_nonterminal (s := site3908) (i := inst3908)
    (p := ⟨[true,false,true,false,true,true,true,true,true,true,true],0,(.inc 3)⟩) (q := (.at 3909)) (e := (.inc 3)) (k := 3909) (next := site3909)
  · rw [show raw90.siteIndex = 3908 from rfl]
    exact lookup3908
  · rw [show raw90.siteIndex = 3908 from rfl]
    exact resolved3908
  · decide
  · decide
  · rfl
  · exact lookup3909
  · decide
private def raw91 := PA215.Census.C039.records[91]
private theorem row91 : destinationAgrees raw91 = true := by
  apply destination_nonterminal (s := site3909) (i := inst3909)
    (p := ⟨[true,false,true,false,true,true,true,true,true],0,.none⟩) (q := (.at 3907)) (e := .none) (k := 3907) (next := site3907)
  · rw [show raw91.siteIndex = 3909 from rfl]
    exact lookup3909
  · rw [show raw91.siteIndex = 3909 from rfl]
    exact resolved3909
  · decide
  · decide
  · rfl
  · exact lookup3907
  · decide
private def raw92 := PA215.Census.C039.records[92]
private theorem row92 : destinationAgrees raw92 = true := by
  apply destination_nonterminal (s := site3910) (i := inst3910)
    (p := ⟨[],0,.none⟩) (q := (.at 0)) (e := .none) (k := 0) (next := site0)
  · rw [show raw92.siteIndex = 3910 from rfl]
    exact lookup3910
  · rw [show raw92.siteIndex = 3910 from rfl]
    exact resolved3910
  · decide
  · decide
  · rfl
  · exact lookup0
  · decide
private def raw93 := PA215.Census.C039.records[93]
private theorem row93 : destinationAgrees raw93 = true := by
  apply destination_nonterminal (s := site3911) (i := inst3911)
    (p := ⟨[true,true,true],0,.none⟩) (q := (.at 3914)) (e := .none) (k := 3914) (next := site3914)
  · rw [show raw93.siteIndex = 3911 from rfl]
    exact lookup3911
  · rw [show raw93.siteIndex = 3911 from rfl]
    exact resolved3911
  · decide
  · decide
  · rfl
  · exact lookup3914
  · decide
private def raw94 := PA215.Census.C039.records[94]
private theorem row94 : destinationAgrees raw94 = true := by
  apply destination_nonterminal (s := site3911) (i := inst3911)
    (p := ⟨[true,true,false,true],1,(.dec 2)⟩) (q := (.at 3912)) (e := (.dec 2)) (k := 3912) (next := site3912)
  · rw [show raw94.siteIndex = 3911 from rfl]
    exact lookup3911
  · rw [show raw94.siteIndex = 3911 from rfl]
    exact resolved3911
  · decide
  · decide
  · rfl
  · exact lookup3912
  · decide
private def raw95 := PA215.Census.C039.records[95]
private theorem row95 : destinationAgrees raw95 = true := by
  apply destination_nonterminal (s := site3912) (i := inst3912)
    (p := ⟨[true,true,false,true,true],0,(.inc 8)⟩) (q := (.at 3913)) (e := (.inc 8)) (k := 3913) (next := site3913)
  · rw [show raw95.siteIndex = 3912 from rfl]
    exact lookup3912
  · rw [show raw95.siteIndex = 3912 from rfl]
    exact resolved3912
  · decide
  · decide
  · rfl
  · exact lookup3913
  · decide
private def raw96 := PA215.Census.C039.records[96]
private theorem row96 : destinationAgrees raw96 = true := by
  apply destination_nonterminal (s := site3913) (i := inst3913)
    (p := ⟨[true,true,false],0,.none⟩) (q := (.at 3911)) (e := .none) (k := 3911) (next := site3911)
  · rw [show raw96.siteIndex = 3913 from rfl]
    exact lookup3913
  · rw [show raw96.siteIndex = 3913 from rfl]
    exact resolved3913
  · decide
  · decide
  · rfl
  · exact lookup3911
  · decide
private def raw97 := PA215.Census.C039.records[97]
private theorem row97 : destinationAgrees raw97 = true := by
  apply destination_nonterminal (s := site3914) (i := inst3914)
    (p := ⟨[true,true,true,false,true],0,.none⟩) (q := (.at 3918)) (e := .none) (k := 3918) (next := site3918)
  · rw [show raw97.siteIndex = 3914 from rfl]
    exact lookup3914
  · rw [show raw97.siteIndex = 3914 from rfl]
    exact resolved3914
  · decide
  · decide
  · rfl
  · exact lookup3918
  · decide
private def raw98 := PA215.Census.C039.records[98]
private theorem row98 : destinationAgrees raw98 = true := by
  apply destination_nonterminal (s := site3914) (i := inst3914)
    (p := ⟨[true,true,true,false,false,true],1,(.dec 7)⟩) (q := (.at 3915)) (e := (.dec 7)) (k := 3915) (next := site3915)
  · rw [show raw98.siteIndex = 3914 from rfl]
    exact lookup3914
  · rw [show raw98.siteIndex = 3914 from rfl]
    exact resolved3914
  · decide
  · decide
  · rfl
  · exact lookup3915
  · decide
private def raw99 := PA215.Census.C039.records[99]
private theorem row99 : destinationAgrees raw99 = true := by
  apply destination_nonterminal (s := site3915) (i := inst3915)
    (p := ⟨[true,true,true,false,false,true,true],0,(.inc 2)⟩) (q := (.at 3916)) (e := (.inc 2)) (k := 3916) (next := site3916)
  · rw [show raw99.siteIndex = 3915 from rfl]
    exact lookup3915
  · rw [show raw99.siteIndex = 3915 from rfl]
    exact resolved3915
  · decide
  · decide
  · rfl
  · exact lookup3916
  · decide
private def raw100 := PA215.Census.C039.records[100]
private theorem row100 : destinationAgrees raw100 = true := by
  apply destination_nonterminal (s := site3916) (i := inst3916)
    (p := ⟨[true,true,true,false,false,true,true,true],0,(.inc 8)⟩) (q := (.at 3917)) (e := (.inc 8)) (k := 3917) (next := site3917)
  · rw [show raw100.siteIndex = 3916 from rfl]
    exact lookup3916
  · rw [show raw100.siteIndex = 3916 from rfl]
    exact resolved3916
  · decide
  · decide
  · rfl
  · exact lookup3917
  · decide
private def raw101 := PA215.Census.C039.records[101]
private theorem row101 : destinationAgrees raw101 = true := by
  apply destination_nonterminal (s := site3917) (i := inst3917)
    (p := ⟨[true,true,true,false,false],0,.none⟩) (q := (.at 3914)) (e := .none) (k := 3914) (next := site3914)
  · rw [show raw101.siteIndex = 3917 from rfl]
    exact lookup3917
  · rw [show raw101.siteIndex = 3917 from rfl]
    exact resolved3917
  · decide
  · decide
  · rfl
  · exact lookup3914
  · decide
private def raw102 := PA215.Census.C039.records[102]
private theorem row102 : destinationAgrees raw102 = true := by
  apply destination_nonterminal (s := site3918) (i := inst3918)
    (p := ⟨[true,true,true,true,false],0,.none⟩) (q := (.at 3921)) (e := .none) (k := 3921) (next := site3921)
  · rw [show raw102.siteIndex = 3918 from rfl]
    exact lookup3918
  · rw [show raw102.siteIndex = 3918 from rfl]
    exact resolved3918
  · decide
  · decide
  · rfl
  · exact lookup3921
  · decide
private def raw103 := PA215.Census.C039.records[103]
private theorem row103 : destinationAgrees raw103 = true := by
  apply destination_nonterminal (s := site3918) (i := inst3918)
    (p := ⟨[true,true,true,false,true,true],1,(.dec 8)⟩) (q := (.at 3919)) (e := (.dec 8)) (k := 3919) (next := site3919)
  · rw [show raw103.siteIndex = 3918 from rfl]
    exact lookup3918
  · rw [show raw103.siteIndex = 3918 from rfl]
    exact resolved3918
  · decide
  · decide
  · rfl
  · exact lookup3919
  · decide
private def raw104 := PA215.Census.C039.records[104]
private theorem row104 : destinationAgrees raw104 = true := by
  apply destination_nonterminal (s := site3919) (i := inst3919)
    (p := ⟨[true,true,true,false,true,true,true],0,(.inc 7)⟩) (q := (.at 3920)) (e := (.inc 7)) (k := 3920) (next := site3920)
  · rw [show raw104.siteIndex = 3919 from rfl]
    exact lookup3919
  · rw [show raw104.siteIndex = 3919 from rfl]
    exact resolved3919
  · decide
  · decide
  · rfl
  · exact lookup3920
  · decide
private def raw105 := PA215.Census.C039.records[105]
private theorem row105 : destinationAgrees raw105 = true := by
  apply destination_nonterminal (s := site3920) (i := inst3920)
    (p := ⟨[true,true,true,false,true],0,.none⟩) (q := (.at 3918)) (e := .none) (k := 3918) (next := site3918)
  · rw [show raw105.siteIndex = 3920 from rfl]
    exact lookup3920
  · rw [show raw105.siteIndex = 3920 from rfl]
    exact resolved3920
  · decide
  · decide
  · rfl
  · exact lookup3918
  · decide
private def raw106 := PA215.Census.C039.records[106]
private theorem row106 : destinationAgrees raw106 = true := by
  apply destination_nonterminal (s := site3921) (i := inst3921)
    (p := ⟨[true,true,true,true,true],0,(.inc 8)⟩) (q := (.at 3922)) (e := (.inc 8)) (k := 3922) (next := site3922)
  · rw [show raw106.siteIndex = 3921 from rfl]
    exact lookup3921
  · rw [show raw106.siteIndex = 3921 from rfl]
    exact resolved3921
  · decide
  · decide
  · rfl
  · exact lookup3922
  · decide
private def raw107 := PA215.Census.C039.records[107]
private theorem row107 : destinationAgrees raw107 = true := by
  apply destination_nonterminal (s := site3922) (i := inst3922)
    (p := ⟨[true,true,true,true,true,false,false,false,true],0,.none⟩) (q := (.at 3926)) (e := .none) (k := 3926) (next := site3926)
  · rw [show raw107.siteIndex = 3922 from rfl]
    exact lookup3922
  · rw [show raw107.siteIndex = 3922 from rfl]
    exact resolved3922
  · decide
  · decide
  · rfl
  · exact lookup3926
  · decide
private def raw108 := PA215.Census.C039.records[108]
private theorem row108 : destinationAgrees raw108 = true := by
  apply destination_nonterminal (s := site3922) (i := inst3922)
    (p := ⟨[true,true,true,true,true,false,false,false,false,true],1,(.dec 7)⟩) (q := (.at 3923)) (e := (.dec 7)) (k := 3923) (next := site3923)
  · rw [show raw108.siteIndex = 3922 from rfl]
    exact lookup3922
  · rw [show raw108.siteIndex = 3922 from rfl]
    exact resolved3922
  · decide
  · decide
  · rfl
  · exact lookup3923
  · decide
private def raw109 := PA215.Census.C039.records[109]
private theorem row109 : destinationAgrees raw109 = true := by
  apply destination_nonterminal (s := site3923) (i := inst3923)
    (p := ⟨[true,true,true,true,true,false,false,false,false,true,true],0,.none⟩) (q := (.at 3925)) (e := .none) (k := 3925) (next := site3925)
  · rw [show raw109.siteIndex = 3923 from rfl]
    exact lookup3923
  · rw [show raw109.siteIndex = 3923 from rfl]
    exact resolved3923
  · decide
  · decide
  · rfl
  · exact lookup3925
  · decide
private def raw110 := PA215.Census.C039.records[110]
private theorem row110 : destinationAgrees raw110 = true := by
  apply destination_nonterminal (s := site3923) (i := inst3923)
    (p := ⟨[true,true,true,true,true,false,false,false,false,true,false,true],1,(.dec 8)⟩) (q := (.at 3924)) (e := (.dec 8)) (k := 3924) (next := site3924)
  · rw [show raw110.siteIndex = 3923 from rfl]
    exact lookup3923
  · rw [show raw110.siteIndex = 3923 from rfl]
    exact resolved3923
  · decide
  · decide
  · rfl
  · exact lookup3924
  · decide
private def raw111 := PA215.Census.C039.records[111]
private theorem row111 : destinationAgrees raw111 = true := by
  apply destination_nonterminal (s := site3924) (i := inst3924)
    (p := ⟨[true,true,true,true,true,false,false,false,false],0,.none⟩) (q := (.at 3922)) (e := .none) (k := 3922) (next := site3922)
  · rw [show raw111.siteIndex = 3924 from rfl]
    exact lookup3924
  · rw [show raw111.siteIndex = 3924 from rfl]
    exact resolved3924
  · decide
  · decide
  · rfl
  · exact lookup3922
  · decide
private def raw112 := PA215.Census.C039.records[112]
private theorem row112 : destinationAgrees raw112 = true := by
  apply destination_nonterminal (s := site3925) (i := inst3925)
    (p := ⟨[true,true,true,true,true,false,false,true],0,.none⟩) (q := (.at 3927)) (e := .none) (k := 3927) (next := site3927)
  · rw [show raw112.siteIndex = 3925 from rfl]
    exact lookup3925
  · rw [show raw112.siteIndex = 3925 from rfl]
    exact resolved3925
  · decide
  · decide
  · rfl
  · exact lookup3927
  · decide
private def raw113 := PA215.Census.C039.records[113]
private theorem row113 : destinationAgrees raw113 = true := by
  apply destination_nonterminal (s := site3926) (i := inst3926)
    (p := ⟨[true,true,true,true,true,false,true],0,.none⟩) (q := (.at 3932)) (e := .none) (k := 3932) (next := site3932)
  · rw [show raw113.siteIndex = 3926 from rfl]
    exact lookup3926
  · rw [show raw113.siteIndex = 3926 from rfl]
    exact resolved3926
  · decide
  · decide
  · rfl
  · exact lookup3932
  · decide
private def raw114 := PA215.Census.C039.records[114]
private theorem row114 : destinationAgrees raw114 = true := by
  apply destination_nonterminal (s := site3926) (i := inst3926)
    (p := ⟨[true,true,true,true,true,false,false,true,false],1,(.dec 8)⟩) (q := (.at 3927)) (e := (.dec 8)) (k := 3927) (next := site3927)
  · rw [show raw114.siteIndex = 3926 from rfl]
    exact lookup3926
  · rw [show raw114.siteIndex = 3926 from rfl]
    exact resolved3926
  · decide
  · decide
  · rfl
  · exact lookup3927
  · decide
private def raw115 := PA215.Census.C039.records[115]
private theorem row115 : destinationAgrees raw115 = true := by
  apply destination_nonterminal (s := site3927) (i := inst3927)
    (p := ⟨[true,true,true,true,true,false,false,true,true],0,.none⟩) (q := (.at 3929)) (e := .none) (k := 3929) (next := site3929)
  · rw [show raw115.siteIndex = 3927 from rfl]
    exact lookup3927
  · rw [show raw115.siteIndex = 3927 from rfl]
    exact resolved3927
  · decide
  · decide
  · rfl
  · exact lookup3929
  · decide
private def raw116 := PA215.Census.C039.records[116]
private theorem row116 : destinationAgrees raw116 = true := by
  apply destination_nonterminal (s := site3927) (i := inst3927)
    (p := ⟨[true,true,true,true,true,false,false,true,false,true],1,(.dec 7)⟩) (q := (.at 3928)) (e := (.dec 7)) (k := 3928) (next := site3928)
  · rw [show raw116.siteIndex = 3927 from rfl]
    exact lookup3927
  · rw [show raw116.siteIndex = 3927 from rfl]
    exact resolved3927
  · decide
  · decide
  · rfl
  · exact lookup3928
  · decide
private def raw117 := PA215.Census.C039.records[117]
private theorem row117 : destinationAgrees raw117 = true := by
  apply destination_nonterminal (s := site3928) (i := inst3928)
    (p := ⟨[true,true,true,true,true,false,false,true,false],0,.none⟩) (q := (.at 3927)) (e := .none) (k := 3927) (next := site3927)
  · rw [show raw117.siteIndex = 3928 from rfl]
    exact lookup3928
  · rw [show raw117.siteIndex = 3928 from rfl]
    exact resolved3928
  · decide
  · decide
  · rfl
  · exact lookup3927
  · decide
private def raw118 := PA215.Census.C039.records[118]
private theorem row118 : destinationAgrees raw118 = true := by
  apply destination_nonterminal (s := site3929) (i := inst3929)
    (p := ⟨[true,true,true,true,true,false,false,true,true,true],0,.none⟩) (q := (.at 3931)) (e := .none) (k := 3931) (next := site3931)
  · rw [show raw118.siteIndex = 3929 from rfl]
    exact lookup3929
  · rw [show raw118.siteIndex = 3929 from rfl]
    exact resolved3929
  · decide
  · decide
  · rfl
  · exact lookup3931
  · decide
private def raw119 := PA215.Census.C039.records[119]
private theorem row119 : destinationAgrees raw119 = true := by
  apply destination_nonterminal (s := site3929) (i := inst3929)
    (p := ⟨[true,true,true,true,true,false,false,true,true,false,true],1,(.dec 8)⟩) (q := (.at 3930)) (e := (.dec 8)) (k := 3930) (next := site3930)
  · rw [show raw119.siteIndex = 3929 from rfl]
    exact lookup3929
  · rw [show raw119.siteIndex = 3929 from rfl]
    exact resolved3929
  · decide
  · decide
  · rfl
  · exact lookup3930
  · decide
private def raw120 := PA215.Census.C039.records[120]
private theorem row120 : destinationAgrees raw120 = true := by
  apply destination_nonterminal (s := site3930) (i := inst3930)
    (p := ⟨[true,true,true,true,true,false,false,true],0,.none⟩) (q := (.at 3927)) (e := .none) (k := 3927) (next := site3927)
  · rw [show raw120.siteIndex = 3930 from rfl]
    exact lookup3930
  · rw [show raw120.siteIndex = 3930 from rfl]
    exact resolved3930
  · decide
  · decide
  · rfl
  · exact lookup3927
  · decide
private def raw121 := PA215.Census.C039.records[121]
private theorem row121 : destinationAgrees raw121 = true := by
  apply destination_nonterminal (s := site3931) (i := inst3931)
    (p := ⟨[true,true,true,true,true,true],0,.none⟩) (q := (.at 3933)) (e := .none) (k := 3933) (next := site3933)
  · rw [show raw121.siteIndex = 3931 from rfl]
    exact lookup3931
  · rw [show raw121.siteIndex = 3931 from rfl]
    exact resolved3931
  · decide
  · decide
  · rfl
  · exact lookup3933
  · decide
private def raw122 := PA215.Census.C039.records[122]
private theorem row122 : destinationAgrees raw122 = true := by
  apply destination_terminal (s := site3932) (i := inst3932)
  · rw [show raw122.siteIndex = 3932 from rfl]
    exact lookup3932
  · rw [show raw122.siteIndex = 3932 from rfl]
    exact resolved3932
  · decide
  · decide
private def raw123 := PA215.Census.C039.records[123]
private theorem row123 : destinationAgrees raw123 = true := by
  apply destination_nonterminal (s := site3933) (i := inst3933)
    (p := ⟨[true,true,true,true,true,true,false,true],0,.none⟩) (q := (.at 3941)) (e := .none) (k := 3941) (next := site3941)
  · rw [show raw123.siteIndex = 3933 from rfl]
    exact lookup3933
  · rw [show raw123.siteIndex = 3933 from rfl]
    exact resolved3933
  · decide
  · decide
  · rfl
  · exact lookup3941
  · decide
private def raw124 := PA215.Census.C039.records[124]
private theorem row124 : destinationAgrees raw124 = true := by
  apply destination_nonterminal (s := site3933) (i := inst3933)
    (p := ⟨[true,true,true,true,true,true,false,false,true],1,(.dec 0)⟩) (q := (.at 3934)) (e := (.dec 0)) (k := 3934) (next := site3934)
  · rw [show raw124.siteIndex = 3933 from rfl]
    exact lookup3933
  · rw [show raw124.siteIndex = 3933 from rfl]
    exact resolved3933
  · decide
  · decide
  · rfl
  · exact lookup3934
  · decide
private def raw125 := PA215.Census.C039.records[125]
private theorem row125 : destinationAgrees raw125 = true := by
  apply destination_nonterminal (s := site3934) (i := inst3934)
    (p := ⟨[true,true,true,true,true,true,false,false,true,true],0,(.inc 5)⟩) (q := (.at 3935)) (e := (.inc 5)) (k := 3935) (next := site3935)
  · rw [show raw125.siteIndex = 3934 from rfl]
    exact lookup3934
  · rw [show raw125.siteIndex = 3934 from rfl]
    exact resolved3934
  · decide
  · decide
  · rfl
  · exact lookup3935
  · decide
private def raw126 := PA215.Census.C039.records[126]
private theorem row126 : destinationAgrees raw126 = true := by
  apply destination_nonterminal (s := site3935) (i := inst3935)
    (p := ⟨[true,true,true,true,true,true,false,false,true,true,false,true],0,.none⟩) (q := (.at 3937)) (e := .none) (k := 3937) (next := site3937)
  · rw [show raw126.siteIndex = 3935 from rfl]
    exact lookup3935
  · rw [show raw126.siteIndex = 3935 from rfl]
    exact resolved3935
  · decide
  · decide
  · rfl
  · exact lookup3937
  · decide
private def raw127 := PA215.Census.C039.records[127]
private theorem row127 : destinationAgrees raw127 = true := by
  apply destination_nonterminal (s := site3935) (i := inst3935)
    (p := ⟨[true,true,true,true,true,true,false,false,true,true,false,false,true],1,(.dec 8)⟩) (q := (.at 3936)) (e := (.dec 8)) (k := 3936) (next := site3936)
  · rw [show raw127.siteIndex = 3935 from rfl]
    exact lookup3935
  · rw [show raw127.siteIndex = 3935 from rfl]
    exact resolved3935
  · decide
  · decide
  · rfl
  · exact lookup3936
  · decide
private theorem enumeration : PA215.Census.C039.records.toList = [raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7,raw8,raw9,raw10,raw11,raw12,raw13,raw14,raw15,raw16,raw17,raw18,raw19,raw20,raw21,raw22,raw23,raw24,raw25,raw26,raw27,raw28,raw29,raw30,raw31,raw32,raw33,raw34,raw35,raw36,raw37,raw38,raw39,raw40,raw41,raw42,raw43,raw44,raw45,raw46,raw47,raw48,raw49,raw50,raw51,raw52,raw53,raw54,raw55,raw56,raw57,raw58,raw59,raw60,raw61,raw62,raw63,raw64,raw65,raw66,raw67,raw68,raw69,raw70,raw71,raw72,raw73,raw74,raw75,raw76,raw77,raw78,raw79,raw80,raw81,raw82,raw83,raw84,raw85,raw86,raw87,raw88,raw89,raw90,raw91,raw92,raw93,raw94,raw95,raw96,raw97,raw98,raw99,raw100,raw101,raw102,raw103,raw104,raw105,raw106,raw107,raw108,raw109,raw110,raw111,raw112,raw113,raw114,raw115,raw116,raw117,raw118,raw119,raw120,raw121,raw122,raw123,raw124,raw125,raw126,raw127] := by rfl
theorem checked : PA215.Census.C039.records.toList.all destinationAgrees = true := by
  rw [enumeration]
  simp only [List.all_cons,List.all_nil,row0,row1,row2,row3,row4,row5,row6,row7,row8,row9,row10,row11,row12,row13,row14,row15,row16,row17,row18,row19,row20,row21,row22,row23,row24,row25,row26,row27,row28,row29,row30,row31,row32,row33,row34,row35,row36,row37,row38,row39,row40,row41,row42,row43,row44,row45,row46,row47,row48,row49,row50,row51,row52,row53,row54,row55,row56,row57,row58,row59,row60,row61,row62,row63,row64,row65,row66,row67,row68,row69,row70,row71,row72,row73,row74,row75,row76,row77,row78,row79,row80,row81,row82,row83,row84,row85,row86,row87,row88,row89,row90,row91,row92,row93,row94,row95,row96,row97,row98,row99,row100,row101,row102,row103,row104,row105,row106,row107,row108,row109,row110,row111,row112,row113,row114,row115,row116,row117,row118,row119,row120,row121,row122,row123,row124,row125,row126,row127,Bool.and_self]
#print axioms checked
end PA215.Source.DestinationJoin.D039
