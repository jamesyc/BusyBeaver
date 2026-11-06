import PA215.Source.DestinationCertificate
import PA215.Census.C031
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA215.Source.DestinationJoin.D031
private def site3048 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,false,true,true,false,false,false],.dec 1⟩
private theorem lookup3048 : exactSites[3048]? = some site3048 := by rfl
private def site3054 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,false,true,true,false,true,true,false,true,false],.dec 6⟩
private theorem lookup3054 : exactSites[3054]? = some site3054 := by rfl
private def site3055 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,false,true,true,false,true,true,false,true,true,false],.inc 1⟩
private theorem lookup3055 : exactSites[3055]? = some site3055 := by rfl
private def site3056 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,false,true,true,false,true,true,false,true,true,true],.continueTo 2⟩
private theorem lookup3056 : exactSites[3056]? = some site3056 := by rfl
private def site3057 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,false,true,true,false,true,true,true],.continueTo 3⟩
private theorem lookup3057 : exactSites[3057]? = some site3057 := by rfl
private def site3058 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,false,true,true,true,false],.dec 7⟩
private theorem lookup3058 : exactSites[3058]? = some site3058 := by rfl
private def site3059 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,false,true,true,true,true,false],.inc 2⟩
private theorem lookup3059 : exactSites[3059]? = some site3059 := by rfl
private def site3060 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,false,true,true,true,true,true],.continueTo 2⟩
private theorem lookup3060 : exactSites[3060]? = some site3060 := by rfl
private def site3061 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,true,false,false],.dec 3⟩
private theorem lookup3061 : exactSites[3061]? = some site3061 := by rfl
private def site3062 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,true,false,true,false],.inc 1⟩
private theorem lookup3062 : exactSites[3062]? = some site3062 := by rfl
private def site3063 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,true,false,true,true,false],.inc 6⟩
private theorem lookup3063 : exactSites[3063]? = some site3063 := by rfl
private def site3064 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,true,false,true,true,true],.continueTo 3⟩
private theorem lookup3064 : exactSites[3064]? = some site3064 := by rfl
private def site3065 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,true,true,false],.dec 6⟩
private theorem lookup3065 : exactSites[3065]? = some site3065 := by rfl
private def site3066 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,true,true,true,false],.inc 3⟩
private theorem lookup3066 : exactSites[3066]? = some site3066 := by rfl
private def site3067 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,true,true,true,true],.continueTo 2⟩
private theorem lookup3067 : exactSites[3067]? = some site3067 := by rfl
private def site3068 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,false,false],.dec 1⟩
private theorem lookup3068 : exactSites[3068]? = some site3068 := by rfl
private def site3069 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,false,true,false],.inc 6⟩
private theorem lookup3069 : exactSites[3069]? = some site3069 := by rfl
private def site3070 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,false,true,true],.continueTo 2⟩
private theorem lookup3070 : exactSites[3070]? = some site3070 := by rfl
private def site3071 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,false,false],.dec 2⟩
private theorem lookup3071 : exactSites[3071]? = some site3071 := by rfl
private def site3072 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,false,true,false],.inc 1⟩
private theorem lookup3072 : exactSites[3072]? = some site3072 := by rfl
private def site3073 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,false,true,true],.continueTo 2⟩
private theorem lookup3073 : exactSites[3073]? = some site3073 := by rfl
private def site3074 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,false,false,false],.dec 1⟩
private theorem lookup3074 : exactSites[3074]? = some site3074 := by rfl
private def site3075 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,false,false,true,false],.inc 7⟩
private theorem lookup3075 : exactSites[3075]? = some site3075 := by rfl
private def site3076 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,false,false,true,true,false],.inc 6⟩
private theorem lookup3076 : exactSites[3076]? = some site3076 := by rfl
private def site3077 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,false,false,true,true,true],.continueTo 3⟩
private theorem lookup3077 : exactSites[3077]? = some site3077 := by rfl
private def site3078 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,false,true,false],.dec 6⟩
private theorem lookup3078 : exactSites[3078]? = some site3078 := by rfl
private def site3079 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,false,true,true,false,false],.inc 7⟩
private theorem lookup3079 : exactSites[3079]? = some site3079 := by rfl
private def site3080 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,false,true,true,false,true,false],.dec 6⟩
private theorem lookup3080 : exactSites[3080]? = some site3080 := by rfl
private def site3081 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,false,true,true,false,true,true,false],.inc 1⟩
private theorem lookup3081 : exactSites[3081]? = some site3081 := by rfl
private def site3082 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,false,true,true,false,true,true,true],.continueTo 2⟩
private theorem lookup3082 : exactSites[3082]? = some site3082 := by rfl
private def site3083 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,false,true,true,true],.continueTo 3⟩
private theorem lookup3083 : exactSites[3083]? = some site3083 := by rfl
private def site3084 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,true,false],.dec 7⟩
private theorem lookup3084 : exactSites[3084]? = some site3084 := by rfl
private def site3085 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,true,true,false],.inc 2⟩
private theorem lookup3085 : exactSites[3085]? = some site3085 := by rfl
private def site3086 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,true,true,true],.continueTo 2⟩
private theorem lookup3086 : exactSites[3086]? = some site3086 := by rfl
private def site3087 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,true,false,false],.dec 5⟩
private theorem lookup3087 : exactSites[3087]? = some site3087 := by rfl
private def site3088 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,true,false,true,false],.inc 1⟩
private theorem lookup3088 : exactSites[3088]? = some site3088 := by rfl
private def site3089 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,true,false,true,true,false],.inc 6⟩
private theorem lookup3089 : exactSites[3089]? = some site3089 := by rfl
private def site3090 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,true,false,true,true,true],.continueTo 3⟩
private theorem lookup3090 : exactSites[3090]? = some site3090 := by rfl
private def site3091 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,true,true,false],.dec 6⟩
private theorem lookup3091 : exactSites[3091]? = some site3091 := by rfl
private def site3092 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,true,true,true,false],.inc 5⟩
private theorem lookup3092 : exactSites[3092]? = some site3092 := by rfl
private def site3093 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,true,true,true,true],.continueTo 2⟩
private theorem lookup3093 : exactSites[3093]? = some site3093 := by rfl
private def site3094 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,false,false,false],.dec 2⟩
private theorem lookup3094 : exactSites[3094]? = some site3094 := by rfl
private def site3095 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,false,false,true,false],.inc 7⟩
private theorem lookup3095 : exactSites[3095]? = some site3095 := by rfl
private def site3096 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,false,false,true,true,false,false,false],.dec 6⟩
private theorem lookup3096 : exactSites[3096]? = some site3096 := by rfl
private def site3097 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,false,false,true,true,false,false,true],.breakTo 1⟩
private theorem lookup3097 : exactSites[3097]? = some site3097 := by rfl
private def site3098 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,false,false,true,true,false,true,false],.dec 7⟩
private theorem lookup3098 : exactSites[3098]? = some site3098 := by rfl
private def site3099 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,false,false,true,true,false,true,true,false],.inc 6⟩
private theorem lookup3099 : exactSites[3099]? = some site3099 := by rfl
private def site3100 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,false,false,true,true,false,true,true,true],.continueTo 2⟩
private theorem lookup3100 : exactSites[3100]? = some site3100 := by rfl
private def site3101 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,false,false,true,true,true],.continueTo 3⟩
private theorem lookup3101 : exactSites[3101]? = some site3101 := by rfl
private def site3102 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,false,true,false],.dec 7⟩
private theorem lookup3102 : exactSites[3102]? = some site3102 := by rfl
private def site3103 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,false,true,true,false],.inc 2⟩
private theorem lookup3103 : exactSites[3103]? = some site3103 := by rfl
private def site3104 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,false,true,true,true],.continueTo 2⟩
private theorem lookup3104 : exactSites[3104]? = some site3104 := by rfl
private def site3105 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,false,false,false],.dec 1⟩
private theorem lookup3105 : exactSites[3105]? = some site3105 := by rfl
private def site3106 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,false,false,true,false],.inc 7⟩
private theorem lookup3106 : exactSites[3106]? = some site3106 := by rfl
private def site3107 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,false,false,true,true,false],.inc 6⟩
private theorem lookup3107 : exactSites[3107]? = some site3107 := by rfl
private def site3108 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,false,false,true,true,true],.continueTo 3⟩
private theorem lookup3108 : exactSites[3108]? = some site3108 := by rfl
private def site3109 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,false,true,false],.dec 6⟩
private theorem lookup3109 : exactSites[3109]? = some site3109 := by rfl
private def site3110 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,false,true,true,false,false],.inc 7⟩
private theorem lookup3110 : exactSites[3110]? = some site3110 := by rfl
private def site3111 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,false,true,true,false,true,false],.dec 6⟩
private theorem lookup3111 : exactSites[3111]? = some site3111 := by rfl
private def site3112 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,false,true,true,false,true,true,false],.inc 1⟩
private theorem lookup3112 : exactSites[3112]? = some site3112 := by rfl
private def site3113 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,false,true,true,false,true,true,true],.continueTo 2⟩
private theorem lookup3113 : exactSites[3113]? = some site3113 := by rfl
private def site3114 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,false,true,true,true],.continueTo 3⟩
private theorem lookup3114 : exactSites[3114]? = some site3114 := by rfl
private def site3115 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,true,false],.dec 7⟩
private theorem lookup3115 : exactSites[3115]? = some site3115 := by rfl
private def site3116 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,true,true,false,false,false],.inc 1⟩
private theorem lookup3116 : exactSites[3116]? = some site3116 := by rfl
private def site3117 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,true,true,false,false,true],.inc 1⟩
private theorem lookup3117 : exactSites[3117]? = some site3117 := by rfl
private def site3118 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,true,true,false,true,false],.inc 1⟩
private theorem lookup3118 : exactSites[3118]? = some site3118 := by rfl
private def site3119 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,true,true,false,true,true],.inc 1⟩
private theorem lookup3119 : exactSites[3119]? = some site3119 := by rfl
private def site3120 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,true,true,true],.continueTo 2⟩
private theorem lookup3120 : exactSites[3120]? = some site3120 := by rfl
private def site3121 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,true],.inc 1⟩
private theorem lookup3121 : exactSites[3121]? = some site3121 := by rfl
private def site3122 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,false,false,false],.dec 2⟩
private theorem lookup3122 : exactSites[3122]? = some site3122 := by rfl
private def site3123 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,false,false,true,false],.inc 7⟩
private theorem lookup3123 : exactSites[3123]? = some site3123 := by rfl
private def site3124 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,false,false,true,true,false,false,false],.dec 6⟩
private theorem lookup3124 : exactSites[3124]? = some site3124 := by rfl
private def site3125 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,false,false,true,true,false,false,true],.breakTo 1⟩
private theorem lookup3125 : exactSites[3125]? = some site3125 := by rfl
private def site3126 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,false,false,true,true,false,true,false],.dec 7⟩
private theorem lookup3126 : exactSites[3126]? = some site3126 := by rfl
private def site3127 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,false,false,true,true,false,true,true,false],.inc 6⟩
private theorem lookup3127 : exactSites[3127]? = some site3127 := by rfl
private def site3128 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,false,false,true,true,false,true,true,true],.continueTo 2⟩
private theorem lookup3128 : exactSites[3128]? = some site3128 := by rfl
private def site3129 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,false,false,true,true,true],.continueTo 3⟩
private theorem lookup3129 : exactSites[3129]? = some site3129 := by rfl
private def site3130 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,false,true,false],.dec 7⟩
private theorem lookup3130 : exactSites[3130]? = some site3130 := by rfl
private def site3131 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,false,true,true,false],.inc 2⟩
private theorem lookup3131 : exactSites[3131]? = some site3131 := by rfl
private def site3132 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,false,true,true,true],.continueTo 2⟩
private theorem lookup3132 : exactSites[3132]? = some site3132 := by rfl
private def site3133 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,false,false,false],.dec 1⟩
private theorem lookup3133 : exactSites[3133]? = some site3133 := by rfl
private def site3134 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,false,false,true,false],.inc 7⟩
private theorem lookup3134 : exactSites[3134]? = some site3134 := by rfl
private def site3135 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,false,false,true,true,false],.inc 6⟩
private theorem lookup3135 : exactSites[3135]? = some site3135 := by rfl
private def site3136 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,false,false,true,true,true],.continueTo 3⟩
private theorem lookup3136 : exactSites[3136]? = some site3136 := by rfl
private def site3137 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,false,true,false],.dec 6⟩
private theorem lookup3137 : exactSites[3137]? = some site3137 := by rfl
private def site3138 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,false],.inc 7⟩
private theorem lookup3138 : exactSites[3138]? = some site3138 := by rfl
private def site3139 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,true,false],.dec 6⟩
private theorem lookup3139 : exactSites[3139]? = some site3139 := by rfl
private def site3140 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,true,true,false],.inc 1⟩
private theorem lookup3140 : exactSites[3140]? = some site3140 := by rfl
private def site3141 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,true,true,true],.continueTo 2⟩
private theorem lookup3141 : exactSites[3141]? = some site3141 := by rfl
private def site3142 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true],.continueTo 3⟩
private theorem lookup3142 : exactSites[3142]? = some site3142 := by rfl
private def site3143 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,true,false],.dec 7⟩
private theorem lookup3143 : exactSites[3143]? = some site3143 := by rfl
private def site3144 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,true,true,false,false,false],.inc 1⟩
private theorem lookup3144 : exactSites[3144]? = some site3144 := by rfl
private def site3145 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,true,true,false,false,true],.inc 1⟩
private theorem lookup3145 : exactSites[3145]? = some site3145 := by rfl
private def site3146 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,true,true,false,true,false],.inc 1⟩
private theorem lookup3146 : exactSites[3146]? = some site3146 := by rfl
private def site3147 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,true,true,false,true,true],.inc 1⟩
private theorem lookup3147 : exactSites[3147]? = some site3147 := by rfl
private def site3148 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,true,true,true],.continueTo 2⟩
private theorem lookup3148 : exactSites[3148]? = some site3148 := by rfl
private def site3149 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,true,false,false,false],.dec 2⟩
private theorem lookup3149 : exactSites[3149]? = some site3149 := by rfl
private def site3150 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,true,false,false,true,false],.inc 7⟩
private theorem lookup3150 : exactSites[3150]? = some site3150 := by rfl
private def site3151 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,true,false,false,true,true,false,false,false],.dec 6⟩
private theorem lookup3151 : exactSites[3151]? = some site3151 := by rfl
private def site3152 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,true,false,false,true,true,false,false,true],.breakTo 1⟩
private theorem lookup3152 : exactSites[3152]? = some site3152 := by rfl
private def site3153 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,true,false,false,true,true,false,true,false],.dec 7⟩
private theorem lookup3153 : exactSites[3153]? = some site3153 := by rfl
private def site3156 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,true,false,false,true,true,true],.continueTo 3⟩
private theorem lookup3156 : exactSites[3156]? = some site3156 := by rfl
private def site3157 : Site := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,true,false,true,false],.dec 7⟩
private theorem lookup3157 : exactSites[3157]? = some site3157 := by rfl
private def inst3055 : Instruction := .inc 1 (some 3056)
private theorem resolved3055 : resolveAt exactSites 3055 = some inst3055 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3055]
  rfl
private def inst3056 : Instruction := .jump (some 3054)
private theorem resolved3056 : resolveAt exactSites 3056 = some inst3056 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3056]
  rfl
private def inst3057 : Instruction := .jump (some 3048)
private theorem resolved3057 : resolveAt exactSites 3057 = some inst3057 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3057]
  rfl
private def inst3058 : Instruction := .dec 7 (some 3061) (some 3059)
private theorem resolved3058 : resolveAt exactSites 3058 = some inst3058 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3058]
  rfl
private def inst3059 : Instruction := .inc 2 (some 3060)
private theorem resolved3059 : resolveAt exactSites 3059 = some inst3059 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3059]
  rfl
private def inst3060 : Instruction := .jump (some 3058)
private theorem resolved3060 : resolveAt exactSites 3060 = some inst3060 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3060]
  rfl
private def inst3061 : Instruction := .dec 3 (some 3065) (some 3062)
private theorem resolved3061 : resolveAt exactSites 3061 = some inst3061 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3061]
  rfl
private def inst3062 : Instruction := .inc 1 (some 3063)
private theorem resolved3062 : resolveAt exactSites 3062 = some inst3062 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3062]
  rfl
private def inst3063 : Instruction := .inc 6 (some 3064)
private theorem resolved3063 : resolveAt exactSites 3063 = some inst3063 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3063]
  rfl
private def inst3064 : Instruction := .jump (some 3061)
private theorem resolved3064 : resolveAt exactSites 3064 = some inst3064 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3064]
  rfl
private def inst3065 : Instruction := .dec 6 (some 3068) (some 3066)
private theorem resolved3065 : resolveAt exactSites 3065 = some inst3065 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3065]
  rfl
private def inst3066 : Instruction := .inc 3 (some 3067)
private theorem resolved3066 : resolveAt exactSites 3066 = some inst3066 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3066]
  rfl
private def inst3067 : Instruction := .jump (some 3065)
private theorem resolved3067 : resolveAt exactSites 3067 = some inst3067 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3067]
  rfl
private def inst3068 : Instruction := .dec 1 (some 3071) (some 3069)
private theorem resolved3068 : resolveAt exactSites 3068 = some inst3068 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3068]
  rfl
private def inst3069 : Instruction := .inc 6 (some 3070)
private theorem resolved3069 : resolveAt exactSites 3069 = some inst3069 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3069]
  rfl
private def inst3070 : Instruction := .jump (some 3068)
private theorem resolved3070 : resolveAt exactSites 3070 = some inst3070 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3070]
  rfl
private def inst3071 : Instruction := .dec 2 (some 3074) (some 3072)
private theorem resolved3071 : resolveAt exactSites 3071 = some inst3071 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3071]
  rfl
private def inst3072 : Instruction := .inc 1 (some 3073)
private theorem resolved3072 : resolveAt exactSites 3072 = some inst3072 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3072]
  rfl
private def inst3073 : Instruction := .jump (some 3071)
private theorem resolved3073 : resolveAt exactSites 3073 = some inst3073 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3073]
  rfl
private def inst3074 : Instruction := .dec 1 (some 3078) (some 3075)
private theorem resolved3074 : resolveAt exactSites 3074 = some inst3074 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3074]
  rfl
private def inst3075 : Instruction := .inc 7 (some 3076)
private theorem resolved3075 : resolveAt exactSites 3075 = some inst3075 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3075]
  rfl
private def inst3076 : Instruction := .inc 6 (some 3077)
private theorem resolved3076 : resolveAt exactSites 3076 = some inst3076 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3076]
  rfl
private def inst3077 : Instruction := .jump (some 3074)
private theorem resolved3077 : resolveAt exactSites 3077 = some inst3077 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3077]
  rfl
private def inst3078 : Instruction := .dec 6 (some 3084) (some 3079)
private theorem resolved3078 : resolveAt exactSites 3078 = some inst3078 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3078]
  rfl
private def inst3079 : Instruction := .inc 7 (some 3080)
private theorem resolved3079 : resolveAt exactSites 3079 = some inst3079 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3079]
  rfl
private def inst3080 : Instruction := .dec 6 (some 3083) (some 3081)
private theorem resolved3080 : resolveAt exactSites 3080 = some inst3080 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3080]
  rfl
private def inst3081 : Instruction := .inc 1 (some 3082)
private theorem resolved3081 : resolveAt exactSites 3081 = some inst3081 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3081]
  rfl
private def inst3082 : Instruction := .jump (some 3080)
private theorem resolved3082 : resolveAt exactSites 3082 = some inst3082 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3082]
  rfl
private def inst3083 : Instruction := .jump (some 3074)
private theorem resolved3083 : resolveAt exactSites 3083 = some inst3083 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3083]
  rfl
private def inst3084 : Instruction := .dec 7 (some 3087) (some 3085)
private theorem resolved3084 : resolveAt exactSites 3084 = some inst3084 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3084]
  rfl
private def inst3085 : Instruction := .inc 2 (some 3086)
private theorem resolved3085 : resolveAt exactSites 3085 = some inst3085 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3085]
  rfl
private def inst3086 : Instruction := .jump (some 3084)
private theorem resolved3086 : resolveAt exactSites 3086 = some inst3086 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3086]
  rfl
private def inst3087 : Instruction := .dec 5 (some 3091) (some 3088)
private theorem resolved3087 : resolveAt exactSites 3087 = some inst3087 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3087]
  rfl
private def inst3088 : Instruction := .inc 1 (some 3089)
private theorem resolved3088 : resolveAt exactSites 3088 = some inst3088 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3088]
  rfl
private def inst3089 : Instruction := .inc 6 (some 3090)
private theorem resolved3089 : resolveAt exactSites 3089 = some inst3089 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3089]
  rfl
private def inst3090 : Instruction := .jump (some 3087)
private theorem resolved3090 : resolveAt exactSites 3090 = some inst3090 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3090]
  rfl
private def inst3091 : Instruction := .dec 6 (some 3094) (some 3092)
private theorem resolved3091 : resolveAt exactSites 3091 = some inst3091 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3091]
  rfl
private def inst3092 : Instruction := .inc 5 (some 3093)
private theorem resolved3092 : resolveAt exactSites 3092 = some inst3092 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3092]
  rfl
private def inst3093 : Instruction := .jump (some 3091)
private theorem resolved3093 : resolveAt exactSites 3093 = some inst3093 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3093]
  rfl
private def inst3094 : Instruction := .dec 2 (some 3102) (some 3095)
private theorem resolved3094 : resolveAt exactSites 3094 = some inst3094 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3094]
  rfl
private def inst3095 : Instruction := .inc 7 (some 3096)
private theorem resolved3095 : resolveAt exactSites 3095 = some inst3095 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3095]
  rfl
private def inst3096 : Instruction := .dec 6 (some 3098) (some 3097)
private theorem resolved3096 : resolveAt exactSites 3096 = some inst3096 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3096]
  rfl
private def inst3097 : Instruction := .jump (some 3101)
private theorem resolved3097 : resolveAt exactSites 3097 = some inst3097 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3097]
  rfl
private def inst3098 : Instruction := .dec 7 (some 3101) (some 3099)
private theorem resolved3098 : resolveAt exactSites 3098 = some inst3098 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3098]
  rfl
private def inst3099 : Instruction := .inc 6 (some 3100)
private theorem resolved3099 : resolveAt exactSites 3099 = some inst3099 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3099]
  rfl
private def inst3100 : Instruction := .jump (some 3098)
private theorem resolved3100 : resolveAt exactSites 3100 = some inst3100 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3100]
  rfl
private def inst3101 : Instruction := .jump (some 3094)
private theorem resolved3101 : resolveAt exactSites 3101 = some inst3101 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3101]
  rfl
private def inst3102 : Instruction := .dec 7 (some 3105) (some 3103)
private theorem resolved3102 : resolveAt exactSites 3102 = some inst3102 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3102]
  rfl
private def inst3103 : Instruction := .inc 2 (some 3104)
private theorem resolved3103 : resolveAt exactSites 3103 = some inst3103 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3103]
  rfl
private def inst3104 : Instruction := .jump (some 3102)
private theorem resolved3104 : resolveAt exactSites 3104 = some inst3104 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3104]
  rfl
private def inst3105 : Instruction := .dec 1 (some 3109) (some 3106)
private theorem resolved3105 : resolveAt exactSites 3105 = some inst3105 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3105]
  rfl
private def inst3106 : Instruction := .inc 7 (some 3107)
private theorem resolved3106 : resolveAt exactSites 3106 = some inst3106 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3106]
  rfl
private def inst3107 : Instruction := .inc 6 (some 3108)
private theorem resolved3107 : resolveAt exactSites 3107 = some inst3107 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3107]
  rfl
private def inst3108 : Instruction := .jump (some 3105)
private theorem resolved3108 : resolveAt exactSites 3108 = some inst3108 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3108]
  rfl
private def inst3109 : Instruction := .dec 6 (some 3115) (some 3110)
private theorem resolved3109 : resolveAt exactSites 3109 = some inst3109 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3109]
  rfl
private def inst3110 : Instruction := .inc 7 (some 3111)
private theorem resolved3110 : resolveAt exactSites 3110 = some inst3110 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3110]
  rfl
private def inst3111 : Instruction := .dec 6 (some 3114) (some 3112)
private theorem resolved3111 : resolveAt exactSites 3111 = some inst3111 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3111]
  rfl
private def inst3112 : Instruction := .inc 1 (some 3113)
private theorem resolved3112 : resolveAt exactSites 3112 = some inst3112 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3112]
  rfl
private def inst3113 : Instruction := .jump (some 3111)
private theorem resolved3113 : resolveAt exactSites 3113 = some inst3113 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3113]
  rfl
private def inst3114 : Instruction := .jump (some 3105)
private theorem resolved3114 : resolveAt exactSites 3114 = some inst3114 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3114]
  rfl
private def inst3115 : Instruction := .dec 7 (some 3121) (some 3116)
private theorem resolved3115 : resolveAt exactSites 3115 = some inst3115 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3115]
  rfl
private def inst3116 : Instruction := .inc 1 (some 3117)
private theorem resolved3116 : resolveAt exactSites 3116 = some inst3116 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3116]
  rfl
private def inst3117 : Instruction := .inc 1 (some 3118)
private theorem resolved3117 : resolveAt exactSites 3117 = some inst3117 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3117]
  rfl
private def inst3118 : Instruction := .inc 1 (some 3119)
private theorem resolved3118 : resolveAt exactSites 3118 = some inst3118 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3118]
  rfl
private def inst3119 : Instruction := .inc 1 (some 3120)
private theorem resolved3119 : resolveAt exactSites 3119 = some inst3119 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3119]
  rfl
private def inst3120 : Instruction := .jump (some 3115)
private theorem resolved3120 : resolveAt exactSites 3120 = some inst3120 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3120]
  rfl
private def inst3121 : Instruction := .inc 1 (some 3122)
private theorem resolved3121 : resolveAt exactSites 3121 = some inst3121 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3121]
  rfl
private def inst3122 : Instruction := .dec 2 (some 3130) (some 3123)
private theorem resolved3122 : resolveAt exactSites 3122 = some inst3122 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3122]
  rfl
private def inst3123 : Instruction := .inc 7 (some 3124)
private theorem resolved3123 : resolveAt exactSites 3123 = some inst3123 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3123]
  rfl
private def inst3124 : Instruction := .dec 6 (some 3126) (some 3125)
private theorem resolved3124 : resolveAt exactSites 3124 = some inst3124 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3124]
  rfl
private def inst3125 : Instruction := .jump (some 3129)
private theorem resolved3125 : resolveAt exactSites 3125 = some inst3125 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3125]
  rfl
private def inst3126 : Instruction := .dec 7 (some 3129) (some 3127)
private theorem resolved3126 : resolveAt exactSites 3126 = some inst3126 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3126]
  rfl
private def inst3127 : Instruction := .inc 6 (some 3128)
private theorem resolved3127 : resolveAt exactSites 3127 = some inst3127 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3127]
  rfl
private def inst3128 : Instruction := .jump (some 3126)
private theorem resolved3128 : resolveAt exactSites 3128 = some inst3128 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3128]
  rfl
private def inst3129 : Instruction := .jump (some 3122)
private theorem resolved3129 : resolveAt exactSites 3129 = some inst3129 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3129]
  rfl
private def inst3130 : Instruction := .dec 7 (some 3133) (some 3131)
private theorem resolved3130 : resolveAt exactSites 3130 = some inst3130 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3130]
  rfl
private def inst3131 : Instruction := .inc 2 (some 3132)
private theorem resolved3131 : resolveAt exactSites 3131 = some inst3131 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3131]
  rfl
private def inst3132 : Instruction := .jump (some 3130)
private theorem resolved3132 : resolveAt exactSites 3132 = some inst3132 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3132]
  rfl
private def inst3133 : Instruction := .dec 1 (some 3137) (some 3134)
private theorem resolved3133 : resolveAt exactSites 3133 = some inst3133 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3133]
  rfl
private def inst3134 : Instruction := .inc 7 (some 3135)
private theorem resolved3134 : resolveAt exactSites 3134 = some inst3134 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3134]
  rfl
private def inst3135 : Instruction := .inc 6 (some 3136)
private theorem resolved3135 : resolveAt exactSites 3135 = some inst3135 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3135]
  rfl
private def inst3136 : Instruction := .jump (some 3133)
private theorem resolved3136 : resolveAt exactSites 3136 = some inst3136 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3136]
  rfl
private def inst3137 : Instruction := .dec 6 (some 3143) (some 3138)
private theorem resolved3137 : resolveAt exactSites 3137 = some inst3137 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3137]
  rfl
private def inst3138 : Instruction := .inc 7 (some 3139)
private theorem resolved3138 : resolveAt exactSites 3138 = some inst3138 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3138]
  rfl
private def inst3139 : Instruction := .dec 6 (some 3142) (some 3140)
private theorem resolved3139 : resolveAt exactSites 3139 = some inst3139 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3139]
  rfl
private def inst3140 : Instruction := .inc 1 (some 3141)
private theorem resolved3140 : resolveAt exactSites 3140 = some inst3140 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3140]
  rfl
private def inst3141 : Instruction := .jump (some 3139)
private theorem resolved3141 : resolveAt exactSites 3141 = some inst3141 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3141]
  rfl
private def inst3142 : Instruction := .jump (some 3133)
private theorem resolved3142 : resolveAt exactSites 3142 = some inst3142 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3142]
  rfl
private def inst3143 : Instruction := .dec 7 (some 3149) (some 3144)
private theorem resolved3143 : resolveAt exactSites 3143 = some inst3143 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3143]
  rfl
private def inst3144 : Instruction := .inc 1 (some 3145)
private theorem resolved3144 : resolveAt exactSites 3144 = some inst3144 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3144]
  rfl
private def inst3145 : Instruction := .inc 1 (some 3146)
private theorem resolved3145 : resolveAt exactSites 3145 = some inst3145 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3145]
  rfl
private def inst3146 : Instruction := .inc 1 (some 3147)
private theorem resolved3146 : resolveAt exactSites 3146 = some inst3146 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3146]
  rfl
private def inst3147 : Instruction := .inc 1 (some 3148)
private theorem resolved3147 : resolveAt exactSites 3147 = some inst3147 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3147]
  rfl
private def inst3148 : Instruction := .jump (some 3143)
private theorem resolved3148 : resolveAt exactSites 3148 = some inst3148 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3148]
  rfl
private def inst3149 : Instruction := .dec 2 (some 3157) (some 3150)
private theorem resolved3149 : resolveAt exactSites 3149 = some inst3149 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3149]
  rfl
private def inst3150 : Instruction := .inc 7 (some 3151)
private theorem resolved3150 : resolveAt exactSites 3150 = some inst3150 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3150]
  rfl
private def inst3151 : Instruction := .dec 6 (some 3153) (some 3152)
private theorem resolved3151 : resolveAt exactSites 3151 = some inst3151 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3151]
  rfl
private def inst3152 : Instruction := .jump (some 3156)
private theorem resolved3152 : resolveAt exactSites 3152 = some inst3152 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3152]
  rfl
private def inst3153 : Instruction := .dec 7 (some 3156) (some 3154)
private theorem resolved3153 : resolveAt exactSites 3153 = some inst3153 := by
  rw [← PathTrie.fastResolveAt_eq]
  unfold PathTrie.fastResolveAt
  rw [lookup3153]
  rfl
private def raw0 := PA215.Census.C031.records[0]
private theorem row0 : destinationAgrees raw0 = true := by
  apply destination_nonterminal (s := site3055) (i := inst3055)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,false,true,true,false,true,true,false,true,true,true],0,(.inc 2)⟩) (q := (.at 3056)) (e := (.inc 2)) (k := 3056) (next := site3056)
  · rw [show raw0.siteIndex = 3055 from rfl]
    exact lookup3055
  · rw [show raw0.siteIndex = 3055 from rfl]
    exact resolved3055
  · decide
  · decide
  · rfl
  · exact lookup3056
  · decide
private def raw1 := PA215.Census.C031.records[1]
private theorem row1 : destinationAgrees raw1 = true := by
  apply destination_nonterminal (s := site3056) (i := inst3056)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,false,true,true,false,true,true,false,true],0,.none⟩) (q := (.at 3054)) (e := .none) (k := 3054) (next := site3054)
  · rw [show raw1.siteIndex = 3056 from rfl]
    exact lookup3056
  · rw [show raw1.siteIndex = 3056 from rfl]
    exact resolved3056
  · decide
  · decide
  · rfl
  · exact lookup3054
  · decide
private def raw2 := PA215.Census.C031.records[2]
private theorem row2 : destinationAgrees raw2 = true := by
  apply destination_nonterminal (s := site3057) (i := inst3057)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,false,true,true,false],0,.none⟩) (q := (.at 3048)) (e := .none) (k := 3048) (next := site3048)
  · rw [show raw2.siteIndex = 3057 from rfl]
    exact lookup3057
  · rw [show raw2.siteIndex = 3057 from rfl]
    exact resolved3057
  · decide
  · decide
  · rfl
  · exact lookup3048
  · decide
private def raw3 := PA215.Census.C031.records[3]
private theorem row3 : destinationAgrees raw3 = true := by
  apply destination_nonterminal (s := site3058) (i := inst3058)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,true,false,false,false],0,.none⟩) (q := (.at 3061)) (e := .none) (k := 3061) (next := site3061)
  · rw [show raw3.siteIndex = 3058 from rfl]
    exact lookup3058
  · rw [show raw3.siteIndex = 3058 from rfl]
    exact resolved3058
  · decide
  · decide
  · rfl
  · exact lookup3061
  · decide
private def raw4 := PA215.Census.C031.records[4]
private theorem row4 : destinationAgrees raw4 = true := by
  apply destination_nonterminal (s := site3058) (i := inst3058)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,false,true,true,true,true],1,(.dec 5)⟩) (q := (.at 3059)) (e := (.dec 5)) (k := 3059) (next := site3059)
  · rw [show raw4.siteIndex = 3058 from rfl]
    exact lookup3058
  · rw [show raw4.siteIndex = 3058 from rfl]
    exact resolved3058
  · decide
  · decide
  · rfl
  · exact lookup3059
  · decide
private def raw5 := PA215.Census.C031.records[5]
private theorem row5 : destinationAgrees raw5 = true := by
  apply destination_nonterminal (s := site3059) (i := inst3059)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,false,true,true,true,true,true],0,(.inc 0)⟩) (q := (.at 3060)) (e := (.inc 0)) (k := 3060) (next := site3060)
  · rw [show raw5.siteIndex = 3059 from rfl]
    exact lookup3059
  · rw [show raw5.siteIndex = 3059 from rfl]
    exact resolved3059
  · decide
  · decide
  · rfl
  · exact lookup3060
  · decide
private def raw6 := PA215.Census.C031.records[6]
private theorem row6 : destinationAgrees raw6 = true := by
  apply destination_nonterminal (s := site3060) (i := inst3060)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,false,true,true,true],0,.none⟩) (q := (.at 3058)) (e := .none) (k := 3058) (next := site3058)
  · rw [show raw6.siteIndex = 3060 from rfl]
    exact lookup3060
  · rw [show raw6.siteIndex = 3060 from rfl]
    exact resolved3060
  · decide
  · decide
  · rfl
  · exact lookup3058
  · decide
private def raw7 := PA215.Census.C031.records[7]
private theorem row7 : destinationAgrees raw7 = true := by
  apply destination_nonterminal (s := site3061) (i := inst3061)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,true,true],0,.none⟩) (q := (.at 3065)) (e := .none) (k := 3065) (next := site3065)
  · rw [show raw7.siteIndex = 3061 from rfl]
    exact lookup3061
  · rw [show raw7.siteIndex = 3061 from rfl]
    exact resolved3061
  · decide
  · decide
  · rfl
  · exact lookup3065
  · decide
private def raw8 := PA215.Census.C031.records[8]
private theorem row8 : destinationAgrees raw8 = true := by
  apply destination_nonterminal (s := site3061) (i := inst3061)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,true,false,true],1,(.dec 4)⟩) (q := (.at 3062)) (e := (.dec 4)) (k := 3062) (next := site3062)
  · rw [show raw8.siteIndex = 3061 from rfl]
    exact lookup3061
  · rw [show raw8.siteIndex = 3061 from rfl]
    exact resolved3061
  · decide
  · decide
  · rfl
  · exact lookup3062
  · decide
private def raw9 := PA215.Census.C031.records[9]
private theorem row9 : destinationAgrees raw9 = true := by
  apply destination_nonterminal (s := site3062) (i := inst3062)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,true,false,true,true],0,(.inc 2)⟩) (q := (.at 3063)) (e := (.inc 2)) (k := 3063) (next := site3063)
  · rw [show raw9.siteIndex = 3062 from rfl]
    exact lookup3062
  · rw [show raw9.siteIndex = 3062 from rfl]
    exact resolved3062
  · decide
  · decide
  · rfl
  · exact lookup3063
  · decide
private def raw10 := PA215.Census.C031.records[10]
private theorem row10 : destinationAgrees raw10 = true := by
  apply destination_nonterminal (s := site3063) (i := inst3063)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,true,false,true,true,true],0,(.inc 8)⟩) (q := (.at 3064)) (e := (.inc 8)) (k := 3064) (next := site3064)
  · rw [show raw10.siteIndex = 3063 from rfl]
    exact lookup3063
  · rw [show raw10.siteIndex = 3063 from rfl]
    exact resolved3063
  · decide
  · decide
  · rfl
  · exact lookup3064
  · decide
private def raw11 := PA215.Census.C031.records[11]
private theorem row11 : destinationAgrees raw11 = true := by
  apply destination_nonterminal (s := site3064) (i := inst3064)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,true,false],0,.none⟩) (q := (.at 3061)) (e := .none) (k := 3061) (next := site3061)
  · rw [show raw11.siteIndex = 3064 from rfl]
    exact lookup3064
  · rw [show raw11.siteIndex = 3064 from rfl]
    exact resolved3064
  · decide
  · decide
  · rfl
  · exact lookup3061
  · decide
private def raw12 := PA215.Census.C031.records[12]
private theorem row12 : destinationAgrees raw12 = true := by
  apply destination_nonterminal (s := site3065) (i := inst3065)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,false],0,.none⟩) (q := (.at 3068)) (e := .none) (k := 3068) (next := site3068)
  · rw [show raw12.siteIndex = 3065 from rfl]
    exact lookup3065
  · rw [show raw12.siteIndex = 3065 from rfl]
    exact resolved3065
  · decide
  · decide
  · rfl
  · exact lookup3068
  · decide
private def raw13 := PA215.Census.C031.records[13]
private theorem row13 : destinationAgrees raw13 = true := by
  apply destination_nonterminal (s := site3065) (i := inst3065)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,true,true,true],1,(.dec 8)⟩) (q := (.at 3066)) (e := (.dec 8)) (k := 3066) (next := site3066)
  · rw [show raw13.siteIndex = 3065 from rfl]
    exact lookup3065
  · rw [show raw13.siteIndex = 3065 from rfl]
    exact resolved3065
  · decide
  · decide
  · rfl
  · exact lookup3066
  · decide
private def raw14 := PA215.Census.C031.records[14]
private theorem row14 : destinationAgrees raw14 = true := by
  apply destination_nonterminal (s := site3066) (i := inst3066)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,true,true,true,true],0,(.inc 4)⟩) (q := (.at 3067)) (e := (.inc 4)) (k := 3067) (next := site3067)
  · rw [show raw14.siteIndex = 3066 from rfl]
    exact lookup3066
  · rw [show raw14.siteIndex = 3066 from rfl]
    exact resolved3066
  · decide
  · decide
  · rfl
  · exact lookup3067
  · decide
private def raw15 := PA215.Census.C031.records[15]
private theorem row15 : destinationAgrees raw15 = true := by
  apply destination_nonterminal (s := site3067) (i := inst3067)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,false,true,true],0,.none⟩) (q := (.at 3065)) (e := .none) (k := 3065) (next := site3065)
  · rw [show raw15.siteIndex = 3067 from rfl]
    exact lookup3067
  · rw [show raw15.siteIndex = 3067 from rfl]
    exact resolved3067
  · decide
  · decide
  · rfl
  · exact lookup3065
  · decide
private def raw16 := PA215.Census.C031.records[16]
private theorem row16 : destinationAgrees raw16 = true := by
  apply destination_nonterminal (s := site3068) (i := inst3068)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true],0,.none⟩) (q := (.at 3071)) (e := .none) (k := 3071) (next := site3071)
  · rw [show raw16.siteIndex = 3068 from rfl]
    exact lookup3068
  · rw [show raw16.siteIndex = 3068 from rfl]
    exact resolved3068
  · decide
  · decide
  · rfl
  · exact lookup3071
  · decide
private def raw17 := PA215.Census.C031.records[17]
private theorem row17 : destinationAgrees raw17 = true := by
  apply destination_nonterminal (s := site3068) (i := inst3068)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,false,true],1,(.dec 2)⟩) (q := (.at 3069)) (e := (.dec 2)) (k := 3069) (next := site3069)
  · rw [show raw17.siteIndex = 3068 from rfl]
    exact lookup3068
  · rw [show raw17.siteIndex = 3068 from rfl]
    exact resolved3068
  · decide
  · decide
  · rfl
  · exact lookup3069
  · decide
private def raw18 := PA215.Census.C031.records[18]
private theorem row18 : destinationAgrees raw18 = true := by
  apply destination_nonterminal (s := site3069) (i := inst3069)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,false,true,true],0,(.inc 8)⟩) (q := (.at 3070)) (e := (.inc 8)) (k := 3070) (next := site3070)
  · rw [show raw18.siteIndex = 3069 from rfl]
    exact lookup3069
  · rw [show raw18.siteIndex = 3069 from rfl]
    exact resolved3069
  · decide
  · decide
  · rfl
  · exact lookup3070
  · decide
private def raw19 := PA215.Census.C031.records[19]
private theorem row19 : destinationAgrees raw19 = true := by
  apply destination_nonterminal (s := site3070) (i := inst3070)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,false],0,.none⟩) (q := (.at 3068)) (e := .none) (k := 3068) (next := site3068)
  · rw [show raw19.siteIndex = 3070 from rfl]
    exact lookup3070
  · rw [show raw19.siteIndex = 3070 from rfl]
    exact resolved3070
  · decide
  · decide
  · rfl
  · exact lookup3068
  · decide
private def raw20 := PA215.Census.C031.records[20]
private theorem row20 : destinationAgrees raw20 = true := by
  apply destination_nonterminal (s := site3071) (i := inst3071)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true],0,.none⟩) (q := (.at 3074)) (e := .none) (k := 3074) (next := site3074)
  · rw [show raw20.siteIndex = 3071 from rfl]
    exact lookup3071
  · rw [show raw20.siteIndex = 3071 from rfl]
    exact resolved3071
  · decide
  · decide
  · rfl
  · exact lookup3074
  · decide
private def raw21 := PA215.Census.C031.records[21]
private theorem row21 : destinationAgrees raw21 = true := by
  apply destination_nonterminal (s := site3071) (i := inst3071)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,false,true],1,(.dec 0)⟩) (q := (.at 3072)) (e := (.dec 0)) (k := 3072) (next := site3072)
  · rw [show raw21.siteIndex = 3071 from rfl]
    exact lookup3071
  · rw [show raw21.siteIndex = 3071 from rfl]
    exact resolved3071
  · decide
  · decide
  · rfl
  · exact lookup3072
  · decide
private def raw22 := PA215.Census.C031.records[22]
private theorem row22 : destinationAgrees raw22 = true := by
  apply destination_nonterminal (s := site3072) (i := inst3072)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,false,true,true],0,(.inc 2)⟩) (q := (.at 3073)) (e := (.inc 2)) (k := 3073) (next := site3073)
  · rw [show raw22.siteIndex = 3072 from rfl]
    exact lookup3072
  · rw [show raw22.siteIndex = 3072 from rfl]
    exact resolved3072
  · decide
  · decide
  · rfl
  · exact lookup3073
  · decide
private def raw23 := PA215.Census.C031.records[23]
private theorem row23 : destinationAgrees raw23 = true := by
  apply destination_nonterminal (s := site3073) (i := inst3073)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,false],0,.none⟩) (q := (.at 3071)) (e := .none) (k := 3071) (next := site3071)
  · rw [show raw23.siteIndex = 3073 from rfl]
    exact lookup3073
  · rw [show raw23.siteIndex = 3073 from rfl]
    exact resolved3073
  · decide
  · decide
  · rfl
  · exact lookup3071
  · decide
private def raw24 := PA215.Census.C031.records[24]
private theorem row24 : destinationAgrees raw24 = true := by
  apply destination_nonterminal (s := site3074) (i := inst3074)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,false,true],0,.none⟩) (q := (.at 3078)) (e := .none) (k := 3078) (next := site3078)
  · rw [show raw24.siteIndex = 3074 from rfl]
    exact lookup3074
  · rw [show raw24.siteIndex = 3074 from rfl]
    exact resolved3074
  · decide
  · decide
  · rfl
  · exact lookup3078
  · decide
private def raw25 := PA215.Census.C031.records[25]
private theorem row25 : destinationAgrees raw25 = true := by
  apply destination_nonterminal (s := site3074) (i := inst3074)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,false,false,true],1,(.dec 2)⟩) (q := (.at 3075)) (e := (.dec 2)) (k := 3075) (next := site3075)
  · rw [show raw25.siteIndex = 3074 from rfl]
    exact lookup3074
  · rw [show raw25.siteIndex = 3074 from rfl]
    exact resolved3074
  · decide
  · decide
  · rfl
  · exact lookup3075
  · decide
private def raw26 := PA215.Census.C031.records[26]
private theorem row26 : destinationAgrees raw26 = true := by
  apply destination_nonterminal (s := site3075) (i := inst3075)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,false,false,true,true],0,(.inc 5)⟩) (q := (.at 3076)) (e := (.inc 5)) (k := 3076) (next := site3076)
  · rw [show raw26.siteIndex = 3075 from rfl]
    exact lookup3075
  · rw [show raw26.siteIndex = 3075 from rfl]
    exact resolved3075
  · decide
  · decide
  · rfl
  · exact lookup3076
  · decide
private def raw27 := PA215.Census.C031.records[27]
private theorem row27 : destinationAgrees raw27 = true := by
  apply destination_nonterminal (s := site3076) (i := inst3076)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,false,false,true,true,true],0,(.inc 8)⟩) (q := (.at 3077)) (e := (.inc 8)) (k := 3077) (next := site3077)
  · rw [show raw27.siteIndex = 3076 from rfl]
    exact lookup3076
  · rw [show raw27.siteIndex = 3076 from rfl]
    exact resolved3076
  · decide
  · decide
  · rfl
  · exact lookup3077
  · decide
private def raw28 := PA215.Census.C031.records[28]
private theorem row28 : destinationAgrees raw28 = true := by
  apply destination_nonterminal (s := site3077) (i := inst3077)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,false,false],0,.none⟩) (q := (.at 3074)) (e := .none) (k := 3074) (next := site3074)
  · rw [show raw28.siteIndex = 3077 from rfl]
    exact lookup3077
  · rw [show raw28.siteIndex = 3077 from rfl]
    exact resolved3077
  · decide
  · decide
  · rfl
  · exact lookup3074
  · decide
private def raw29 := PA215.Census.C031.records[29]
private theorem row29 : destinationAgrees raw29 = true := by
  apply destination_nonterminal (s := site3078) (i := inst3078)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,true,false],0,.none⟩) (q := (.at 3084)) (e := .none) (k := 3084) (next := site3084)
  · rw [show raw29.siteIndex = 3078 from rfl]
    exact lookup3078
  · rw [show raw29.siteIndex = 3078 from rfl]
    exact resolved3078
  · decide
  · decide
  · rfl
  · exact lookup3084
  · decide
private def raw30 := PA215.Census.C031.records[30]
private theorem row30 : destinationAgrees raw30 = true := by
  apply destination_nonterminal (s := site3078) (i := inst3078)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,false,true,true],1,(.dec 8)⟩) (q := (.at 3079)) (e := (.dec 8)) (k := 3079) (next := site3079)
  · rw [show raw30.siteIndex = 3078 from rfl]
    exact lookup3078
  · rw [show raw30.siteIndex = 3078 from rfl]
    exact resolved3078
  · decide
  · decide
  · rfl
  · exact lookup3079
  · decide
private def raw31 := PA215.Census.C031.records[31]
private theorem row31 : destinationAgrees raw31 = true := by
  apply destination_nonterminal (s := site3079) (i := inst3079)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,false,true,true,false,true],0,(.inc 5)⟩) (q := (.at 3080)) (e := (.inc 5)) (k := 3080) (next := site3080)
  · rw [show raw31.siteIndex = 3079 from rfl]
    exact lookup3079
  · rw [show raw31.siteIndex = 3079 from rfl]
    exact resolved3079
  · decide
  · decide
  · rfl
  · exact lookup3080
  · decide
private def raw32 := PA215.Census.C031.records[32]
private theorem row32 : destinationAgrees raw32 = true := by
  apply destination_nonterminal (s := site3080) (i := inst3080)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,false,true,true,true,false],0,.none⟩) (q := (.at 3083)) (e := .none) (k := 3083) (next := site3083)
  · rw [show raw32.siteIndex = 3080 from rfl]
    exact lookup3080
  · rw [show raw32.siteIndex = 3080 from rfl]
    exact resolved3080
  · decide
  · decide
  · rfl
  · exact lookup3083
  · decide
private def raw33 := PA215.Census.C031.records[33]
private theorem row33 : destinationAgrees raw33 = true := by
  apply destination_nonterminal (s := site3080) (i := inst3080)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,false,true,true,false,true,true],1,(.dec 8)⟩) (q := (.at 3081)) (e := (.dec 8)) (k := 3081) (next := site3081)
  · rw [show raw33.siteIndex = 3080 from rfl]
    exact lookup3080
  · rw [show raw33.siteIndex = 3080 from rfl]
    exact resolved3080
  · decide
  · decide
  · rfl
  · exact lookup3081
  · decide
private def raw34 := PA215.Census.C031.records[34]
private theorem row34 : destinationAgrees raw34 = true := by
  apply destination_nonterminal (s := site3081) (i := inst3081)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,false,true,true,false,true,true,true],0,(.inc 2)⟩) (q := (.at 3082)) (e := (.inc 2)) (k := 3082) (next := site3082)
  · rw [show raw34.siteIndex = 3081 from rfl]
    exact lookup3081
  · rw [show raw34.siteIndex = 3081 from rfl]
    exact resolved3081
  · decide
  · decide
  · rfl
  · exact lookup3082
  · decide
private def raw35 := PA215.Census.C031.records[35]
private theorem row35 : destinationAgrees raw35 = true := by
  apply destination_nonterminal (s := site3082) (i := inst3082)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,false,true,true,false,true],0,.none⟩) (q := (.at 3080)) (e := .none) (k := 3080) (next := site3080)
  · rw [show raw35.siteIndex = 3082 from rfl]
    exact lookup3082
  · rw [show raw35.siteIndex = 3082 from rfl]
    exact resolved3082
  · decide
  · decide
  · rfl
  · exact lookup3080
  · decide
private def raw36 := PA215.Census.C031.records[36]
private theorem row36 : destinationAgrees raw36 = true := by
  apply destination_nonterminal (s := site3083) (i := inst3083)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,false],0,.none⟩) (q := (.at 3074)) (e := .none) (k := 3074) (next := site3074)
  · rw [show raw36.siteIndex = 3083 from rfl]
    exact lookup3083
  · rw [show raw36.siteIndex = 3083 from rfl]
    exact resolved3083
  · decide
  · decide
  · rfl
  · exact lookup3074
  · decide
private def raw37 := PA215.Census.C031.records[37]
private theorem row37 : destinationAgrees raw37 = true := by
  apply destination_nonterminal (s := site3084) (i := inst3084)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,true,false,false,false],0,.none⟩) (q := (.at 3087)) (e := .none) (k := 3087) (next := site3087)
  · rw [show raw37.siteIndex = 3084 from rfl]
    exact lookup3084
  · rw [show raw37.siteIndex = 3084 from rfl]
    exact resolved3084
  · decide
  · decide
  · rfl
  · exact lookup3087
  · decide
private def raw38 := PA215.Census.C031.records[38]
private theorem row38 : destinationAgrees raw38 = true := by
  apply destination_nonterminal (s := site3084) (i := inst3084)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,true,true],1,(.dec 5)⟩) (q := (.at 3085)) (e := (.dec 5)) (k := 3085) (next := site3085)
  · rw [show raw38.siteIndex = 3084 from rfl]
    exact lookup3084
  · rw [show raw38.siteIndex = 3084 from rfl]
    exact resolved3084
  · decide
  · decide
  · rfl
  · exact lookup3085
  · decide
private def raw39 := PA215.Census.C031.records[39]
private theorem row39 : destinationAgrees raw39 = true := by
  apply destination_nonterminal (s := site3085) (i := inst3085)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,true,true,true],0,(.inc 0)⟩) (q := (.at 3086)) (e := (.inc 0)) (k := 3086) (next := site3086)
  · rw [show raw39.siteIndex = 3085 from rfl]
    exact lookup3085
  · rw [show raw39.siteIndex = 3085 from rfl]
    exact resolved3085
  · decide
  · decide
  · rfl
  · exact lookup3086
  · decide
private def raw40 := PA215.Census.C031.records[40]
private theorem row40 : destinationAgrees raw40 = true := by
  apply destination_nonterminal (s := site3086) (i := inst3086)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,false,true,true,true],0,.none⟩) (q := (.at 3084)) (e := .none) (k := 3084) (next := site3084)
  · rw [show raw40.siteIndex = 3086 from rfl]
    exact lookup3086
  · rw [show raw40.siteIndex = 3086 from rfl]
    exact resolved3086
  · decide
  · decide
  · rfl
  · exact lookup3084
  · decide
private def raw41 := PA215.Census.C031.records[41]
private theorem row41 : destinationAgrees raw41 = true := by
  apply destination_nonterminal (s := site3087) (i := inst3087)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,true,true],0,.none⟩) (q := (.at 3091)) (e := .none) (k := 3091) (next := site3091)
  · rw [show raw41.siteIndex = 3087 from rfl]
    exact lookup3087
  · rw [show raw41.siteIndex = 3087 from rfl]
    exact resolved3087
  · decide
  · decide
  · rfl
  · exact lookup3091
  · decide
private def raw42 := PA215.Census.C031.records[42]
private theorem row42 : destinationAgrees raw42 = true := by
  apply destination_nonterminal (s := site3087) (i := inst3087)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,true,false,true],1,(.dec 7)⟩) (q := (.at 3088)) (e := (.dec 7)) (k := 3088) (next := site3088)
  · rw [show raw42.siteIndex = 3087 from rfl]
    exact lookup3087
  · rw [show raw42.siteIndex = 3087 from rfl]
    exact resolved3087
  · decide
  · decide
  · rfl
  · exact lookup3088
  · decide
private def raw43 := PA215.Census.C031.records[43]
private theorem row43 : destinationAgrees raw43 = true := by
  apply destination_nonterminal (s := site3088) (i := inst3088)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,true,false,true,true],0,(.inc 2)⟩) (q := (.at 3089)) (e := (.inc 2)) (k := 3089) (next := site3089)
  · rw [show raw43.siteIndex = 3088 from rfl]
    exact lookup3088
  · rw [show raw43.siteIndex = 3088 from rfl]
    exact resolved3088
  · decide
  · decide
  · rfl
  · exact lookup3089
  · decide
private def raw44 := PA215.Census.C031.records[44]
private theorem row44 : destinationAgrees raw44 = true := by
  apply destination_nonterminal (s := site3089) (i := inst3089)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,true,false,true,true,true],0,(.inc 8)⟩) (q := (.at 3090)) (e := (.inc 8)) (k := 3090) (next := site3090)
  · rw [show raw44.siteIndex = 3089 from rfl]
    exact lookup3089
  · rw [show raw44.siteIndex = 3089 from rfl]
    exact resolved3089
  · decide
  · decide
  · rfl
  · exact lookup3090
  · decide
private def raw45 := PA215.Census.C031.records[45]
private theorem row45 : destinationAgrees raw45 = true := by
  apply destination_nonterminal (s := site3090) (i := inst3090)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,true,false],0,.none⟩) (q := (.at 3087)) (e := .none) (k := 3087) (next := site3087)
  · rw [show raw45.siteIndex = 3090 from rfl]
    exact lookup3090
  · rw [show raw45.siteIndex = 3090 from rfl]
    exact resolved3090
  · decide
  · decide
  · rfl
  · exact lookup3087
  · decide
private def raw46 := PA215.Census.C031.records[46]
private theorem row46 : destinationAgrees raw46 = true := by
  apply destination_nonterminal (s := site3091) (i := inst3091)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,false,false],0,.none⟩) (q := (.at 3094)) (e := .none) (k := 3094) (next := site3094)
  · rw [show raw46.siteIndex = 3091 from rfl]
    exact lookup3091
  · rw [show raw46.siteIndex = 3091 from rfl]
    exact resolved3091
  · decide
  · decide
  · rfl
  · exact lookup3094
  · decide
private def raw47 := PA215.Census.C031.records[47]
private theorem row47 : destinationAgrees raw47 = true := by
  apply destination_nonterminal (s := site3091) (i := inst3091)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,true,true,true],1,(.dec 8)⟩) (q := (.at 3092)) (e := (.dec 8)) (k := 3092) (next := site3092)
  · rw [show raw47.siteIndex = 3091 from rfl]
    exact lookup3091
  · rw [show raw47.siteIndex = 3091 from rfl]
    exact resolved3091
  · decide
  · decide
  · rfl
  · exact lookup3092
  · decide
private def raw48 := PA215.Census.C031.records[48]
private theorem row48 : destinationAgrees raw48 = true := by
  apply destination_nonterminal (s := site3092) (i := inst3092)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,true,true,true,true],0,(.inc 7)⟩) (q := (.at 3093)) (e := (.inc 7)) (k := 3093) (next := site3093)
  · rw [show raw48.siteIndex = 3092 from rfl]
    exact lookup3092
  · rw [show raw48.siteIndex = 3092 from rfl]
    exact resolved3092
  · decide
  · decide
  · rfl
  · exact lookup3093
  · decide
private def raw49 := PA215.Census.C031.records[49]
private theorem row49 : destinationAgrees raw49 = true := by
  apply destination_nonterminal (s := site3093) (i := inst3093)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,false,true,true,true],0,.none⟩) (q := (.at 3091)) (e := .none) (k := 3091) (next := site3091)
  · rw [show raw49.siteIndex = 3093 from rfl]
    exact lookup3093
  · rw [show raw49.siteIndex = 3093 from rfl]
    exact resolved3093
  · decide
  · decide
  · rfl
  · exact lookup3091
  · decide
private def raw50 := PA215.Census.C031.records[50]
private theorem row50 : destinationAgrees raw50 = true := by
  apply destination_nonterminal (s := site3094) (i := inst3094)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,false,true],0,.none⟩) (q := (.at 3102)) (e := .none) (k := 3102) (next := site3102)
  · rw [show raw50.siteIndex = 3094 from rfl]
    exact lookup3094
  · rw [show raw50.siteIndex = 3094 from rfl]
    exact resolved3094
  · decide
  · decide
  · rfl
  · exact lookup3102
  · decide
private def raw51 := PA215.Census.C031.records[51]
private theorem row51 : destinationAgrees raw51 = true := by
  apply destination_nonterminal (s := site3094) (i := inst3094)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,false,false,true],1,(.dec 0)⟩) (q := (.at 3095)) (e := (.dec 0)) (k := 3095) (next := site3095)
  · rw [show raw51.siteIndex = 3094 from rfl]
    exact lookup3094
  · rw [show raw51.siteIndex = 3094 from rfl]
    exact resolved3094
  · decide
  · decide
  · rfl
  · exact lookup3095
  · decide
private def raw52 := PA215.Census.C031.records[52]
private theorem row52 : destinationAgrees raw52 = true := by
  apply destination_nonterminal (s := site3095) (i := inst3095)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,false,false,true,true],0,(.inc 5)⟩) (q := (.at 3096)) (e := (.inc 5)) (k := 3096) (next := site3096)
  · rw [show raw52.siteIndex = 3095 from rfl]
    exact lookup3095
  · rw [show raw52.siteIndex = 3095 from rfl]
    exact resolved3095
  · decide
  · decide
  · rfl
  · exact lookup3096
  · decide
private def raw53 := PA215.Census.C031.records[53]
private theorem row53 : destinationAgrees raw53 = true := by
  apply destination_nonterminal (s := site3096) (i := inst3096)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,false,false,true,true,false,true],0,.none⟩) (q := (.at 3098)) (e := .none) (k := 3098) (next := site3098)
  · rw [show raw53.siteIndex = 3096 from rfl]
    exact lookup3096
  · rw [show raw53.siteIndex = 3096 from rfl]
    exact resolved3096
  · decide
  · decide
  · rfl
  · exact lookup3098
  · decide
private def raw54 := PA215.Census.C031.records[54]
private theorem row54 : destinationAgrees raw54 = true := by
  apply destination_nonterminal (s := site3096) (i := inst3096)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,false,false,true,true,false,false,true],1,(.dec 8)⟩) (q := (.at 3097)) (e := (.dec 8)) (k := 3097) (next := site3097)
  · rw [show raw54.siteIndex = 3096 from rfl]
    exact lookup3096
  · rw [show raw54.siteIndex = 3096 from rfl]
    exact resolved3096
  · decide
  · decide
  · rfl
  · exact lookup3097
  · decide
private def raw55 := PA215.Census.C031.records[55]
private theorem row55 : destinationAgrees raw55 = true := by
  apply destination_nonterminal (s := site3097) (i := inst3097)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,false,false,true,true,true],0,.none⟩) (q := (.at 3101)) (e := .none) (k := 3101) (next := site3101)
  · rw [show raw55.siteIndex = 3097 from rfl]
    exact lookup3097
  · rw [show raw55.siteIndex = 3097 from rfl]
    exact resolved3097
  · decide
  · decide
  · rfl
  · exact lookup3101
  · decide
private def raw56 := PA215.Census.C031.records[56]
private theorem row56 : destinationAgrees raw56 = true := by
  apply destination_nonterminal (s := site3098) (i := inst3098)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,false,false,true,true,true,false],0,.none⟩) (q := (.at 3101)) (e := .none) (k := 3101) (next := site3101)
  · rw [show raw56.siteIndex = 3098 from rfl]
    exact lookup3098
  · rw [show raw56.siteIndex = 3098 from rfl]
    exact resolved3098
  · decide
  · decide
  · rfl
  · exact lookup3101
  · decide
private def raw57 := PA215.Census.C031.records[57]
private theorem row57 : destinationAgrees raw57 = true := by
  apply destination_nonterminal (s := site3098) (i := inst3098)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,false,false,true,true,false,true,true],1,(.dec 5)⟩) (q := (.at 3099)) (e := (.dec 5)) (k := 3099) (next := site3099)
  · rw [show raw57.siteIndex = 3098 from rfl]
    exact lookup3098
  · rw [show raw57.siteIndex = 3098 from rfl]
    exact resolved3098
  · decide
  · decide
  · rfl
  · exact lookup3099
  · decide
private def raw58 := PA215.Census.C031.records[58]
private theorem row58 : destinationAgrees raw58 = true := by
  apply destination_nonterminal (s := site3099) (i := inst3099)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,false,false,true,true,false,true,true,true],0,(.inc 8)⟩) (q := (.at 3100)) (e := (.inc 8)) (k := 3100) (next := site3100)
  · rw [show raw58.siteIndex = 3099 from rfl]
    exact lookup3099
  · rw [show raw58.siteIndex = 3099 from rfl]
    exact resolved3099
  · decide
  · decide
  · rfl
  · exact lookup3100
  · decide
private def raw59 := PA215.Census.C031.records[59]
private theorem row59 : destinationAgrees raw59 = true := by
  apply destination_nonterminal (s := site3100) (i := inst3100)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,false,false,true,true,false,true],0,.none⟩) (q := (.at 3098)) (e := .none) (k := 3098) (next := site3098)
  · rw [show raw59.siteIndex = 3100 from rfl]
    exact lookup3100
  · rw [show raw59.siteIndex = 3100 from rfl]
    exact resolved3100
  · decide
  · decide
  · rfl
  · exact lookup3098
  · decide
private def raw60 := PA215.Census.C031.records[60]
private theorem row60 : destinationAgrees raw60 = true := by
  apply destination_nonterminal (s := site3101) (i := inst3101)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,false,false],0,.none⟩) (q := (.at 3094)) (e := .none) (k := 3094) (next := site3094)
  · rw [show raw60.siteIndex = 3101 from rfl]
    exact lookup3101
  · rw [show raw60.siteIndex = 3101 from rfl]
    exact resolved3101
  · decide
  · decide
  · rfl
  · exact lookup3094
  · decide
private def raw61 := PA215.Census.C031.records[61]
private theorem row61 : destinationAgrees raw61 = true := by
  apply destination_nonterminal (s := site3102) (i := inst3102)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,false],0,.none⟩) (q := (.at 3105)) (e := .none) (k := 3105) (next := site3105)
  · rw [show raw61.siteIndex = 3102 from rfl]
    exact lookup3102
  · rw [show raw61.siteIndex = 3102 from rfl]
    exact resolved3102
  · decide
  · decide
  · rfl
  · exact lookup3105
  · decide
private def raw62 := PA215.Census.C031.records[62]
private theorem row62 : destinationAgrees raw62 = true := by
  apply destination_nonterminal (s := site3102) (i := inst3102)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,false,true,true],1,(.dec 5)⟩) (q := (.at 3103)) (e := (.dec 5)) (k := 3103) (next := site3103)
  · rw [show raw62.siteIndex = 3102 from rfl]
    exact lookup3102
  · rw [show raw62.siteIndex = 3102 from rfl]
    exact resolved3102
  · decide
  · decide
  · rfl
  · exact lookup3103
  · decide
private def raw63 := PA215.Census.C031.records[63]
private theorem row63 : destinationAgrees raw63 = true := by
  apply destination_nonterminal (s := site3103) (i := inst3103)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,false,true,true,true],0,(.inc 0)⟩) (q := (.at 3104)) (e := (.inc 0)) (k := 3104) (next := site3104)
  · rw [show raw63.siteIndex = 3103 from rfl]
    exact lookup3103
  · rw [show raw63.siteIndex = 3103 from rfl]
    exact resolved3103
  · decide
  · decide
  · rfl
  · exact lookup3104
  · decide
private def raw64 := PA215.Census.C031.records[64]
private theorem row64 : destinationAgrees raw64 = true := by
  apply destination_nonterminal (s := site3104) (i := inst3104)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,false,true],0,.none⟩) (q := (.at 3102)) (e := .none) (k := 3102) (next := site3102)
  · rw [show raw64.siteIndex = 3104 from rfl]
    exact lookup3104
  · rw [show raw64.siteIndex = 3104 from rfl]
    exact resolved3104
  · decide
  · decide
  · rfl
  · exact lookup3102
  · decide
private def raw65 := PA215.Census.C031.records[65]
private theorem row65 : destinationAgrees raw65 = true := by
  apply destination_nonterminal (s := site3105) (i := inst3105)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,false,true],0,.none⟩) (q := (.at 3109)) (e := .none) (k := 3109) (next := site3109)
  · rw [show raw65.siteIndex = 3105 from rfl]
    exact lookup3105
  · rw [show raw65.siteIndex = 3105 from rfl]
    exact resolved3105
  · decide
  · decide
  · rfl
  · exact lookup3109
  · decide
private def raw66 := PA215.Census.C031.records[66]
private theorem row66 : destinationAgrees raw66 = true := by
  apply destination_nonterminal (s := site3105) (i := inst3105)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,false,false,true],1,(.dec 2)⟩) (q := (.at 3106)) (e := (.dec 2)) (k := 3106) (next := site3106)
  · rw [show raw66.siteIndex = 3105 from rfl]
    exact lookup3105
  · rw [show raw66.siteIndex = 3105 from rfl]
    exact resolved3105
  · decide
  · decide
  · rfl
  · exact lookup3106
  · decide
private def raw67 := PA215.Census.C031.records[67]
private theorem row67 : destinationAgrees raw67 = true := by
  apply destination_nonterminal (s := site3106) (i := inst3106)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,false,false,true,true],0,(.inc 5)⟩) (q := (.at 3107)) (e := (.inc 5)) (k := 3107) (next := site3107)
  · rw [show raw67.siteIndex = 3106 from rfl]
    exact lookup3106
  · rw [show raw67.siteIndex = 3106 from rfl]
    exact resolved3106
  · decide
  · decide
  · rfl
  · exact lookup3107
  · decide
private def raw68 := PA215.Census.C031.records[68]
private theorem row68 : destinationAgrees raw68 = true := by
  apply destination_nonterminal (s := site3107) (i := inst3107)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,false,false,true,true,true],0,(.inc 8)⟩) (q := (.at 3108)) (e := (.inc 8)) (k := 3108) (next := site3108)
  · rw [show raw68.siteIndex = 3107 from rfl]
    exact lookup3107
  · rw [show raw68.siteIndex = 3107 from rfl]
    exact resolved3107
  · decide
  · decide
  · rfl
  · exact lookup3108
  · decide
private def raw69 := PA215.Census.C031.records[69]
private theorem row69 : destinationAgrees raw69 = true := by
  apply destination_nonterminal (s := site3108) (i := inst3108)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,false,false],0,.none⟩) (q := (.at 3105)) (e := .none) (k := 3105) (next := site3105)
  · rw [show raw69.siteIndex = 3108 from rfl]
    exact lookup3108
  · rw [show raw69.siteIndex = 3108 from rfl]
    exact resolved3108
  · decide
  · decide
  · rfl
  · exact lookup3105
  · decide
private def raw70 := PA215.Census.C031.records[70]
private theorem row70 : destinationAgrees raw70 = true := by
  apply destination_nonterminal (s := site3109) (i := inst3109)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,true,false],0,.none⟩) (q := (.at 3115)) (e := .none) (k := 3115) (next := site3115)
  · rw [show raw70.siteIndex = 3109 from rfl]
    exact lookup3109
  · rw [show raw70.siteIndex = 3109 from rfl]
    exact resolved3109
  · decide
  · decide
  · rfl
  · exact lookup3115
  · decide
private def raw71 := PA215.Census.C031.records[71]
private theorem row71 : destinationAgrees raw71 = true := by
  apply destination_nonterminal (s := site3109) (i := inst3109)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,false,true,true],1,(.dec 8)⟩) (q := (.at 3110)) (e := (.dec 8)) (k := 3110) (next := site3110)
  · rw [show raw71.siteIndex = 3109 from rfl]
    exact lookup3109
  · rw [show raw71.siteIndex = 3109 from rfl]
    exact resolved3109
  · decide
  · decide
  · rfl
  · exact lookup3110
  · decide
private def raw72 := PA215.Census.C031.records[72]
private theorem row72 : destinationAgrees raw72 = true := by
  apply destination_nonterminal (s := site3110) (i := inst3110)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,false,true,true,false,true],0,(.inc 5)⟩) (q := (.at 3111)) (e := (.inc 5)) (k := 3111) (next := site3111)
  · rw [show raw72.siteIndex = 3110 from rfl]
    exact lookup3110
  · rw [show raw72.siteIndex = 3110 from rfl]
    exact resolved3110
  · decide
  · decide
  · rfl
  · exact lookup3111
  · decide
private def raw73 := PA215.Census.C031.records[73]
private theorem row73 : destinationAgrees raw73 = true := by
  apply destination_nonterminal (s := site3111) (i := inst3111)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,false,true,true,true,false],0,.none⟩) (q := (.at 3114)) (e := .none) (k := 3114) (next := site3114)
  · rw [show raw73.siteIndex = 3111 from rfl]
    exact lookup3111
  · rw [show raw73.siteIndex = 3111 from rfl]
    exact resolved3111
  · decide
  · decide
  · rfl
  · exact lookup3114
  · decide
private def raw74 := PA215.Census.C031.records[74]
private theorem row74 : destinationAgrees raw74 = true := by
  apply destination_nonterminal (s := site3111) (i := inst3111)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,false,true,true,false,true,true],1,(.dec 8)⟩) (q := (.at 3112)) (e := (.dec 8)) (k := 3112) (next := site3112)
  · rw [show raw74.siteIndex = 3111 from rfl]
    exact lookup3111
  · rw [show raw74.siteIndex = 3111 from rfl]
    exact resolved3111
  · decide
  · decide
  · rfl
  · exact lookup3112
  · decide
private def raw75 := PA215.Census.C031.records[75]
private theorem row75 : destinationAgrees raw75 = true := by
  apply destination_nonterminal (s := site3112) (i := inst3112)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,false,true,true,false,true,true,true],0,(.inc 2)⟩) (q := (.at 3113)) (e := (.inc 2)) (k := 3113) (next := site3113)
  · rw [show raw75.siteIndex = 3112 from rfl]
    exact lookup3112
  · rw [show raw75.siteIndex = 3112 from rfl]
    exact resolved3112
  · decide
  · decide
  · rfl
  · exact lookup3113
  · decide
private def raw76 := PA215.Census.C031.records[76]
private theorem row76 : destinationAgrees raw76 = true := by
  apply destination_nonterminal (s := site3113) (i := inst3113)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,false,true,true,false,true],0,.none⟩) (q := (.at 3111)) (e := .none) (k := 3111) (next := site3111)
  · rw [show raw76.siteIndex = 3113 from rfl]
    exact lookup3113
  · rw [show raw76.siteIndex = 3113 from rfl]
    exact resolved3113
  · decide
  · decide
  · rfl
  · exact lookup3111
  · decide
private def raw77 := PA215.Census.C031.records[77]
private theorem row77 : destinationAgrees raw77 = true := by
  apply destination_nonterminal (s := site3114) (i := inst3114)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,false],0,.none⟩) (q := (.at 3105)) (e := .none) (k := 3105) (next := site3105)
  · rw [show raw77.siteIndex = 3114 from rfl]
    exact lookup3114
  · rw [show raw77.siteIndex = 3114 from rfl]
    exact resolved3114
  · decide
  · decide
  · rfl
  · exact lookup3105
  · decide
private def raw78 := PA215.Census.C031.records[78]
private theorem row78 : destinationAgrees raw78 = true := by
  apply destination_nonterminal (s := site3115) (i := inst3115)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,true,false,false],0,.none⟩) (q := (.at 3121)) (e := .none) (k := 3121) (next := site3121)
  · rw [show raw78.siteIndex = 3115 from rfl]
    exact lookup3115
  · rw [show raw78.siteIndex = 3115 from rfl]
    exact resolved3115
  · decide
  · decide
  · rfl
  · exact lookup3121
  · decide
private def raw79 := PA215.Census.C031.records[79]
private theorem row79 : destinationAgrees raw79 = true := by
  apply destination_nonterminal (s := site3115) (i := inst3115)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,true,true],1,(.dec 5)⟩) (q := (.at 3116)) (e := (.dec 5)) (k := 3116) (next := site3116)
  · rw [show raw79.siteIndex = 3115 from rfl]
    exact lookup3115
  · rw [show raw79.siteIndex = 3115 from rfl]
    exact resolved3115
  · decide
  · decide
  · rfl
  · exact lookup3116
  · decide
private def raw80 := PA215.Census.C031.records[80]
private theorem row80 : destinationAgrees raw80 = true := by
  apply destination_nonterminal (s := site3116) (i := inst3116)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,true,true,false,false,true],0,(.inc 2)⟩) (q := (.at 3117)) (e := (.inc 2)) (k := 3117) (next := site3117)
  · rw [show raw80.siteIndex = 3116 from rfl]
    exact lookup3116
  · rw [show raw80.siteIndex = 3116 from rfl]
    exact resolved3116
  · decide
  · decide
  · rfl
  · exact lookup3117
  · decide
private def raw81 := PA215.Census.C031.records[81]
private theorem row81 : destinationAgrees raw81 = true := by
  apply destination_nonterminal (s := site3117) (i := inst3117)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,true,true,false,true,false],0,(.inc 2)⟩) (q := (.at 3118)) (e := (.inc 2)) (k := 3118) (next := site3118)
  · rw [show raw81.siteIndex = 3117 from rfl]
    exact lookup3117
  · rw [show raw81.siteIndex = 3117 from rfl]
    exact resolved3117
  · decide
  · decide
  · rfl
  · exact lookup3118
  · decide
private def raw82 := PA215.Census.C031.records[82]
private theorem row82 : destinationAgrees raw82 = true := by
  apply destination_nonterminal (s := site3118) (i := inst3118)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,true,true,false,true,true],0,(.inc 2)⟩) (q := (.at 3119)) (e := (.inc 2)) (k := 3119) (next := site3119)
  · rw [show raw82.siteIndex = 3118 from rfl]
    exact lookup3118
  · rw [show raw82.siteIndex = 3118 from rfl]
    exact resolved3118
  · decide
  · decide
  · rfl
  · exact lookup3119
  · decide
private def raw83 := PA215.Census.C031.records[83]
private theorem row83 : destinationAgrees raw83 = true := by
  apply destination_nonterminal (s := site3119) (i := inst3119)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,true,true,true,false,false],0,(.inc 2)⟩) (q := (.at 3120)) (e := (.inc 2)) (k := 3120) (next := site3120)
  · rw [show raw83.siteIndex = 3119 from rfl]
    exact lookup3119
  · rw [show raw83.siteIndex = 3119 from rfl]
    exact resolved3119
  · decide
  · decide
  · rfl
  · exact lookup3120
  · decide
private def raw84 := PA215.Census.C031.records[84]
private theorem row84 : destinationAgrees raw84 = true := by
  apply destination_nonterminal (s := site3120) (i := inst3120)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,false,true,false,true,true],0,.none⟩) (q := (.at 3115)) (e := .none) (k := 3115) (next := site3115)
  · rw [show raw84.siteIndex = 3120 from rfl]
    exact lookup3120
  · rw [show raw84.siteIndex = 3120 from rfl]
    exact resolved3120
  · decide
  · decide
  · rfl
  · exact lookup3115
  · decide
private def raw85 := PA215.Census.C031.records[85]
private theorem row85 : destinationAgrees raw85 = true := by
  apply destination_nonterminal (s := site3121) (i := inst3121)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false],0,(.inc 2)⟩) (q := (.at 3122)) (e := (.inc 2)) (k := 3122) (next := site3122)
  · rw [show raw85.siteIndex = 3121 from rfl]
    exact lookup3121
  · rw [show raw85.siteIndex = 3121 from rfl]
    exact resolved3121
  · decide
  · decide
  · rfl
  · exact lookup3122
  · decide
private def raw86 := PA215.Census.C031.records[86]
private theorem row86 : destinationAgrees raw86 = true := by
  apply destination_nonterminal (s := site3122) (i := inst3122)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,false,true],0,.none⟩) (q := (.at 3130)) (e := .none) (k := 3130) (next := site3130)
  · rw [show raw86.siteIndex = 3122 from rfl]
    exact lookup3122
  · rw [show raw86.siteIndex = 3122 from rfl]
    exact resolved3122
  · decide
  · decide
  · rfl
  · exact lookup3130
  · decide
private def raw87 := PA215.Census.C031.records[87]
private theorem row87 : destinationAgrees raw87 = true := by
  apply destination_nonterminal (s := site3122) (i := inst3122)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,false,false,true],1,(.dec 0)⟩) (q := (.at 3123)) (e := (.dec 0)) (k := 3123) (next := site3123)
  · rw [show raw87.siteIndex = 3122 from rfl]
    exact lookup3122
  · rw [show raw87.siteIndex = 3122 from rfl]
    exact resolved3122
  · decide
  · decide
  · rfl
  · exact lookup3123
  · decide
private def raw88 := PA215.Census.C031.records[88]
private theorem row88 : destinationAgrees raw88 = true := by
  apply destination_nonterminal (s := site3123) (i := inst3123)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,false,false,true,true],0,(.inc 5)⟩) (q := (.at 3124)) (e := (.inc 5)) (k := 3124) (next := site3124)
  · rw [show raw88.siteIndex = 3123 from rfl]
    exact lookup3123
  · rw [show raw88.siteIndex = 3123 from rfl]
    exact resolved3123
  · decide
  · decide
  · rfl
  · exact lookup3124
  · decide
private def raw89 := PA215.Census.C031.records[89]
private theorem row89 : destinationAgrees raw89 = true := by
  apply destination_nonterminal (s := site3124) (i := inst3124)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,false,false,true,true,false,true],0,.none⟩) (q := (.at 3126)) (e := .none) (k := 3126) (next := site3126)
  · rw [show raw89.siteIndex = 3124 from rfl]
    exact lookup3124
  · rw [show raw89.siteIndex = 3124 from rfl]
    exact resolved3124
  · decide
  · decide
  · rfl
  · exact lookup3126
  · decide
private def raw90 := PA215.Census.C031.records[90]
private theorem row90 : destinationAgrees raw90 = true := by
  apply destination_nonterminal (s := site3124) (i := inst3124)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,false,false,true,true,false,false,true],1,(.dec 8)⟩) (q := (.at 3125)) (e := (.dec 8)) (k := 3125) (next := site3125)
  · rw [show raw90.siteIndex = 3124 from rfl]
    exact lookup3124
  · rw [show raw90.siteIndex = 3124 from rfl]
    exact resolved3124
  · decide
  · decide
  · rfl
  · exact lookup3125
  · decide
private def raw91 := PA215.Census.C031.records[91]
private theorem row91 : destinationAgrees raw91 = true := by
  apply destination_nonterminal (s := site3125) (i := inst3125)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,false,false,true,true,true],0,.none⟩) (q := (.at 3129)) (e := .none) (k := 3129) (next := site3129)
  · rw [show raw91.siteIndex = 3125 from rfl]
    exact lookup3125
  · rw [show raw91.siteIndex = 3125 from rfl]
    exact resolved3125
  · decide
  · decide
  · rfl
  · exact lookup3129
  · decide
private def raw92 := PA215.Census.C031.records[92]
private theorem row92 : destinationAgrees raw92 = true := by
  apply destination_nonterminal (s := site3126) (i := inst3126)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,false,false,true,true,true,false],0,.none⟩) (q := (.at 3129)) (e := .none) (k := 3129) (next := site3129)
  · rw [show raw92.siteIndex = 3126 from rfl]
    exact lookup3126
  · rw [show raw92.siteIndex = 3126 from rfl]
    exact resolved3126
  · decide
  · decide
  · rfl
  · exact lookup3129
  · decide
private def raw93 := PA215.Census.C031.records[93]
private theorem row93 : destinationAgrees raw93 = true := by
  apply destination_nonterminal (s := site3126) (i := inst3126)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,false,false,true,true,false,true,true],1,(.dec 5)⟩) (q := (.at 3127)) (e := (.dec 5)) (k := 3127) (next := site3127)
  · rw [show raw93.siteIndex = 3126 from rfl]
    exact lookup3126
  · rw [show raw93.siteIndex = 3126 from rfl]
    exact resolved3126
  · decide
  · decide
  · rfl
  · exact lookup3127
  · decide
private def raw94 := PA215.Census.C031.records[94]
private theorem row94 : destinationAgrees raw94 = true := by
  apply destination_nonterminal (s := site3127) (i := inst3127)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,false,false,true,true,false,true,true,true],0,(.inc 8)⟩) (q := (.at 3128)) (e := (.inc 8)) (k := 3128) (next := site3128)
  · rw [show raw94.siteIndex = 3127 from rfl]
    exact lookup3127
  · rw [show raw94.siteIndex = 3127 from rfl]
    exact resolved3127
  · decide
  · decide
  · rfl
  · exact lookup3128
  · decide
private def raw95 := PA215.Census.C031.records[95]
private theorem row95 : destinationAgrees raw95 = true := by
  apply destination_nonterminal (s := site3128) (i := inst3128)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,false,false,true,true,false,true],0,.none⟩) (q := (.at 3126)) (e := .none) (k := 3126) (next := site3126)
  · rw [show raw95.siteIndex = 3128 from rfl]
    exact lookup3128
  · rw [show raw95.siteIndex = 3128 from rfl]
    exact resolved3128
  · decide
  · decide
  · rfl
  · exact lookup3126
  · decide
private def raw96 := PA215.Census.C031.records[96]
private theorem row96 : destinationAgrees raw96 = true := by
  apply destination_nonterminal (s := site3129) (i := inst3129)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,false,false],0,.none⟩) (q := (.at 3122)) (e := .none) (k := 3122) (next := site3122)
  · rw [show raw96.siteIndex = 3129 from rfl]
    exact lookup3129
  · rw [show raw96.siteIndex = 3129 from rfl]
    exact resolved3129
  · decide
  · decide
  · rfl
  · exact lookup3122
  · decide
private def raw97 := PA215.Census.C031.records[97]
private theorem row97 : destinationAgrees raw97 = true := by
  apply destination_nonterminal (s := site3130) (i := inst3130)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,false],0,.none⟩) (q := (.at 3133)) (e := .none) (k := 3133) (next := site3133)
  · rw [show raw97.siteIndex = 3130 from rfl]
    exact lookup3130
  · rw [show raw97.siteIndex = 3130 from rfl]
    exact resolved3130
  · decide
  · decide
  · rfl
  · exact lookup3133
  · decide
private def raw98 := PA215.Census.C031.records[98]
private theorem row98 : destinationAgrees raw98 = true := by
  apply destination_nonterminal (s := site3130) (i := inst3130)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,false,true,true],1,(.dec 5)⟩) (q := (.at 3131)) (e := (.dec 5)) (k := 3131) (next := site3131)
  · rw [show raw98.siteIndex = 3130 from rfl]
    exact lookup3130
  · rw [show raw98.siteIndex = 3130 from rfl]
    exact resolved3130
  · decide
  · decide
  · rfl
  · exact lookup3131
  · decide
private def raw99 := PA215.Census.C031.records[99]
private theorem row99 : destinationAgrees raw99 = true := by
  apply destination_nonterminal (s := site3131) (i := inst3131)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,false,true,true,true],0,(.inc 0)⟩) (q := (.at 3132)) (e := (.inc 0)) (k := 3132) (next := site3132)
  · rw [show raw99.siteIndex = 3131 from rfl]
    exact lookup3131
  · rw [show raw99.siteIndex = 3131 from rfl]
    exact resolved3131
  · decide
  · decide
  · rfl
  · exact lookup3132
  · decide
private def raw100 := PA215.Census.C031.records[100]
private theorem row100 : destinationAgrees raw100 = true := by
  apply destination_nonterminal (s := site3132) (i := inst3132)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,false,true],0,.none⟩) (q := (.at 3130)) (e := .none) (k := 3130) (next := site3130)
  · rw [show raw100.siteIndex = 3132 from rfl]
    exact lookup3132
  · rw [show raw100.siteIndex = 3132 from rfl]
    exact resolved3132
  · decide
  · decide
  · rfl
  · exact lookup3130
  · decide
private def raw101 := PA215.Census.C031.records[101]
private theorem row101 : destinationAgrees raw101 = true := by
  apply destination_nonterminal (s := site3133) (i := inst3133)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,false,true],0,.none⟩) (q := (.at 3137)) (e := .none) (k := 3137) (next := site3137)
  · rw [show raw101.siteIndex = 3133 from rfl]
    exact lookup3133
  · rw [show raw101.siteIndex = 3133 from rfl]
    exact resolved3133
  · decide
  · decide
  · rfl
  · exact lookup3137
  · decide
private def raw102 := PA215.Census.C031.records[102]
private theorem row102 : destinationAgrees raw102 = true := by
  apply destination_nonterminal (s := site3133) (i := inst3133)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,false,false,true],1,(.dec 2)⟩) (q := (.at 3134)) (e := (.dec 2)) (k := 3134) (next := site3134)
  · rw [show raw102.siteIndex = 3133 from rfl]
    exact lookup3133
  · rw [show raw102.siteIndex = 3133 from rfl]
    exact resolved3133
  · decide
  · decide
  · rfl
  · exact lookup3134
  · decide
private def raw103 := PA215.Census.C031.records[103]
private theorem row103 : destinationAgrees raw103 = true := by
  apply destination_nonterminal (s := site3134) (i := inst3134)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,false,false,true,true],0,(.inc 5)⟩) (q := (.at 3135)) (e := (.inc 5)) (k := 3135) (next := site3135)
  · rw [show raw103.siteIndex = 3134 from rfl]
    exact lookup3134
  · rw [show raw103.siteIndex = 3134 from rfl]
    exact resolved3134
  · decide
  · decide
  · rfl
  · exact lookup3135
  · decide
private def raw104 := PA215.Census.C031.records[104]
private theorem row104 : destinationAgrees raw104 = true := by
  apply destination_nonterminal (s := site3135) (i := inst3135)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,false,false,true,true,true],0,(.inc 8)⟩) (q := (.at 3136)) (e := (.inc 8)) (k := 3136) (next := site3136)
  · rw [show raw104.siteIndex = 3135 from rfl]
    exact lookup3135
  · rw [show raw104.siteIndex = 3135 from rfl]
    exact resolved3135
  · decide
  · decide
  · rfl
  · exact lookup3136
  · decide
private def raw105 := PA215.Census.C031.records[105]
private theorem row105 : destinationAgrees raw105 = true := by
  apply destination_nonterminal (s := site3136) (i := inst3136)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,false,false],0,.none⟩) (q := (.at 3133)) (e := .none) (k := 3133) (next := site3133)
  · rw [show raw105.siteIndex = 3136 from rfl]
    exact lookup3136
  · rw [show raw105.siteIndex = 3136 from rfl]
    exact resolved3136
  · decide
  · decide
  · rfl
  · exact lookup3133
  · decide
private def raw106 := PA215.Census.C031.records[106]
private theorem row106 : destinationAgrees raw106 = true := by
  apply destination_nonterminal (s := site3137) (i := inst3137)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,true,false],0,.none⟩) (q := (.at 3143)) (e := .none) (k := 3143) (next := site3143)
  · rw [show raw106.siteIndex = 3137 from rfl]
    exact lookup3137
  · rw [show raw106.siteIndex = 3137 from rfl]
    exact resolved3137
  · decide
  · decide
  · rfl
  · exact lookup3143
  · decide
private def raw107 := PA215.Census.C031.records[107]
private theorem row107 : destinationAgrees raw107 = true := by
  apply destination_nonterminal (s := site3137) (i := inst3137)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true],1,(.dec 8)⟩) (q := (.at 3138)) (e := (.dec 8)) (k := 3138) (next := site3138)
  · rw [show raw107.siteIndex = 3137 from rfl]
    exact lookup3137
  · rw [show raw107.siteIndex = 3137 from rfl]
    exact resolved3137
  · decide
  · decide
  · rfl
  · exact lookup3138
  · decide
private def raw108 := PA215.Census.C031.records[108]
private theorem row108 : destinationAgrees raw108 = true := by
  apply destination_nonterminal (s := site3138) (i := inst3138)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,true],0,(.inc 5)⟩) (q := (.at 3139)) (e := (.inc 5)) (k := 3139) (next := site3139)
  · rw [show raw108.siteIndex = 3138 from rfl]
    exact lookup3138
  · rw [show raw108.siteIndex = 3138 from rfl]
    exact resolved3138
  · decide
  · decide
  · rfl
  · exact lookup3139
  · decide
private def raw109 := PA215.Census.C031.records[109]
private theorem row109 : destinationAgrees raw109 = true := by
  apply destination_nonterminal (s := site3139) (i := inst3139)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,true,false],0,.none⟩) (q := (.at 3142)) (e := .none) (k := 3142) (next := site3142)
  · rw [show raw109.siteIndex = 3139 from rfl]
    exact lookup3139
  · rw [show raw109.siteIndex = 3139 from rfl]
    exact resolved3139
  · decide
  · decide
  · rfl
  · exact lookup3142
  · decide
private def raw110 := PA215.Census.C031.records[110]
private theorem row110 : destinationAgrees raw110 = true := by
  apply destination_nonterminal (s := site3139) (i := inst3139)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,true,true],1,(.dec 8)⟩) (q := (.at 3140)) (e := (.dec 8)) (k := 3140) (next := site3140)
  · rw [show raw110.siteIndex = 3139 from rfl]
    exact lookup3139
  · rw [show raw110.siteIndex = 3139 from rfl]
    exact resolved3139
  · decide
  · decide
  · rfl
  · exact lookup3140
  · decide
private def raw111 := PA215.Census.C031.records[111]
private theorem row111 : destinationAgrees raw111 = true := by
  apply destination_nonterminal (s := site3140) (i := inst3140)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,true,true,true],0,(.inc 2)⟩) (q := (.at 3141)) (e := (.inc 2)) (k := 3141) (next := site3141)
  · rw [show raw111.siteIndex = 3140 from rfl]
    exact lookup3140
  · rw [show raw111.siteIndex = 3140 from rfl]
    exact resolved3140
  · decide
  · decide
  · rfl
  · exact lookup3141
  · decide
private def raw112 := PA215.Census.C031.records[112]
private theorem row112 : destinationAgrees raw112 = true := by
  apply destination_nonterminal (s := site3141) (i := inst3141)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,false,true,true,false,true],0,.none⟩) (q := (.at 3139)) (e := .none) (k := 3139) (next := site3139)
  · rw [show raw112.siteIndex = 3141 from rfl]
    exact lookup3141
  · rw [show raw112.siteIndex = 3141 from rfl]
    exact resolved3141
  · decide
  · decide
  · rfl
  · exact lookup3139
  · decide
private def raw113 := PA215.Census.C031.records[113]
private theorem row113 : destinationAgrees raw113 = true := by
  apply destination_nonterminal (s := site3142) (i := inst3142)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,false],0,.none⟩) (q := (.at 3133)) (e := .none) (k := 3133) (next := site3133)
  · rw [show raw113.siteIndex = 3142 from rfl]
    exact lookup3142
  · rw [show raw113.siteIndex = 3142 from rfl]
    exact resolved3142
  · decide
  · decide
  · rfl
  · exact lookup3133
  · decide
private def raw114 := PA215.Census.C031.records[114]
private theorem row114 : destinationAgrees raw114 = true := by
  apply destination_nonterminal (s := site3143) (i := inst3143)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,true,false,false],0,.none⟩) (q := (.at 3149)) (e := .none) (k := 3149) (next := site3149)
  · rw [show raw114.siteIndex = 3143 from rfl]
    exact lookup3143
  · rw [show raw114.siteIndex = 3143 from rfl]
    exact resolved3143
  · decide
  · decide
  · rfl
  · exact lookup3149
  · decide
private def raw115 := PA215.Census.C031.records[115]
private theorem row115 : destinationAgrees raw115 = true := by
  apply destination_nonterminal (s := site3143) (i := inst3143)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,true,true],1,(.dec 5)⟩) (q := (.at 3144)) (e := (.dec 5)) (k := 3144) (next := site3144)
  · rw [show raw115.siteIndex = 3143 from rfl]
    exact lookup3143
  · rw [show raw115.siteIndex = 3143 from rfl]
    exact resolved3143
  · decide
  · decide
  · rfl
  · exact lookup3144
  · decide
private def raw116 := PA215.Census.C031.records[116]
private theorem row116 : destinationAgrees raw116 = true := by
  apply destination_nonterminal (s := site3144) (i := inst3144)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,true,true,false,false,true],0,(.inc 2)⟩) (q := (.at 3145)) (e := (.inc 2)) (k := 3145) (next := site3145)
  · rw [show raw116.siteIndex = 3144 from rfl]
    exact lookup3144
  · rw [show raw116.siteIndex = 3144 from rfl]
    exact resolved3144
  · decide
  · decide
  · rfl
  · exact lookup3145
  · decide
private def raw117 := PA215.Census.C031.records[117]
private theorem row117 : destinationAgrees raw117 = true := by
  apply destination_nonterminal (s := site3145) (i := inst3145)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,true,true,false,true,false],0,(.inc 2)⟩) (q := (.at 3146)) (e := (.inc 2)) (k := 3146) (next := site3146)
  · rw [show raw117.siteIndex = 3145 from rfl]
    exact lookup3145
  · rw [show raw117.siteIndex = 3145 from rfl]
    exact resolved3145
  · decide
  · decide
  · rfl
  · exact lookup3146
  · decide
private def raw118 := PA215.Census.C031.records[118]
private theorem row118 : destinationAgrees raw118 = true := by
  apply destination_nonterminal (s := site3146) (i := inst3146)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,true,true,false,true,true],0,(.inc 2)⟩) (q := (.at 3147)) (e := (.inc 2)) (k := 3147) (next := site3147)
  · rw [show raw118.siteIndex = 3146 from rfl]
    exact lookup3146
  · rw [show raw118.siteIndex = 3146 from rfl]
    exact resolved3146
  · decide
  · decide
  · rfl
  · exact lookup3147
  · decide
private def raw119 := PA215.Census.C031.records[119]
private theorem row119 : destinationAgrees raw119 = true := by
  apply destination_nonterminal (s := site3147) (i := inst3147)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,true,true,true,false,false],0,(.inc 2)⟩) (q := (.at 3148)) (e := (.inc 2)) (k := 3148) (next := site3148)
  · rw [show raw119.siteIndex = 3147 from rfl]
    exact lookup3147
  · rw [show raw119.siteIndex = 3147 from rfl]
    exact resolved3147
  · decide
  · decide
  · rfl
  · exact lookup3148
  · decide
private def raw120 := PA215.Census.C031.records[120]
private theorem row120 : destinationAgrees raw120 = true := by
  apply destination_nonterminal (s := site3148) (i := inst3148)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,false,true,true],0,.none⟩) (q := (.at 3143)) (e := .none) (k := 3143) (next := site3143)
  · rw [show raw120.siteIndex = 3148 from rfl]
    exact lookup3148
  · rw [show raw120.siteIndex = 3148 from rfl]
    exact resolved3148
  · decide
  · decide
  · rfl
  · exact lookup3143
  · decide
private def raw121 := PA215.Census.C031.records[121]
private theorem row121 : destinationAgrees raw121 = true := by
  apply destination_nonterminal (s := site3149) (i := inst3149)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,true,false,true],0,.none⟩) (q := (.at 3157)) (e := .none) (k := 3157) (next := site3157)
  · rw [show raw121.siteIndex = 3149 from rfl]
    exact lookup3149
  · rw [show raw121.siteIndex = 3149 from rfl]
    exact resolved3149
  · decide
  · decide
  · rfl
  · exact lookup3157
  · decide
private def raw122 := PA215.Census.C031.records[122]
private theorem row122 : destinationAgrees raw122 = true := by
  apply destination_nonterminal (s := site3149) (i := inst3149)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,true,false,false,true],1,(.dec 0)⟩) (q := (.at 3150)) (e := (.dec 0)) (k := 3150) (next := site3150)
  · rw [show raw122.siteIndex = 3149 from rfl]
    exact lookup3149
  · rw [show raw122.siteIndex = 3149 from rfl]
    exact resolved3149
  · decide
  · decide
  · rfl
  · exact lookup3150
  · decide
private def raw123 := PA215.Census.C031.records[123]
private theorem row123 : destinationAgrees raw123 = true := by
  apply destination_nonterminal (s := site3150) (i := inst3150)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,true,false,false,true,true],0,(.inc 5)⟩) (q := (.at 3151)) (e := (.inc 5)) (k := 3151) (next := site3151)
  · rw [show raw123.siteIndex = 3150 from rfl]
    exact lookup3150
  · rw [show raw123.siteIndex = 3150 from rfl]
    exact resolved3150
  · decide
  · decide
  · rfl
  · exact lookup3151
  · decide
private def raw124 := PA215.Census.C031.records[124]
private theorem row124 : destinationAgrees raw124 = true := by
  apply destination_nonterminal (s := site3151) (i := inst3151)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,true,false,false,true,true,false,true],0,.none⟩) (q := (.at 3153)) (e := .none) (k := 3153) (next := site3153)
  · rw [show raw124.siteIndex = 3151 from rfl]
    exact lookup3151
  · rw [show raw124.siteIndex = 3151 from rfl]
    exact resolved3151
  · decide
  · decide
  · rfl
  · exact lookup3153
  · decide
private def raw125 := PA215.Census.C031.records[125]
private theorem row125 : destinationAgrees raw125 = true := by
  apply destination_nonterminal (s := site3151) (i := inst3151)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,true,false,false,true,true,false,false,true],1,(.dec 8)⟩) (q := (.at 3152)) (e := (.dec 8)) (k := 3152) (next := site3152)
  · rw [show raw125.siteIndex = 3151 from rfl]
    exact lookup3151
  · rw [show raw125.siteIndex = 3151 from rfl]
    exact resolved3151
  · decide
  · decide
  · rfl
  · exact lookup3152
  · decide
private def raw126 := PA215.Census.C031.records[126]
private theorem row126 : destinationAgrees raw126 = true := by
  apply destination_nonterminal (s := site3152) (i := inst3152)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,true,false,false,true,true,true],0,.none⟩) (q := (.at 3156)) (e := .none) (k := 3156) (next := site3156)
  · rw [show raw126.siteIndex = 3152 from rfl]
    exact lookup3152
  · rw [show raw126.siteIndex = 3152 from rfl]
    exact resolved3152
  · decide
  · decide
  · rfl
  · exact lookup3156
  · decide
private def raw127 := PA215.Census.C031.records[127]
private theorem row127 : destinationAgrees raw127 = true := by
  apply destination_nonterminal (s := site3153) (i := inst3153)
    (p := ⟨[true,false,true,false,false,true,false,true,true,true,true,false,true,true,true,false,true,false,false,true,true,true,false],0,.none⟩) (q := (.at 3156)) (e := .none) (k := 3156) (next := site3156)
  · rw [show raw127.siteIndex = 3153 from rfl]
    exact lookup3153
  · rw [show raw127.siteIndex = 3153 from rfl]
    exact resolved3153
  · decide
  · decide
  · rfl
  · exact lookup3156
  · decide
private theorem enumeration : PA215.Census.C031.records.toList = [raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7,raw8,raw9,raw10,raw11,raw12,raw13,raw14,raw15,raw16,raw17,raw18,raw19,raw20,raw21,raw22,raw23,raw24,raw25,raw26,raw27,raw28,raw29,raw30,raw31,raw32,raw33,raw34,raw35,raw36,raw37,raw38,raw39,raw40,raw41,raw42,raw43,raw44,raw45,raw46,raw47,raw48,raw49,raw50,raw51,raw52,raw53,raw54,raw55,raw56,raw57,raw58,raw59,raw60,raw61,raw62,raw63,raw64,raw65,raw66,raw67,raw68,raw69,raw70,raw71,raw72,raw73,raw74,raw75,raw76,raw77,raw78,raw79,raw80,raw81,raw82,raw83,raw84,raw85,raw86,raw87,raw88,raw89,raw90,raw91,raw92,raw93,raw94,raw95,raw96,raw97,raw98,raw99,raw100,raw101,raw102,raw103,raw104,raw105,raw106,raw107,raw108,raw109,raw110,raw111,raw112,raw113,raw114,raw115,raw116,raw117,raw118,raw119,raw120,raw121,raw122,raw123,raw124,raw125,raw126,raw127] := by rfl
theorem checked : PA215.Census.C031.records.toList.all destinationAgrees = true := by
  rw [enumeration]
  simp only [List.all_cons,List.all_nil,row0,row1,row2,row3,row4,row5,row6,row7,row8,row9,row10,row11,row12,row13,row14,row15,row16,row17,row18,row19,row20,row21,row22,row23,row24,row25,row26,row27,row28,row29,row30,row31,row32,row33,row34,row35,row36,row37,row38,row39,row40,row41,row42,row43,row44,row45,row46,row47,row48,row49,row50,row51,row52,row53,row54,row55,row56,row57,row58,row59,row60,row61,row62,row63,row64,row65,row66,row67,row68,row69,row70,row71,row72,row73,row74,row75,row76,row77,row78,row79,row80,row81,row82,row83,row84,row85,row86,row87,row88,row89,row90,row91,row92,row93,row94,row95,row96,row97,row98,row99,row100,row101,row102,row103,row104,row105,row106,row107,row108,row109,row110,row111,row112,row113,row114,row115,row116,row117,row118,row119,row120,row121,row122,row123,row124,row125,row126,row127,Bool.and_self]
#print axioms checked
end PA215.Source.DestinationJoin.D031
