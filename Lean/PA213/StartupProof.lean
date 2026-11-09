module

public import PA213.Startup.S000
public import PA213.Startup.S001
public import PA213.Startup.S002
public import PA213.Startup.S003
public import PA213.Startup.S004
public import PA213.Startup.S005
public import PA213.Startup.S006
public import PA213.Startup.S007
public import PA213.Startup.S008
public import PA213.Startup.S009
public import PA213.Startup.S010
public import PA213.Startup.S011
public import PA213.Startup.S012
public import PA213.Startup.S013
public import PA213.Startup.S014
public import PA213.Startup.S015

@[expose] public section

namespace PA213.Startup
open PA215.Zip PA213.CandidateTable

theorem startup_positive : Reach1 machine blank startupTarget := by
  rw [← checkpoint_initial, ← checkpoint_final]
  have first : Reach1 machine checkpoint000 checkpoint001 := ⟨255, run000⟩
  have step001 := first.trans_reach reach001
  have step002 := step001.trans_reach reach002
  have step003 := step002.trans_reach reach003
  have step004 := step003.trans_reach reach004
  have step005 := step004.trans_reach reach005
  have step006 := step005.trans_reach reach006
  have step007 := step006.trans_reach reach007
  have step008 := step007.trans_reach reach008
  have step009 := step008.trans_reach reach009
  have step010 := step009.trans_reach reach010
  have step011 := step010.trans_reach reach011
  have step012 := step011.trans_reach reach012
  have step013 := step012.trans_reach reach013
  have step014 := step013.trans_reach reach014
  have step015 := step014.trans_reach reach015
  have step016 := step015.trans_reach reach016
  have step017 := step016.trans_reach reach017
  have step018 := step017.trans_reach reach018
  have step019 := step018.trans_reach reach019
  have step020 := step019.trans_reach reach020
  have step021 := step020.trans_reach reach021
  have step022 := step021.trans_reach reach022
  have step023 := step022.trans_reach reach023
  have step024 := step023.trans_reach reach024
  have step025 := step024.trans_reach reach025
  have step026 := step025.trans_reach reach026
  have step027 := step026.trans_reach reach027
  have step028 := step027.trans_reach reach028
  have step029 := step028.trans_reach reach029
  have step030 := step029.trans_reach reach030
  have step031 := step030.trans_reach reach031
  have step032 := step031.trans_reach reach032
  have step033 := step032.trans_reach reach033
  have step034 := step033.trans_reach reach034
  have step035 := step034.trans_reach reach035
  have step036 := step035.trans_reach reach036
  have step037 := step036.trans_reach reach037
  have step038 := step037.trans_reach reach038
  have step039 := step038.trans_reach reach039
  have step040 := step039.trans_reach reach040
  have step041 := step040.trans_reach reach041
  have step042 := step041.trans_reach reach042
  have step043 := step042.trans_reach reach043
  have step044 := step043.trans_reach reach044
  have step045 := step044.trans_reach reach045
  have step046 := step045.trans_reach reach046
  have step047 := step046.trans_reach reach047
  have step048 := step047.trans_reach reach048
  have step049 := step048.trans_reach reach049
  have step050 := step049.trans_reach reach050
  have step051 := step050.trans_reach reach051
  have step052 := step051.trans_reach reach052
  have step053 := step052.trans_reach reach053
  have step054 := step053.trans_reach reach054
  have step055 := step054.trans_reach reach055
  have step056 := step055.trans_reach reach056
  have step057 := step056.trans_reach reach057
  have step058 := step057.trans_reach reach058
  have step059 := step058.trans_reach reach059
  have step060 := step059.trans_reach reach060
  have step061 := step060.trans_reach reach061
  have step062 := step061.trans_reach reach062
  have step063 := step062.trans_reach reach063
  have step064 := step063.trans_reach reach064
  have step065 := step064.trans_reach reach065
  have step066 := step065.trans_reach reach066
  have step067 := step066.trans_reach reach067
  have step068 := step067.trans_reach reach068
  have step069 := step068.trans_reach reach069
  have step070 := step069.trans_reach reach070
  have step071 := step070.trans_reach reach071
  have step072 := step071.trans_reach reach072
  have step073 := step072.trans_reach reach073
  have step074 := step073.trans_reach reach074
  have step075 := step074.trans_reach reach075
  have step076 := step075.trans_reach reach076
  have step077 := step076.trans_reach reach077
  have step078 := step077.trans_reach reach078
  have step079 := step078.trans_reach reach079
  have step080 := step079.trans_reach reach080
  have step081 := step080.trans_reach reach081
  have step082 := step081.trans_reach reach082
  have step083 := step082.trans_reach reach083
  have step084 := step083.trans_reach reach084
  have step085 := step084.trans_reach reach085
  have step086 := step085.trans_reach reach086
  have step087 := step086.trans_reach reach087
  have step088 := step087.trans_reach reach088
  have step089 := step088.trans_reach reach089
  have step090 := step089.trans_reach reach090
  have step091 := step090.trans_reach reach091
  have step092 := step091.trans_reach reach092
  have step093 := step092.trans_reach reach093
  have step094 := step093.trans_reach reach094
  have step095 := step094.trans_reach reach095
  have step096 := step095.trans_reach reach096
  have step097 := step096.trans_reach reach097
  have step098 := step097.trans_reach reach098
  have step099 := step098.trans_reach reach099
  have step100 := step099.trans_reach reach100
  have step101 := step100.trans_reach reach101
  have step102 := step101.trans_reach reach102
  have step103 := step102.trans_reach reach103
  have step104 := step103.trans_reach reach104
  have step105 := step104.trans_reach reach105
  have step106 := step105.trans_reach reach106
  have step107 := step106.trans_reach reach107
  have step108 := step107.trans_reach reach108
  have step109 := step108.trans_reach reach109
  have step110 := step109.trans_reach reach110
  have step111 := step110.trans_reach reach111
  have step112 := step111.trans_reach reach112
  have step113 := step112.trans_reach reach113
  have step114 := step113.trans_reach reach114
  have step115 := step114.trans_reach reach115
  have step116 := step115.trans_reach reach116
  have step117 := step116.trans_reach reach117
  have step118 := step117.trans_reach reach118
  have step119 := step118.trans_reach reach119
  have step120 := step119.trans_reach reach120
  have step121 := step120.trans_reach reach121
  have step122 := step121.trans_reach reach122
  have step123 := step122.trans_reach reach123
  have step124 := step123.trans_reach reach124
  have step125 := step124.trans_reach reach125
  have step126 := step125.trans_reach reach126
  have step127 := step126.trans_reach reach127
  have step128 := step127.trans_reach reach128
  have step129 := step128.trans_reach reach129
  have step130 := step129.trans_reach reach130
  have step131 := step130.trans_reach reach131
  have step132 := step131.trans_reach reach132
  have step133 := step132.trans_reach reach133
  have step134 := step133.trans_reach reach134
  have step135 := step134.trans_reach reach135
  have step136 := step135.trans_reach reach136
  have step137 := step136.trans_reach reach137
  have step138 := step137.trans_reach reach138
  have step139 := step138.trans_reach reach139
  have step140 := step139.trans_reach reach140
  have step141 := step140.trans_reach reach141
  have step142 := step141.trans_reach reach142
  have step143 := step142.trans_reach reach143
  have step144 := step143.trans_reach reach144
  have step145 := step144.trans_reach reach145
  have step146 := step145.trans_reach reach146
  have step147 := step146.trans_reach reach147
  have step148 := step147.trans_reach reach148
  have step149 := step148.trans_reach reach149
  have step150 := step149.trans_reach reach150
  have step151 := step150.trans_reach reach151
  have step152 := step151.trans_reach reach152
  have step153 := step152.trans_reach reach153
  have step154 := step153.trans_reach reach154
  have step155 := step154.trans_reach reach155
  have step156 := step155.trans_reach reach156
  have step157 := step156.trans_reach reach157
  have step158 := step157.trans_reach reach158
  have step159 := step158.trans_reach reach159
  have step160 := step159.trans_reach reach160
  have step161 := step160.trans_reach reach161
  have step162 := step161.trans_reach reach162
  have step163 := step162.trans_reach reach163
  have step164 := step163.trans_reach reach164
  have step165 := step164.trans_reach reach165
  have step166 := step165.trans_reach reach166
  have step167 := step166.trans_reach reach167
  have step168 := step167.trans_reach reach168
  have step169 := step168.trans_reach reach169
  have step170 := step169.trans_reach reach170
  have step171 := step170.trans_reach reach171
  have step172 := step171.trans_reach reach172
  have step173 := step172.trans_reach reach173
  have step174 := step173.trans_reach reach174
  have step175 := step174.trans_reach reach175
  have step176 := step175.trans_reach reach176
  have step177 := step176.trans_reach reach177
  have step178 := step177.trans_reach reach178
  have step179 := step178.trans_reach reach179
  have step180 := step179.trans_reach reach180
  have step181 := step180.trans_reach reach181
  have step182 := step181.trans_reach reach182
  have step183 := step182.trans_reach reach183
  have step184 := step183.trans_reach reach184
  have step185 := step184.trans_reach reach185
  have step186 := step185.trans_reach reach186
  have step187 := step186.trans_reach reach187
  have step188 := step187.trans_reach reach188
  have step189 := step188.trans_reach reach189
  have step190 := step189.trans_reach reach190
  have step191 := step190.trans_reach reach191
  have step192 := step191.trans_reach reach192
  have step193 := step192.trans_reach reach193
  have step194 := step193.trans_reach reach194
  have step195 := step194.trans_reach reach195
  have step196 := step195.trans_reach reach196
  have step197 := step196.trans_reach reach197
  have step198 := step197.trans_reach reach198
  have step199 := step198.trans_reach reach199
  have step200 := step199.trans_reach reach200
  have step201 := step200.trans_reach reach201
  have step202 := step201.trans_reach reach202
  have step203 := step202.trans_reach reach203
  have step204 := step203.trans_reach reach204
  have step205 := step204.trans_reach reach205
  have step206 := step205.trans_reach reach206
  have step207 := step206.trans_reach reach207
  have step208 := step207.trans_reach reach208
  have step209 := step208.trans_reach reach209
  have step210 := step209.trans_reach reach210
  have step211 := step210.trans_reach reach211
  have step212 := step211.trans_reach reach212
  have step213 := step212.trans_reach reach213
  have step214 := step213.trans_reach reach214
  have step215 := step214.trans_reach reach215
  have step216 := step215.trans_reach reach216
  have step217 := step216.trans_reach reach217
  have step218 := step217.trans_reach reach218
  have step219 := step218.trans_reach reach219
  have step220 := step219.trans_reach reach220
  have step221 := step220.trans_reach reach221
  have step222 := step221.trans_reach reach222
  have step223 := step222.trans_reach reach223
  have step224 := step223.trans_reach reach224
  have step225 := step224.trans_reach reach225
  have step226 := step225.trans_reach reach226
  have step227 := step226.trans_reach reach227
  have step228 := step227.trans_reach reach228
  have step229 := step228.trans_reach reach229
  have step230 := step229.trans_reach reach230
  have step231 := step230.trans_reach reach231
  have step232 := step231.trans_reach reach232
  have step233 := step232.trans_reach reach233
  have step234 := step233.trans_reach reach234
  have step235 := step234.trans_reach reach235
  have step236 := step235.trans_reach reach236
  have step237 := step236.trans_reach reach237
  have step238 := step237.trans_reach reach238
  have step239 := step238.trans_reach reach239
  have step240 := step239.trans_reach reach240
  have step241 := step240.trans_reach reach241
  have step242 := step241.trans_reach reach242
  have step243 := step242.trans_reach reach243
  have step244 := step243.trans_reach reach244
  have step245 := step244.trans_reach reach245
  have step246 := step245.trans_reach reach246
  have step247 := step246.trans_reach reach247
  have step248 := step247.trans_reach reach248
  have step249 := step248.trans_reach reach249
  have step250 := step249.trans_reach reach250
  have step251 := step250.trans_reach reach251
  have step252 := step251.trans_reach reach252
  exact step252

#print axioms startup_positive
end PA213.Startup
