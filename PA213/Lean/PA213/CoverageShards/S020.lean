import PA213.PrimitiveSimulation
import PA213.FastPaths
import PA213.RuntimeShards.S026
import PA213.RuntimeShards.S027
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace PA213.CoverageShards.S020
open PA215.Source PA213.SourceProgram PA213.PathBounds PA213.PrimitiveSimulation
def e1280 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,false,true,true], .continueTo 2⟩, .jump (some 1278), implements_jump PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,false,true,true] (some 1278) 0 91 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1280_plain_checked⟩
def e1281 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,false,false], .dec 2⟩, .dec 2 (some 1284) (some 1282), implements_dec PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,false,false] 2 (some 1284) (some 1282) 0 1 356 362 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1281_zero_checked PA213.RuntimeShards.S026.s1281_positive_checked⟩
def e1282 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,false,true,false], .inc 1⟩, .inc 1 (some 1283), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,false,true,false] 1 (some 1283) 0 354 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1282_plain_checked⟩
def e1283 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,false,true,true], .continueTo 2⟩, .jump (some 1281), implements_jump PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,false,true,true] (some 1281) 0 94 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1283_plain_checked⟩
def e1284 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,true,false,false,false], .dec 1⟩, .dec 1 (some 1288) (some 1285), implements_dec PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,true,false,false,false] 1 (some 1288) (some 1285) 0 1 362 368 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1284_zero_checked PA213.RuntimeShards.S026.s1284_positive_checked⟩
def e1285 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,true,false,false,true,false], .inc 7⟩, .inc 7 (some 1286), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,true,false,false,true,false] 7 (some 1286) 0 381 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1285_plain_checked⟩
def e1286 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,true,false,false,true,true,false], .inc 6⟩, .inc 6 (some 1287), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,true,false,false,true,true,false] 6 (some 1287) 0 408 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1286_plain_checked⟩
def e1287 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,true,false,false,true,true,true], .continueTo 3⟩, .jump (some 1284), implements_jump PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,true,false,false,true,true,true] (some 1284) 0 109 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1287_plain_checked⟩
def e1288 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 1294) (some 1289), implements_dec PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,true,false,true,false] 6 (some 1294) (some 1289) 0 1 383 386 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1288_zero_checked PA213.RuntimeShards.S026.s1288_positive_checked⟩
def e1289 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,true,false,true,true,false,false], .inc 7⟩, .inc 7 (some 1290), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,true,false,true,true,false,false] 7 (some 1290) 0 381 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1289_plain_checked⟩
def e1290 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,true,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 1293) (some 1291), implements_dec PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,true,false,true,true,false,true,false] 6 (some 1293) (some 1291) 0 1 401 404 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1290_zero_checked PA213.RuntimeShards.S026.s1290_positive_checked⟩
def e1291 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,true,false,true,true,false,true,true,false], .inc 1⟩, .inc 1 (some 1292), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,true,false,true,true,false,true,true,false] 1 (some 1292) 0 399 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1291_plain_checked⟩
def e1292 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,true,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 1290), implements_jump PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,true,false,true,true,false,true,true,true] (some 1290) 0 109 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1292_plain_checked⟩
def e1293 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,true,false,true,true,true], .continueTo 3⟩, .jump (some 1284), implements_jump PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,true,false,true,true,true] (some 1284) 0 112 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1293_plain_checked⟩
def e1294 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,true,true,false], .dec 7⟩, .dec 7 (some 1297) (some 1295), implements_dec PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,true,true,false] 7 (some 1297) (some 1295) 0 1 371 368 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1294_zero_checked PA213.RuntimeShards.S026.s1294_positive_checked⟩
def e1295 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,true,true,true,false], .inc 2⟩, .inc 2 (some 1296), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,true,true,true,false] 2 (some 1296) 0 381 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1295_plain_checked⟩
def e1296 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,true,true,true,true], .continueTo 2⟩, .jump (some 1294), implements_jump PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,false,true,true,true,true,true] (some 1294) 0 100 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1296_plain_checked⟩
def e1297 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,true,false,false], .dec 5⟩, .dec 5 (some 1301) (some 1298), implements_dec PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,true,false,false] 5 (some 1301) (some 1298) 0 1 335 341 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1297_zero_checked PA213.RuntimeShards.S026.s1297_positive_checked⟩
def e1298 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,true,false,true,false], .inc 1⟩, .inc 1 (some 1299), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,true,false,true,false] 1 (some 1299) 0 345 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1298_plain_checked⟩
def e1299 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,true,false,true,true,false], .inc 6⟩, .inc 6 (some 1300), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,true,false,true,true,false] 6 (some 1300) 0 372 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1299_plain_checked⟩
def e1300 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,true,false,true,true,true], .continueTo 3⟩, .jump (some 1297), implements_jump PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,true,false,true,true,true] (some 1297) 0 97 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1300_plain_checked⟩
def e1301 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,true,true,false], .dec 6⟩, .dec 6 (some 1304) (some 1302), implements_dec PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,true,true,false] 6 (some 1304) (some 1302) 0 1 344 341 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1301_zero_checked PA213.RuntimeShards.S026.s1301_positive_checked⟩
def e1302 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,true,true,true,false], .inc 5⟩, .inc 5 (some 1303), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,true,true,true,false] 5 (some 1303) 0 372 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1302_plain_checked⟩
def e1303 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,true,true,true,true], .continueTo 2⟩, .jump (some 1301), implements_jump PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,false,true,true,true,true,true] (some 1301) 0 91 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1303_plain_checked⟩
def e1304 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,false,false,false], .dec 2⟩, .dec 2 (some 1312) (some 1305), implements_dec PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,false,false,false] 2 (some 1312) (some 1305) 0 1 347 353 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1304_zero_checked PA213.RuntimeShards.S026.s1304_positive_checked⟩
def e1305 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,false,false,true,false], .inc 7⟩, .inc 7 (some 1306), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,false,false,true,false] 7 (some 1306) 0 363 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1305_plain_checked⟩
def e1306 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,false,false,true,true,false,false,false], .dec 6⟩, .dec 6 (some 1308) (some 1307), implements_dec PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,false,false,true,true,false,false,false] 6 (some 1308) (some 1307) 0 1 389 395 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1306_zero_checked PA213.RuntimeShards.S026.s1306_positive_checked⟩
def e1307 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,false,false,true,true,false,false,true], .breakTo 1⟩, .jump (some 1311), implements_jump PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,false,false,true,true,false,false,true] (some 1311) 0 106 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1307_plain_checked⟩
def e1308 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,false,false,true,true,false,true,false], .dec 7⟩, .dec 7 (some 1311) (some 1309), implements_dec PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,false,false,true,true,false,true,false] 7 (some 1311) (some 1309) 0 1 401 404 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1308_zero_checked PA213.RuntimeShards.S026.s1308_positive_checked⟩
def e1309 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,false,false,true,true,false,true,true,false], .inc 6⟩, .inc 6 (some 1310), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,false,false,true,true,false,true,true,false] 6 (some 1310) 0 408 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1309_plain_checked⟩
def e1310 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,false,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 1308), implements_jump PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,false,false,true,true,false,true,true,true] (some 1308) 0 109 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1310_plain_checked⟩
def e1311 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,false,false,true,true,true], .continueTo 3⟩, .jump (some 1304), implements_jump PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,false,false,true,true,true] (some 1304) 0 100 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1311_plain_checked⟩
def e1312 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,false,true,false], .dec 7⟩, .dec 7 (some 1315) (some 1313), implements_dec PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,false,true,false] 7 (some 1315) (some 1313) 0 1 347 350 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1312_zero_checked PA213.RuntimeShards.S026.s1312_positive_checked⟩
def e1313 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,false], .inc 2⟩, .inc 2 (some 1314), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,false] 2 (some 1314) 0 363 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1313_plain_checked⟩
def e1314 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true], .continueTo 2⟩, .jump (some 1312), implements_jump PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,false,true,true,true] (some 1312) 0 94 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1314_plain_checked⟩
def e1315 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,false,false,false], .dec 1⟩, .dec 1 (some 1319) (some 1316), implements_dec PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,false,false,false] 1 (some 1319) (some 1316) 0 1 344 350 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1315_zero_checked PA213.RuntimeShards.S026.s1315_positive_checked⟩
def e1316 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,false,false,true,false], .inc 7⟩, .inc 7 (some 1317), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,false,false,true,false] 7 (some 1317) 0 363 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1316_plain_checked⟩
def e1317 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,false,false,true,true,false], .inc 6⟩, .inc 6 (some 1318), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,false,false,true,true,false] 6 (some 1318) 0 390 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1317_plain_checked⟩
def e1318 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,false,false,true,true,true], .continueTo 3⟩, .jump (some 1315), implements_jump PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,false,false,true,true,true] (some 1315) 0 103 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1318_plain_checked⟩
def e1319 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,false,true,false], .dec 6⟩, .dec 6 (some 1325) (some 1320), implements_dec PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,false,true,false] 6 (some 1325) (some 1320) 0 1 365 368 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1319_zero_checked PA213.RuntimeShards.S026.s1319_positive_checked⟩
def e1320 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,false,true,true,false,false], .inc 7⟩, .inc 7 (some 1321), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,false,true,true,false,false] 7 (some 1321) 0 363 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1320_plain_checked⟩
def e1321 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 1324) (some 1322), implements_dec PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,false,true,true,false,true,false] 6 (some 1324) (some 1322) 0 1 383 386 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1321_zero_checked PA213.RuntimeShards.S026.s1321_positive_checked⟩
def e1322 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,false,true,true,false,true,true,false], .inc 1⟩, .inc 1 (some 1323), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,false,true,true,false,true,true,false] 1 (some 1323) 0 381 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1322_plain_checked⟩
def e1323 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,false,true,true,false,true,true,true], .continueTo 2⟩, .jump (some 1321), implements_jump PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,false,true,true,false,true,true,true] (some 1321) 0 103 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1323_plain_checked⟩
def e1324 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,false,true,true,true], .continueTo 3⟩, .jump (some 1315), implements_jump PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,false,true,true,true] (some 1315) 0 106 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1324_plain_checked⟩
def e1325 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,true,false], .dec 7⟩, .dec 7 (some 1331) (some 1326), implements_dec PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,true,false] 7 (some 1331) (some 1326) 0 1 350 350 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1325_zero_checked PA213.RuntimeShards.S026.s1325_positive_checked⟩
def e1326 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,false], .inc 1⟩, .inc 1 (some 1327), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,false] 1 (some 1327) 0 363 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1326_plain_checked⟩
def e1327 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true], .inc 1⟩, .inc 1 (some 1328), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,true,true,false,false,true] 1 (some 1328) 0 366 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S026.s1327_plain_checked⟩
def e1328 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,true,true,false,true,false], .inc 1⟩, .inc 1 (some 1329), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,true,true,false,true,false] 1 (some 1329) 0 363 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S027.s1328_plain_checked⟩
def e1329 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,true,true,false,true,true], .inc 1⟩, .inc 1 (some 1330), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,true,true,false,true,true] 1 (some 1330) 0 369 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S027.s1329_plain_checked⟩
def e1330 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,true,true,true], .continueTo 2⟩, .jump (some 1325), implements_jump PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,false,true,true,true,true] (some 1325) 0 91 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S027.s1330_plain_checked⟩
def e1331 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,true], .inc 1⟩, .inc 1 (some 1332), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,false,true,true,true,true,true] 1 (some 1332) 0 333 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S027.s1331_plain_checked⟩
def e1332 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,true,false,false,false,false,false,false], .dec 1⟩, .dec 1 (some 1335) (some 1333), implements_dec PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,true,false,false,false,false,false,false] 1 (some 1335) (some 1333) 0 1 326 332 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S027.s1332_zero_checked PA213.RuntimeShards.S027.s1332_positive_checked⟩
def e1333 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,true,false,false,false,false,false,true,false], .inc 6⟩, .inc 6 (some 1334), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,true,false,false,false,false,false,true,false] 6 (some 1334) 0 345 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S027.s1333_plain_checked⟩
def e1334 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,true,false,false,false,false,false,true,true], .continueTo 2⟩, .jump (some 1332), implements_jump PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,true,false,false,false,false,false,true,true] (some 1332) 0 88 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S027.s1334_plain_checked⟩
def e1335 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,true,false,false,false,false,true,false,false], .dec 2⟩, .dec 2 (some 1338) (some 1336), implements_dec PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,true,false,false,false,false,true,false,false] 2 (some 1338) (some 1336) 0 1 347 353 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S027.s1335_zero_checked PA213.RuntimeShards.S027.s1335_positive_checked⟩
def e1336 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,true,false,false,false,false,true,false,true,false], .inc 1⟩, .inc 1 (some 1337), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,true,false,false,false,false,true,false,true,false] 1 (some 1337) 0 345 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S027.s1336_plain_checked⟩
def e1337 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,true,false,false,false,false,true,false,true,true], .continueTo 2⟩, .jump (some 1335), implements_jump PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,true,false,false,false,false,true,false,true,true] (some 1335) 0 91 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S027.s1337_plain_checked⟩
def e1338 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,true,false,false,false,false,true,true,false,false,false], .dec 1⟩, .dec 1 (some 1342) (some 1339), implements_dec PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,true,false,false,false,false,true,true,false,false,false] 1 (some 1342) (some 1339) 0 1 353 359 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S027.s1338_zero_checked PA213.RuntimeShards.S027.s1338_positive_checked⟩
def e1339 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,true,false,false,false,false,true,true,false,false,true,false], .inc 7⟩, .inc 7 (some 1340), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,true,false,false,false,false,true,true,false,false,true,false] 7 (some 1340) 0 372 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S027.s1339_plain_checked⟩
def e1340 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,true,false,false,false,false,true,true,false,false,true,true,false], .inc 6⟩, .inc 6 (some 1341), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,true,false,false,false,false,true,true,false,false,true,true,false] 6 (some 1341) 0 399 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S027.s1340_plain_checked⟩
def e1341 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,true,false,false,false,false,true,true,false,false,true,true,true], .continueTo 3⟩, .jump (some 1338), implements_jump PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,true,false,false,false,false,true,true,false,false,true,true,true] (some 1338) 0 106 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S027.s1341_plain_checked⟩
def e1342 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,true,false,false,false,false,true,true,false,true,false], .dec 6⟩, .dec 6 (some 1348) (some 1343), implements_dec PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,true,false,false,false,false,true,true,false,true,false] 6 (some 1348) (some 1343) 0 1 374 377 (by decide) (by decide) (PA213.FastPaths.path_short _) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S027.s1342_zero_checked PA213.RuntimeShards.S027.s1342_positive_checked⟩
def e1343 : Entry PA213.FastPaths.path 3947 :=
  ⟨⟨[true,false,true,false,false,true,true,true,false,true,false,true,false,false,false,false,true,true,false,true,true,false,false], .inc 7⟩, .inc 7 (some 1344), implements_inc PA213.FastPaths.path 3947 [true,false,true,false,false,true,true,true,false,true,false,true,false,false,false,false,true,true,false,true,true,false,false] 7 (some 1344) 0 372 (by decide) (PA213.FastPaths.path_short _) PA213.RuntimeShards.S027.s1343_plain_checked⟩
def entries : Array (Entry PA213.FastPaths.path 3947) := #[
  e1280,
  e1281,
  e1282,
  e1283,
  e1284,
  e1285,
  e1286,
  e1287,
  e1288,
  e1289,
  e1290,
  e1291,
  e1292,
  e1293,
  e1294,
  e1295,
  e1296,
  e1297,
  e1298,
  e1299,
  e1300,
  e1301,
  e1302,
  e1303,
  e1304,
  e1305,
  e1306,
  e1307,
  e1308,
  e1309,
  e1310,
  e1311,
  e1312,
  e1313,
  e1314,
  e1315,
  e1316,
  e1317,
  e1318,
  e1319,
  e1320,
  e1321,
  e1322,
  e1323,
  e1324,
  e1325,
  e1326,
  e1327,
  e1328,
  e1329,
  e1330,
  e1331,
  e1332,
  e1333,
  e1334,
  e1335,
  e1336,
  e1337,
  e1338,
  e1339,
  e1340,
  e1341,
  e1342,
  e1343
]
theorem sites_block : entries.toList.map (·.site) =
    (sites.toList.drop 1280).take 64 := by decide +kernel
theorem codes_block : entries.toList.map (·.code) =
    (codes.toList.drop 1280).take 64 := by decide +kernel
end PA213.CoverageShards.S020
