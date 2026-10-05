import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk3Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 16; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected,
    Slot2.Left7.expected,
    Slot2.Left8.expected,
    Slot2.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 61, numerator := 19890835904304857795788800 }, { target := 62, numerator := 1672605311556175986792857600 }, { target := 67, numerator := 1672604908033649374396416000 }, { target := 75, numerator := 19891239426831470192230400 }, { target := 132, numerator := 398612351522269350227607552 }, { target := 133, numerator := 33519010443585766775328866304 }, { target := 138, numerator := 33519002356994333462904176640 }, { target := 146, numerator := 398620438113702662652297216 }, { target := 177, numerator := 669127719820815416250335232 }, { target := 178, numerator := 56266442680749760195711729664 }, { target := 183, numerator := 56266429106251964954695434240 }, { target := 191, numerator := 669141294318610657266630656 }, { target := 203, numerator := 642076182990960809648062464 }, { target := 204, numerator := 53991699457033360853673443328 }, { target := 209, numerator := 53991686431326201805516308480 }, { target := 217, numerator := 642089208698119857805197312 }, { target := 219, numerator := 90143519797555728786391040 }, { target := 220, numerator := 13313726135512784167386480640 }, { target := 222, numerator := 138766740943798931975412121600 }, { target := 230, numerator := 13313726135512784167386480640 }, { target := 237, numerator := 90143519797555728786391040 }, { target := 272, numerator := 19890835904304857795788800 }, { target := 273, numerator := 1672605311556175986792857600 }, { target := 278, numerator := 1672604908033649374396416000 }, { target := 286, numerator := 19891239426831470192230400 }, { target := 317, numerator := 642076182990960809648062464 }, { target := 318, numerator := 53991699457033360853673443328 }, { target := 323, numerator := 53991686431326201805516308480 }, { target := 331, numerator := 642089208698119857805197312 }, { target := 343, numerator := 428846422096812734077206528 }, { target := 344, numerator := 36061370517151154275254009856 }, { target := 349, numerator := 36061361817205480511986728960 }, { target := 357, numerator := 428855122042486497344487424 }, { target := 359, numerator := 82392862020569628741206016 }, { target := 360, numerator := 12168994542552806463274745856 }, { target := 362, numerator := 126835394993490986422386032640 }, { target := 370, numerator := 12168994542552806463274745856 }, { target := 377, numerator := 82392862020569628741206016 }, { target := 392, numerator := 20686469340477052107620352 }, { target := 393, numerator := 1739509524018423026264571904 }, { target := 398, numerator := 1739509104354995349372272640 }, { target := 406, numerator := 20686889003904728999919616 }, { target := 418, numerator := 398612351522269350227607552 }, { target := 419, numerator := 33519010443585766775328866304 }, { target := 424, numerator := 33519002356994333462904176640 }, { target := 432, numerator := 398620438113702662652297216 }, { target := 434, numerator := 90143519797555728786391040 }, { target := 435, numerator := 13313726135512784167386480640 }, { target := 437, numerator := 138766740943798931975412121600 }, { target := 445, numerator := 13313726135512784167386480640 }, { target := 452, numerator := 90143519797555728786391040 }, { target := 453, numerator := 19095202468132663483957248 }, { target := 454, numerator := 1605701099093928947321143296 }, { target := 459, numerator := 1605700711712303399420559360 }, { target := 467, numerator := 19095589849758211384541184 }, { target := 469, numerator := 82392862020569628741206016 }, { target := 470, numerator := 12168994542552806463274745856 }, { target := 472, numerator := 126835394993490986422386032640 }, { target := 480, numerator := 12168994542552806463274745856 }, { target := 487, numerator := 82392862020569628741206016 }, { target := 488, numerator := 9573672460187563220306755584 }, { target := 490, numerator := 346953058854001955950641020928 }, { target := 493, numerator := 346953186357896993431061790720 }, { target := 500, numerator := 9573544956292525739885985792 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk0

namespace RouteChunk1

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot3.Left4.expected,
    Slot3.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 17, numerator := 15371302901740695170580480 }, { target := 18, numerator := 367919572680374058599055360 }, { target := 19, numerator := 275195906789228574828134400 }, { target := 20, numerator := 319326421571645409350123520 }, { target := 21, numerator := 15371302901740695170580480 }, { target := 22, numerator := 318830573090944096602685440 }, { target := 23, numerator := 320318118533048034844999680 }, { target := 24, numerator := 15371302901740695170580480 }, { target := 25, numerator := 367919572680374058599055360 }, { target := 26, numerator := 15371302901740695170580480 }, { target := 37, numerator := 15810482984647572175454208 }, { target := 38, numerator := 378431560471241888844742656 }, { target := 39, numerator := 283058646983206534108938240 }, { target := 40, numerator := 328450033616549563902984192 }, { target := 41, numerator := 15810482984647572175454208 }, { target := 42, numerator := 327940018036399642219905024 }, { target := 43, numerator := 329470064776849407269142528 }, { target := 44, numerator := 15810482984647572175454208 }, { target := 45, numerator := 378431560471241888844742656 }, { target := 46, numerator := 15810482984647572175454208 }, { target := 51, numerator := 15371302901740695170580480 }, { target := 52, numerator := 367919572680374058599055360 }, { target := 53, numerator := 275195906789228574828134400 }, { target := 54, numerator := 319326421571645409350123520 }, { target := 55, numerator := 15371302901740695170580480 }, { target := 56, numerator := 318830573090944096602685440 }, { target := 57, numerator := 320318118533048034844999680 }, { target := 58, numerator := 15371302901740695170580480 }, { target := 59, numerator := 367919572680374058599055360 }, { target := 60, numerator := 15371302901740695170580480 }, { target := 88, numerator := 13614582570113187151085568 }, { target := 89, numerator := 325871621516902737616306176 }, { target := 90, numerator := 243744946013316737704919040 }, { target := 91, numerator := 282831973392028791138680832 }, { target := 92, numerator := 13614582570113187151085568 }, { target := 93, numerator := 282392793309121914133807104 }, { target := 94, numerator := 283710333557842545148428288 }, { target := 95, numerator := 13614582570113187151085568 }, { target := 96, numerator := 325871621516902737616306176 }, { target := 97, numerator := 13614582570113187151085568 }, { target := 108, numerator := 637250300297878534071779328 }, { target := 109, numerator := 15252894284549221686492266496 }, { target := 110, numerator := 11408836021462018916446371840 }, { target := 111, numerator := 13238361077155928256200835072 }, { target := 112, numerator := 637250300297878534071779328 }, { target := 113, numerator := 13217804615855996690585616384 }, { target := 114, numerator := 13279473999755791387431272448 }, { target := 115, numerator := 637250300297878534071779328 }, { target := 116, numerator := 15252894284549221686492266496 }, { target := 117, numerator := 637250300297878534071779328 }, { target := 122, numerator := 173476132748216416925122560 }, { target := 123, numerator := 4152235177392792947046481920 }, { target := 124, numerator := 3105782376621293915917516800 }, { target := 125, numerator := 3603826757737141048379965440 }, { target := 126, numerator := 173476132748216416925122560 }, { target := 127, numerator := 3598230753454940518801735680 }, { target := 128, numerator := 3615018766301542107536424960 }, { target := 129, numerator := 173476132748216416925122560 }, { target := 130, numerator := 4152235177392792947046481920 }, { target := 131, numerator := 173476132748216416925122560 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk1

namespace RouteChunk2

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot3.Left6.expected,
    Slot3.Left7.expected,
    Slot3.Left8.expected,
    Slot3.Left9.expected,
    Slot3.Left10.expected,
    Slot3.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 153, numerator := 15810482984647572175454208 }, { target := 154, numerator := 378431560471241888844742656 }, { target := 155, numerator := 283058646983206534108938240 }, { target := 156, numerator := 328450033616549563902984192 }, { target := 157, numerator := 15810482984647572175454208 }, { target := 158, numerator := 327940018036399642219905024 }, { target := 159, numerator := 329470064776849407269142528 }, { target := 160, numerator := 15810482984647572175454208 }, { target := 161, numerator := 378431560471241888844742656 }, { target := 162, numerator := 15810482984647572175454208 }, { target := 167, numerator := 637250300297878534071779328 }, { target := 168, numerator := 15252894284549221686492266496 }, { target := 169, numerator := 11408836021462018916446371840 }, { target := 170, numerator := 13238361077155928256200835072 }, { target := 171, numerator := 637250300297878534071779328 }, { target := 172, numerator := 13217804615855996690585616384 }, { target := 173, numerator := 13279473999755791387431272448 }, { target := 174, numerator := 637250300297878534071779328 }, { target := 175, numerator := 15252894284549221686492266496 }, { target := 176, numerator := 637250300297878534071779328 }, { target := 193, numerator := 15371302901740695170580480 }, { target := 194, numerator := 367919572680374058599055360 }, { target := 195, numerator := 275195906789228574828134400 }, { target := 196, numerator := 319326421571645409350123520 }, { target := 197, numerator := 15371302901740695170580480 }, { target := 198, numerator := 318830573090944096602685440 }, { target := 199, numerator := 320318118533048034844999680 }, { target := 200, numerator := 15371302901740695170580480 }, { target := 201, numerator := 367919572680374058599055360 }, { target := 202, numerator := 15371302901740695170580480 }, { target := 248, numerator := 15371302901740695170580480 }, { target := 249, numerator := 367919572680374058599055360 }, { target := 250, numerator := 275195906789228574828134400 }, { target := 251, numerator := 319326421571645409350123520 }, { target := 252, numerator := 15371302901740695170580480 }, { target := 253, numerator := 318830573090944096602685440 }, { target := 254, numerator := 320318118533048034844999680 }, { target := 255, numerator := 15371302901740695170580480 }, { target := 256, numerator := 367919572680374058599055360 }, { target := 257, numerator := 15371302901740695170580480 }, { target := 262, numerator := 13175402487206310146211840 }, { target := 263, numerator := 315359633726034907370618880 }, { target := 264, numerator := 235882205819338778424115200 }, { target := 265, numerator := 273708361347124636585820160 }, { target := 266, numerator := 13175402487206310146211840 }, { target := 267, numerator := 273283348363666368516587520 }, { target := 268, numerator := 274558387314041172724285440 }, { target := 269, numerator := 13175402487206310146211840 }, { target := 270, numerator := 315359633726034907370618880 }, { target := 271, numerator := 13175402487206310146211840 }, { target := 293, numerator := 15371302901740695170580480 }, { target := 294, numerator := 367919572680374058599055360 }, { target := 295, numerator := 275195906789228574828134400 }, { target := 296, numerator := 319326421571645409350123520 }, { target := 297, numerator := 15371302901740695170580480 }, { target := 298, numerator := 318830573090944096602685440 }, { target := 299, numerator := 320318118533048034844999680 }, { target := 300, numerator := 15371302901740695170580480 }, { target := 301, numerator := 367919572680374058599055360 }, { target := 302, numerator := 15371302901740695170580480 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk2

namespace RouteChunk3

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot3.Left12.expected,
    Slot3.Left13.expected,
    Slot3.Left14.expected,
    Slot3.Left15.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected,
    Slot5.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 61, numerator := 360073141071955845898567680 }, { target := 62, numerator := 30148612599863728054424567808 }, { target := 67, numerator := 30148623510619984969403990016 }, { target := 75, numerator := 360062230315698930919145472 }, { target := 219, numerator := 59043748135319174106841088 }, { target := 220, numerator := 6190630502624026694602719232 }, { target := 222, numerator := 66728809290379162986479616000 }, { target := 230, numerator := 6190635224990509564247932928 }, { target := 237, numerator := 59043748135319174106841088 }, { target := 307, numerator := 173476132748216416925122560 }, { target := 308, numerator := 4152235177392792947046481920 }, { target := 309, numerator := 3105782376621293915917516800 }, { target := 310, numerator := 3603826757737141048379965440 }, { target := 311, numerator := 173476132748216416925122560 }, { target := 312, numerator := 3598230753454940518801735680 }, { target := 313, numerator := 3615018766301542107536424960 }, { target := 314, numerator := 173476132748216416925122560 }, { target := 315, numerator := 4152235177392792947046481920 }, { target := 316, numerator := 173476132748216416925122560 }, { target := 333, numerator := 13175402487206310146211840 }, { target := 334, numerator := 315359633726034907370618880 }, { target := 335, numerator := 235882205819338778424115200 }, { target := 336, numerator := 273708361347124636585820160 }, { target := 337, numerator := 13175402487206310146211840 }, { target := 338, numerator := 273283348363666368516587520 }, { target := 339, numerator := 274558387314041172724285440 }, { target := 340, numerator := 13175402487206310146211840 }, { target := 341, numerator := 315359633726034907370618880 }, { target := 342, numerator := 13175402487206310146211840 }, { target := 359, numerator := 59043748135319174106841088 }, { target := 360, numerator := 6190630502624026694602719232 }, { target := 362, numerator := 66728809290379162986479616000 }, { target := 370, numerator := 6190635224990509564247932928 }, { target := 377, numerator := 59043748135319174106841088 }, { target := 382, numerator := 15371302901740695170580480 }, { target := 383, numerator := 367919572680374058599055360 }, { target := 384, numerator := 275195906789228574828134400 }, { target := 385, numerator := 319326421571645409350123520 }, { target := 386, numerator := 15371302901740695170580480 }, { target := 387, numerator := 318830573090944096602685440 }, { target := 388, numerator := 320318118533048034844999680 }, { target := 389, numerator := 15371302901740695170580480 }, { target := 390, numerator := 367919572680374058599055360 }, { target := 391, numerator := 15371302901740695170580480 }, { target := 408, numerator := 13614582570113187151085568 }, { target := 409, numerator := 325871621516902737616306176 }, { target := 410, numerator := 243744946013316737704919040 }, { target := 411, numerator := 282831973392028791138680832 }, { target := 412, numerator := 13614582570113187151085568 }, { target := 413, numerator := 282392793309121914133807104 }, { target := 414, numerator := 283710333557842545148428288 }, { target := 415, numerator := 13614582570113187151085568 }, { target := 416, numerator := 325871621516902737616306176 }, { target := 417, numerator := 13614582570113187151085568 }, { target := 434, numerator := 59043748135319174106841088 }, { target := 435, numerator := 6190630502624026694602719232 }, { target := 437, numerator := 66728809290379162986479616000 }, { target := 445, numerator := 6190635224990509564247932928 }, { target := 452, numerator := 59043748135319174106841088 }, { target := 469, numerator := 59043748135319174106841088 }, { target := 470, numerator := 6190630502624026694602719232 }, { target := 472, numerator := 66728809290379162986479616000 }, { target := 480, numerator := 6190635224990509564247932928 }, { target := 487, numerator := 59043748135319174106841088 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk3

namespace RouteChunk4

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot5.Left2.expected,
    Slot5.Left7.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left6.expected,
    Slot6.Left14.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot8.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 2, numerator := 59043748135319174106841088 }, { target := 3, numerator := 59043748135319174106841088 }, { target := 4, numerator := 59043748135319174106841088 }, { target := 5, numerator := 59043748135319174106841088 }, { target := 8, numerator := 6190630502624026694602719232 }, { target := 9, numerator := 6190630502624026694602719232 }, { target := 10, numerator := 6190630502624026694602719232 }, { target := 11, numerator := 6190630502624026694602719232 }, { target := 17, numerator := 360073141071955845898567680 }, { target := 19, numerator := 3487694760584671327640616960 }, { target := 24, numerator := 360073141071955845898567680 }, { target := 28, numerator := 66728809290379162986479616000 }, { target := 29, numerator := 66728809290379162986479616000 }, { target := 30, numerator := 66728809290379162986479616000 }, { target := 31, numerator := 66728809290379162986479616000 }, { target := 37, numerator := 30148612599863728054424567808 }, { target := 39, numerator := 292021665071733480042660888576 }, { target := 44, numerator := 30148612599863728054424567808 }, { target := 61, numerator := 15371302901740695170580480 }, { target := 62, numerator := 15810482984647572175454208 }, { target := 63, numerator := 15371302901740695170580480 }, { target := 64, numerator := 13614582570113187151085568 }, { target := 65, numerator := 637250300297878534071779328 }, { target := 66, numerator := 173476132748216416925122560 }, { target := 67, numerator := 15810482984647572175454208 }, { target := 68, numerator := 637250300297878534071779328 }, { target := 69, numerator := 15371302901740695170580480 }, { target := 70, numerator := 15371302901740695170580480 }, { target := 71, numerator := 13175402487206310146211840 }, { target := 72, numerator := 15371302901740695170580480 }, { target := 73, numerator := 173476132748216416925122560 }, { target := 74, numerator := 13175402487206310146211840 }, { target := 75, numerator := 15371302901740695170580480 }, { target := 76, numerator := 13614582570113187151085568 }, { target := 149, numerator := 6190635224990509564247932928 }, { target := 150, numerator := 6190635224990509564247932928 }, { target := 151, numerator := 6190635224990509564247932928 }, { target := 152, numerator := 6190635224990509564247932928 }, { target := 153, numerator := 30148623510619984969403990016 }, { target := 155, numerator := 292021770754116003693122813952 }, { target := 160, numerator := 30148623510619984969403990016 }, { target := 177, numerator := 3487694760584671327640616960 }, { target := 178, numerator := 292021665071733480042660888576 }, { target := 183, numerator := 292021770754116003693122813952 }, { target := 191, numerator := 3487589078202147677178691584 }, { target := 378, numerator := 59043748135319174106841088 }, { target := 379, numerator := 59043748135319174106841088 }, { target := 380, numerator := 59043748135319174106841088 }, { target := 381, numerator := 59043748135319174106841088 }, { target := 382, numerator := 360062230315698930919145472 }, { target := 384, numerator := 3487589078202147677178691584 }, { target := 389, numerator := 360062230315698930919145472 }, { target := 392, numerator := 360073141071955845898567680 }, { target := 393, numerator := 30148612599863728054424567808 }, { target := 398, numerator := 30148623510619984969403990016 }, { target := 406, numerator := 360062230315698930919145472 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk4

namespace RouteChunk5

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left1.expected,
    Slot8.Left2.expected,
    Slot8.Left3.expected,
    Slot8.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 132, numerator := 367919572680374058599055360 }, { target := 133, numerator := 378431560471241888844742656 }, { target := 134, numerator := 367919572680374058599055360 }, { target := 135, numerator := 325871621516902737616306176 }, { target := 136, numerator := 15252894284549221686492266496 }, { target := 137, numerator := 4152235177392792947046481920 }, { target := 138, numerator := 378431560471241888844742656 }, { target := 139, numerator := 15252894284549221686492266496 }, { target := 140, numerator := 367919572680374058599055360 }, { target := 141, numerator := 367919572680374058599055360 }, { target := 142, numerator := 315359633726034907370618880 }, { target := 143, numerator := 367919572680374058599055360 }, { target := 144, numerator := 4152235177392792947046481920 }, { target := 145, numerator := 315359633726034907370618880 }, { target := 146, numerator := 367919572680374058599055360 }, { target := 147, numerator := 325871621516902737616306176 }, { target := 177, numerator := 275195906789228574828134400 }, { target := 178, numerator := 283058646983206534108938240 }, { target := 179, numerator := 275195906789228574828134400 }, { target := 180, numerator := 243744946013316737704919040 }, { target := 181, numerator := 11408836021462018916446371840 }, { target := 182, numerator := 3105782376621293915917516800 }, { target := 183, numerator := 283058646983206534108938240 }, { target := 184, numerator := 11408836021462018916446371840 }, { target := 185, numerator := 275195906789228574828134400 }, { target := 186, numerator := 275195906789228574828134400 }, { target := 187, numerator := 235882205819338778424115200 }, { target := 188, numerator := 275195906789228574828134400 }, { target := 189, numerator := 3105782376621293915917516800 }, { target := 190, numerator := 235882205819338778424115200 }, { target := 191, numerator := 275195906789228574828134400 }, { target := 192, numerator := 243744946013316737704919040 }, { target := 203, numerator := 319326421571645409350123520 }, { target := 204, numerator := 328450033616549563902984192 }, { target := 205, numerator := 319326421571645409350123520 }, { target := 206, numerator := 282831973392028791138680832 }, { target := 207, numerator := 13238361077155928256200835072 }, { target := 208, numerator := 3603826757737141048379965440 }, { target := 209, numerator := 328450033616549563902984192 }, { target := 210, numerator := 13238361077155928256200835072 }, { target := 211, numerator := 319326421571645409350123520 }, { target := 212, numerator := 319326421571645409350123520 }, { target := 213, numerator := 273708361347124636585820160 }, { target := 214, numerator := 319326421571645409350123520 }, { target := 215, numerator := 3603826757737141048379965440 }, { target := 216, numerator := 273708361347124636585820160 }, { target := 217, numerator := 319326421571645409350123520 }, { target := 218, numerator := 282831973392028791138680832 }, { target := 272, numerator := 15371302901740695170580480 }, { target := 273, numerator := 15810482984647572175454208 }, { target := 274, numerator := 15371302901740695170580480 }, { target := 275, numerator := 13614582570113187151085568 }, { target := 276, numerator := 637250300297878534071779328 }, { target := 277, numerator := 173476132748216416925122560 }, { target := 278, numerator := 15810482984647572175454208 }, { target := 279, numerator := 637250300297878534071779328 }, { target := 280, numerator := 15371302901740695170580480 }, { target := 281, numerator := 15371302901740695170580480 }, { target := 282, numerator := 13175402487206310146211840 }, { target := 283, numerator := 15371302901740695170580480 }, { target := 284, numerator := 173476132748216416925122560 }, { target := 285, numerator := 13175402487206310146211840 }, { target := 286, numerator := 15371302901740695170580480 }, { target := 287, numerator := 13614582570113187151085568 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk5

namespace RouteChunk6

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left5.expected,
    Slot8.Left6.expected,
    Slot8.Left7.expected,
    Slot8.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 317, numerator := 318830573090944096602685440 }, { target := 318, numerator := 327940018036399642219905024 }, { target := 319, numerator := 318830573090944096602685440 }, { target := 320, numerator := 282392793309121914133807104 }, { target := 321, numerator := 13217804615855996690585616384 }, { target := 322, numerator := 3598230753454940518801735680 }, { target := 323, numerator := 327940018036399642219905024 }, { target := 324, numerator := 13217804615855996690585616384 }, { target := 325, numerator := 318830573090944096602685440 }, { target := 326, numerator := 318830573090944096602685440 }, { target := 327, numerator := 273283348363666368516587520 }, { target := 328, numerator := 318830573090944096602685440 }, { target := 329, numerator := 3598230753454940518801735680 }, { target := 330, numerator := 273283348363666368516587520 }, { target := 331, numerator := 318830573090944096602685440 }, { target := 332, numerator := 282392793309121914133807104 }, { target := 343, numerator := 320318118533048034844999680 }, { target := 344, numerator := 329470064776849407269142528 }, { target := 345, numerator := 320318118533048034844999680 }, { target := 346, numerator := 283710333557842545148428288 }, { target := 347, numerator := 13279473999755791387431272448 }, { target := 348, numerator := 3615018766301542107536424960 }, { target := 349, numerator := 329470064776849407269142528 }, { target := 350, numerator := 13279473999755791387431272448 }, { target := 351, numerator := 320318118533048034844999680 }, { target := 352, numerator := 320318118533048034844999680 }, { target := 353, numerator := 274558387314041172724285440 }, { target := 354, numerator := 320318118533048034844999680 }, { target := 355, numerator := 3615018766301542107536424960 }, { target := 356, numerator := 274558387314041172724285440 }, { target := 357, numerator := 320318118533048034844999680 }, { target := 358, numerator := 283710333557842545148428288 }, { target := 392, numerator := 15371302901740695170580480 }, { target := 393, numerator := 15810482984647572175454208 }, { target := 394, numerator := 15371302901740695170580480 }, { target := 395, numerator := 13614582570113187151085568 }, { target := 396, numerator := 637250300297878534071779328 }, { target := 397, numerator := 173476132748216416925122560 }, { target := 398, numerator := 15810482984647572175454208 }, { target := 399, numerator := 637250300297878534071779328 }, { target := 400, numerator := 15371302901740695170580480 }, { target := 401, numerator := 15371302901740695170580480 }, { target := 402, numerator := 13175402487206310146211840 }, { target := 403, numerator := 15371302901740695170580480 }, { target := 404, numerator := 173476132748216416925122560 }, { target := 405, numerator := 13175402487206310146211840 }, { target := 406, numerator := 15371302901740695170580480 }, { target := 407, numerator := 13614582570113187151085568 }, { target := 418, numerator := 367919572680374058599055360 }, { target := 419, numerator := 378431560471241888844742656 }, { target := 420, numerator := 367919572680374058599055360 }, { target := 421, numerator := 325871621516902737616306176 }, { target := 422, numerator := 15252894284549221686492266496 }, { target := 423, numerator := 4152235177392792947046481920 }, { target := 424, numerator := 378431560471241888844742656 }, { target := 425, numerator := 15252894284549221686492266496 }, { target := 426, numerator := 367919572680374058599055360 }, { target := 427, numerator := 367919572680374058599055360 }, { target := 428, numerator := 315359633726034907370618880 }, { target := 429, numerator := 367919572680374058599055360 }, { target := 430, numerator := 4152235177392792947046481920 }, { target := 431, numerator := 315359633726034907370618880 }, { target := 432, numerator := 367919572680374058599055360 }, { target := 433, numerator := 325871621516902737616306176 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk6

namespace RouteChunk7

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left9.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left6.expected,
    Slot9.Left14.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 2, numerator := 90143519797555728786391040 }, { target := 3, numerator := 82392862020569628741206016 }, { target := 4, numerator := 90143519797555728786391040 }, { target := 5, numerator := 82392862020569628741206016 }, { target := 8, numerator := 13313726135512784167386480640 }, { target := 9, numerator := 12168994542552806463274745856 }, { target := 10, numerator := 13313726135512784167386480640 }, { target := 11, numerator := 12168994542552806463274745856 }, { target := 17, numerator := 19890835904304857795788800 }, { target := 18, numerator := 398612351522269350227607552 }, { target := 19, numerator := 669127719820815416250335232 }, { target := 20, numerator := 642076182990960809648062464 }, { target := 21, numerator := 19890835904304857795788800 }, { target := 22, numerator := 642076182990960809648062464 }, { target := 23, numerator := 428846422096812734077206528 }, { target := 24, numerator := 20686469340477052107620352 }, { target := 25, numerator := 398612351522269350227607552 }, { target := 26, numerator := 19095202468132663483957248 }, { target := 37, numerator := 1672605311556175986792857600 }, { target := 38, numerator := 33519010443585766775328866304 }, { target := 39, numerator := 56266442680749760195711729664 }, { target := 40, numerator := 53991699457033360853673443328 }, { target := 41, numerator := 1672605311556175986792857600 }, { target := 42, numerator := 53991699457033360853673443328 }, { target := 43, numerator := 36061370517151154275254009856 }, { target := 44, numerator := 1739509524018423026264571904 }, { target := 45, numerator := 33519010443585766775328866304 }, { target := 46, numerator := 1605701099093928947321143296 }, { target := 153, numerator := 1672604908033649374396416000 }, { target := 154, numerator := 33519002356994333462904176640 }, { target := 155, numerator := 56266429106251964954695434240 }, { target := 156, numerator := 53991686431326201805516308480 }, { target := 157, numerator := 1672604908033649374396416000 }, { target := 158, numerator := 53991686431326201805516308480 }, { target := 159, numerator := 36061361817205480511986728960 }, { target := 160, numerator := 1739509104354995349372272640 }, { target := 161, numerator := 33519002356994333462904176640 }, { target := 162, numerator := 1605700711712303399420559360 }, { target := 382, numerator := 19891239426831470192230400 }, { target := 383, numerator := 398620438113702662652297216 }, { target := 384, numerator := 669141294318610657266630656 }, { target := 385, numerator := 642089208698119857805197312 }, { target := 386, numerator := 19891239426831470192230400 }, { target := 387, numerator := 642089208698119857805197312 }, { target := 388, numerator := 428855122042486497344487424 }, { target := 389, numerator := 20686889003904728999919616 }, { target := 390, numerator := 398620438113702662652297216 }, { target := 391, numerator := 19095589849758211384541184 }, { target := 453, numerator := 15371302901740695170580480 }, { target := 454, numerator := 15810482984647572175454208 }, { target := 455, numerator := 15371302901740695170580480 }, { target := 456, numerator := 13614582570113187151085568 }, { target := 457, numerator := 637250300297878534071779328 }, { target := 458, numerator := 173476132748216416925122560 }, { target := 459, numerator := 15810482984647572175454208 }, { target := 460, numerator := 637250300297878534071779328 }, { target := 461, numerator := 15371302901740695170580480 }, { target := 462, numerator := 15371302901740695170580480 }, { target := 463, numerator := 13175402487206310146211840 }, { target := 464, numerator := 15371302901740695170580480 }, { target := 465, numerator := 173476132748216416925122560 }, { target := 466, numerator := 13175402487206310146211840 }, { target := 467, numerator := 15371302901740695170580480 }, { target := 468, numerator := 13614582570113187151085568 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk7

namespace RouteChunk8

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 9573672460187563220306755584 }, { target := 6, numerator := 346953058854001955950641020928 }, { target := 27, numerator := 346953186357896993431061790720 }, { target := 28, numerator := 138766740943798931975412121600 }, { target := 29, numerator := 126835394993490986422386032640 }, { target := 30, numerator := 138766740943798931975412121600 }, { target := 31, numerator := 126835394993490986422386032640 }, { target := 148, numerator := 9573544956292525739885985792 }, { target := 149, numerator := 13313726135512784167386480640 }, { target := 150, numerator := 12168994542552806463274745856 }, { target := 151, numerator := 13313726135512784167386480640 }, { target := 152, numerator := 12168994542552806463274745856 }, { target := 378, numerator := 90143519797555728786391040 }, { target := 379, numerator := 82392862020569628741206016 }, { target := 380, numerator := 90143519797555728786391040 }, { target := 381, numerator := 82392862020569628741206016 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk8

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3.Parent2
