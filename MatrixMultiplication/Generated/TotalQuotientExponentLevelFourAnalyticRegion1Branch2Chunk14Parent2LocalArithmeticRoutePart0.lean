import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk14Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 60; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot3.Left0.expected,
    Slot3.Left2.expected,
    Slot3.Left7.expected,
    Slot4.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 250, numerator := 433196623212152279873355776 }, { target := 251, numerator := 251590724426118921053011968 }, { target := 252, numerator := 8365453588981128872029323264 }, { target := 253, numerator := 1979621752721304141969752064 }, { target := 254, numerator := 238349107351060030471274496 }, { target := 255, numerator := 8365451587509396874542972928 }, { target := 256, numerator := 238349107351060030471274496 }, { target := 257, numerator := 238349107351060030471274496 }, { target := 258, numerator := 10209286764870404638519590912 }, { target := 259, numerator := 238349107351060030471274496 }, { target := 260, numerator := 1979621752721304141969752064 }, { target := 261, numerator := 10209286764870404638519590912 }, { target := 262, numerator := 433198624683884277359706112 }, { target := 263, numerator := 238349107351060030471274496 }, { target := 264, numerator := 238349107351060030471274496 }, { target := 265, numerator := 251590724426118921053011968 }, { target := 562, numerator := 2052148332168876051182649344 }, { target := 563, numerator := 2436926144450540310779396096 }, { target := 564, numerator := 1859759426028043921384275968 }, { target := 565, numerator := 19174760978702935603237879808 }, { target := 566, numerator := 2308666873689985557580480512 }, { target := 567, numerator := 1859759426028043921384275968 }, { target := 568, numerator := 2308666873689985557580480512 }, { target := 569, numerator := 2308666873689985557580480512 }, { target := 570, numerator := 98887897756387714716363915264 }, { target := 571, numerator := 2308666873689985557580480512 }, { target := 572, numerator := 19174760978702935603237879808 }, { target := 573, numerator := 98887897756387714716363915264 }, { target := 574, numerator := 2052148332168876051182649344 }, { target := 575, numerator := 2308666873689985557580480512 }, { target := 576, numerator := 2308666873689985557580480512 }, { target := 577, numerator := 2436926144450540310779396096 }, { target := 613, numerator := 3551282166473871223498473472 }, { target := 616, numerator := 12704477476209962668800344064 }, { target := 618, numerator := 3551280985882250506087170048 }, { target := 880, numerator := 3551282166473871223498473472 }, { target := 883, numerator := 12704477476209962668800344064 }, { target := 885, numerator := 3551280985882250506087170048 }, { target := 925, numerator := 211865873200942249307799552 }, { target := 926, numerator := 251590724426118921053011968 }, { target := 927, numerator := 192003447588353913435193344 }, { target := 928, numerator := 1979621752721304141969752064 }, { target := 929, numerator := 238349107351060030471274496 }, { target := 930, numerator := 192003447588353913435193344 }, { target := 931, numerator := 238349107351060030471274496 }, { target := 932, numerator := 238349107351060030471274496 }, { target := 933, numerator := 10209286764870404638519590912 }, { target := 934, numerator := 238349107351060030471274496 }, { target := 935, numerator := 1979621752721304141969752064 }, { target := 936, numerator := 10209286764870404638519590912 }, { target := 937, numerator := 211865873200942249307799552 }, { target := 938, numerator := 238349107351060030471274496 }, { target := 939, numerator := 238349107351060030471274496 }, { target := 940, numerator := 251590724426118921053011968 }, { target := 976, numerator := 3551282166473871223498473472 }, { target := 979, numerator := 12704477476209962668800344064 }, { target := 981, numerator := 3551280985882250506087170048 }, { target := 1002, numerator := 3551282166473871223498473472 }, { target := 1005, numerator := 12704477476209962668800344064 }, { target := 1007, numerator := 3551280985882250506087170048 }]

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
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected,
    Slot4.Left4.expected,
    Slot4.Left5.expected,
    Slot4.Left6.expected,
    Slot4.Left7.expected,
    Slot4.Left8.expected,
    Slot4.Left9.expected,
    Slot5.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 121, numerator := 79563343617219431183155200 }, { target := 122, numerator := 1336664172769286443877007360 }, { target := 123, numerator := 2896105707666787295066849280 }, { target := 124, numerator := 95476012340663317419786240 }, { target := 125, numerator := 1527616197450613078716579840 }, { target := 126, numerator := 111388681064107203656417280 }, { target := 127, numerator := 2896105707666787295066849280 }, { target := 128, numerator := 2896105707666787295066849280 }, { target := 129, numerator := 1527616197450613078716579840 }, { target := 130, numerator := 35739853952854968487473315840 }, { target := 131, numerator := 2864280370219899522593587200 }, { target := 132, numerator := 1336664172769286443877007360 }, { target := 133, numerator := 2896105707666787295066849280 }, { target := 134, numerator := 111388681064107203656417280 }, { target := 135, numerator := 2864280370219899522593587200 }, { target := 136, numerator := 111388681064107203656417280 }, { target := 137, numerator := 2896105707666787295066849280 }, { target := 138, numerator := 2896105707666787295066849280 }, { target := 139, numerator := 95476012340663317419786240 }, { target := 466, numerator := 5297658597042511054182023168 }, { target := 468, numerator := 195635484029465774815382077440 }, { target := 471, numerator := 195635436123271415391676530688 }, { target := 478, numerator := 5297706503236870477887569920 }, { target := 562, numerator := 3962534395361986031093022720 }, { target := 564, numerator := 146331123499128712968378777600 }, { target := 567, numerator := 146331087666328349787574763520 }, { target := 574, numerator := 3962570228162349211897036800 }, { target := 597, numerator := 4597967838942556764007038976 }, { target := 599, numerator := 169796835195385389462407086080 }, { target := 602, numerator := 169796793616424247321077743616 }, { target := 609, numerator := 4598009417903698905336381440 }, { target := 733, numerator := 221330750011210030565556224 }, { target := 735, numerator := 8173450141392774958594129920 }, { target := 738, numerator := 8173448139921042961107779584 }, { target := 745, numerator := 221332751482942028051906560 }, { target := 829, numerator := 4590828137329291924311375872 }, { target := 831, numerator := 169533175513404977366968565760 }, { target := 834, numerator := 169533133999007439483622653952 }, { target := 841, numerator := 4590869651726829807657287680 }, { target := 864, numerator := 4612247242169086443398365184 }, { target := 866, numerator := 170324154559346213653284126720 }, { target := 869, numerator := 170324112851257862995987922944 }, { target := 876, numerator := 4612288950257437100694568960 }, { target := 925, numerator := 221330750011210030565556224 }, { target := 927, numerator := 8173450141392774958594129920 }, { target := 930, numerator := 8173448139921042961107779584 }, { target := 937, numerator := 221332751482942028051906560 }, { target := 960, numerator := 5297658597042511054182023168 }, { target := 962, numerator := 195635484029465774815382077440 }, { target := 965, numerator := 195635436123271415391676530688 }, { target := 972, numerator := 5297706503236870477887569920 }, { target := 986, numerator := 221330750011210030565556224 }, { target := 988, numerator := 8173450141392774958594129920 }, { target := 991, numerator := 8173448139921042961107779584 }, { target := 998, numerator := 221332751482942028051906560 }]

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
    Slot5.Left1.expected,
    Slot5.Left6.expected,
    Slot5.Left14.expected,
    Slot6.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 121, numerator := 101850376989054021528453120 }, { target := 122, numerator := 16260126798662820186386595840 }, { target := 124, numerator := 162251613457592411317799485440 }, { target := 132, numerator := 16260126798662820186386595840 }, { target := 139, numerator := 101838755540287584510935040 }, { target := 196, numerator := 6690421246224703947171430400 }, { target := 197, numerator := 112399076936575026312480030720 }, { target := 198, numerator := 243531333362579223677040066560 }, { target := 199, numerator := 8028505495469644736605716480 }, { target := 200, numerator := 128456087927514315785691463680 }, { target := 201, numerator := 9366589744714585526040002560 }, { target := 202, numerator := 243531333362579223677040066560 }, { target := 203, numerator := 243531333362579223677040066560 }, { target := 204, numerator := 128456087927514315785691463680 }, { target := 205, numerator := 3005337223804137013069406535680 }, { target := 206, numerator := 240855164864089342098171494400 }, { target := 207, numerator := 112399076936575026312480030720 }, { target := 208, numerator := 243531333362579223677040066560 }, { target := 209, numerator := 9366589744714585526040002560 }, { target := 210, numerator := 240855164864089342098171494400 }, { target := 211, numerator := 9366589744714585526040002560 }, { target := 212, numerator := 243531333362579223677040066560 }, { target := 213, numerator := 243531333362579223677040066560 }, { target := 214, numerator := 8028505495469644736605716480 }, { target := 508, numerator := 6690419632134597497585664000 }, { target := 509, numerator := 112399049819861237959439155200 }, { target := 510, numerator := 243531274609699348912118169600 }, { target := 511, numerator := 8028503558561516997102796800 }, { target := 512, numerator := 128456056936984271953644748800 }, { target := 513, numerator := 9366587484988436496619929600 }, { target := 514, numerator := 243531274609699348912118169600 }, { target := 515, numerator := 243531274609699348912118169600 }, { target := 516, numerator := 128456056936984271953644748800 }, { target := 517, numerator := 3005336498754861195915480268800 }, { target := 518, numerator := 240855106756845509913083904000 }, { target := 519, numerator := 112399049819861237959439155200 }, { target := 520, numerator := 243531274609699348912118169600 }, { target := 521, numerator := 9366587484988436496619929600 }, { target := 522, numerator := 240855106756845509913083904000 }, { target := 523, numerator := 9366587484988436496619929600 }, { target := 524, numerator := 243531274609699348912118169600 }, { target := 525, numerator := 243531274609699348912118169600 }, { target := 526, numerator := 8028503558561516997102796800 }, { target := 906, numerator := 79564957707325880768921600 }, { target := 907, numerator := 1336691289483074796917882880 }, { target := 908, numerator := 2896164460546662059988746240 }, { target := 909, numerator := 95477949248791056922705920 }, { target := 910, numerator := 1527647187980656910763294720 }, { target := 911, numerator := 111390940790256233076490240 }, { target := 912, numerator := 2896164460546662059988746240 }, { target := 913, numerator := 2896164460546662059988746240 }, { target := 914, numerator := 1527647187980656910763294720 }, { target := 915, numerator := 35740579002130785641399582720 }, { target := 916, numerator := 2864338477463731707681177600 }, { target := 917, numerator := 1336691289483074796917882880 }, { target := 918, numerator := 2896164460546662059988746240 }, { target := 919, numerator := 111390940790256233076490240 }, { target := 920, numerator := 2864338477463731707681177600 }, { target := 921, numerator := 111390940790256233076490240 }, { target := 922, numerator := 2896164460546662059988746240 }, { target := 923, numerator := 2896164460546662059988746240 }, { target := 924, numerator := 95477949248791056922705920 }]

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
    Slot6.Left1.expected,
    Slot6.Left2.expected,
    Slot6.Left3.expected,
    Slot6.Left4.expected,
    Slot6.Left5.expected,
    Slot6.Left6.expected,
    Slot6.Left7.expected,
    Slot6.Left8.expected,
    Slot6.Left9.expected,
    Slot6.Left10.expected,
    Slot6.Left11.expected,
    Slot6.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 196, numerator := 79216959880375350077685760 }, { target := 197, numerator := 12646765287848860144967352320 }, { target := 199, numerator := 126195699355905208802732933120 }, { target := 207, numerator := 12646765287848860144967352320 }, { target := 214, numerator := 79207920975779232397393920 }, { target := 231, numerator := 90533668434714685803069440 }, { target := 232, numerator := 14453446043255840165676974080 }, { target := 234, numerator := 144223656406748810060266209280 }, { target := 242, numerator := 14453446043255840165676974080 }, { target := 249, numerator := 90523338258033408454164480 }, { target := 337, numerator := 106377060410789755818606592 }, { target := 338, numerator := 16982799100825612194670444544 }, { target := 340, numerator := 169462796277929851820812795904 }, { target := 348, numerator := 16982799100825612194670444544 }, { target := 355, numerator := 106364922453189254933643264 }, { target := 412, numerator := 1256154649531666265517588480 }, { target := 413, numerator := 200541563850174782298768015360 }, { target := 415, numerator := 2001103232643639739586193653760 }, { target := 423, numerator := 200541563850174782298768015360 }, { target := 430, numerator := 1256011318330213542301532160 }, { target := 447, numerator := 2824650455163098197055766528 }, { target := 448, numerator := 450947516549582213169121591296 }, { target := 450, numerator := 4499778079890562873880305729536 }, { target := 458, numerator := 450947516549582213169121591296 }, { target := 465, numerator := 2824328153650642343769931776 }, { target := 508, numerator := 79216959880375350077685760 }, { target := 509, numerator := 12646765287848860144967352320 }, { target := 511, numerator := 126195699355905208802732933120 }, { target := 519, numerator := 12646765287848860144967352320 }, { target := 526, numerator := 79207920975779232397393920 }, { target := 543, numerator := 1256154649531666265517588480 }, { target := 544, numerator := 200541563850174782298768015360 }, { target := 546, numerator := 2001103232643639739586193653760 }, { target := 554, numerator := 200541563850174782298768015360 }, { target := 561, numerator := 1256011318330213542301532160 }, { target := 578, numerator := 90533668434714685803069440 }, { target := 579, numerator := 14453446043255840165676974080 }, { target := 581, numerator := 144223656406748810060266209280 }, { target := 589, numerator := 14453446043255840165676974080 }, { target := 596, numerator := 90523338258033408454164480 }, { target := 679, numerator := 88270326723846818657992704 }, { target := 680, numerator := 14092109892174444161535049728 }, { target := 682, numerator := 140618064996580089808759554048 }, { target := 690, numerator := 14092109892174444161535049728 }, { target := 697, numerator := 88260254801582573242810368 }, { target := 714, numerator := 88270326723846818657992704 }, { target := 715, numerator := 14092109892174444161535049728 }, { target := 717, numerator := 140618064996580089808759554048 }, { target := 725, numerator := 14092109892174444161535049728 }, { target := 732, numerator := 88260254801582573242810368 }, { target := 775, numerator := 88270326723846818657992704 }, { target := 776, numerator := 14092109892174444161535049728 }, { target := 778, numerator := 140618064996580089808759554048 }, { target := 786, numerator := 14092109892174444161535049728 }, { target := 793, numerator := 88260254801582573242810368 }, { target := 810, numerator := 2824650455163098197055766528 }, { target := 811, numerator := 450947516549582213169121591296 }, { target := 813, numerator := 4499778079890562873880305729536 }, { target := 821, numerator := 450947516549582213169121591296 }, { target := 828, numerator := 2824328153650642343769931776 }]

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
    Slot6.Left13.expected,
    Slot6.Left14.expected,
    Slot6.Left15.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 102305066172040869838848000 }, { target := 35, numerator := 79570607022698454319104000 }, { target := 36, numerator := 90937836597369662078976000 }, { target := 37, numerator := 106851958001909352942796800 }, { target := 38, numerator := 1261762482788504061345792000 }, { target := 39, numerator := 2837260501837933456864051200 }, { target := 40, numerator := 79570607022698454319104000 }, { target := 41, numerator := 1261762482788504061345792000 }, { target := 42, numerator := 90937836597369662078976000 }, { target := 43, numerator := 88664390682435420527001600 }, { target := 44, numerator := 88664390682435420527001600 }, { target := 45, numerator := 88664390682435420527001600 }, { target := 46, numerator := 2837260501837933456864051200 }, { target := 47, numerator := 88664390682435420527001600 }, { target := 48, numerator := 102305066172040869838848000 }, { target := 49, numerator := 106851958001909352942796800 }, { target := 79, numerator := 16332716650442564919361536000 }, { target := 80, numerator := 12703224061455328270614528000 }, { target := 81, numerator := 14517970355948946594988032000 }, { target := 82, numerator := 17058615168240012249110937600 }, { target := 83, numerator := 201436838688791634005458944000 }, { target := 84, numerator := 452960675105607133763626598400 }, { target := 85, numerator := 12703224061455328270614528000 }, { target := 86, numerator := 201436838688791634005458944000 }, { target := 87, numerator := 14517970355948946594988032000 }, { target := 88, numerator := 14155021097050222930113331200 }, { target := 89, numerator := 14155021097050222930113331200 }, { target := 90, numerator := 14155021097050222930113331200 }, { target := 91, numerator := 452960675105607133763626598400 }, { target := 92, numerator := 14155021097050222930113331200 }, { target := 93, numerator := 16332716650442564919361536000 }, { target := 94, numerator := 17058615168240012249110937600 }, { target := 154, numerator := 162975951017670948868325376000 }, { target := 155, numerator := 126759073013744071342030848000 }, { target := 156, numerator := 144867512015707510105178112000 }, { target := 157, numerator := 170219326618456324373584281600 }, { target := 158, numerator := 2010036729217941702709346304000 }, { target := 159, numerator := 4519866374890074315281557094400 }, { target := 160, numerator := 126759073013744071342030848000 }, { target := 161, numerator := 2010036729217941702709346304000 }, { target := 162, numerator := 144867512015707510105178112000 }, { target := 163, numerator := 141245824215314822352548659200 }, { target := 164, numerator := 141245824215314822352548659200 }, { target := 165, numerator := 141245824215314822352548659200 }, { target := 166, numerator := 4519866374890074315281557094400 }, { target := 167, numerator := 141245824215314822352548659200 }, { target := 168, numerator := 162975951017670948868325376000 }, { target := 169, numerator := 170219326618456324373584281600 }, { target := 845, numerator := 88270326723846818657992704 }, { target := 846, numerator := 14092109892174444161535049728 }, { target := 848, numerator := 140618064996580089808759554048 }, { target := 856, numerator := 14092109892174444161535049728 }, { target := 863, numerator := 88260254801582573242810368 }, { target := 906, numerator := 101850376989054021528453120 }, { target := 907, numerator := 16260126798662820186386595840 }, { target := 909, numerator := 162251613457592411317799485440 }, { target := 917, numerator := 16260126798662820186386595840 }, { target := 924, numerator := 101838755540287584510935040 }, { target := 941, numerator := 106377060410789755818606592 }, { target := 942, numerator := 16982799100825612194670444544 }, { target := 944, numerator := 169462796277929851820812795904 }, { target := 952, numerator := 16982799100825612194670444544 }, { target := 959, numerator := 106364922453189254933643264 }]

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
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left2.expected,
    Slot8.Left3.expected,
    Slot8.Left4.expected,
    Slot8.Left5.expected,
    Slot8.Left6.expected,
    Slot8.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 77858414825421871943516160 }, { target := 35, numerator := 6547055076662746005446328320 }, { target := 40, numerator := 6547053497160284694065971200 }, { target := 48, numerator := 77859994327883183323873280 }, { target := 79, numerator := 1308021369067087448651071488 }, { target := 80, numerator := 109990525287934132891498315776 }, { target := 85, numerator := 109990498752292782860308316160 }, { target := 93, numerator := 1308047904708437479841071104 }, { target := 105, numerator := 2834046299645356138743988224 }, { target := 106, numerator := 238312804790523954598246350848 }, { target := 111, numerator := 238312747296634362864001351680 }, { target := 119, numerator := 2834103793534947872988987392 }, { target := 154, numerator := 93430097790506246332219392 }, { target := 155, numerator := 7856466091995295206535593984 }, { target := 160, numerator := 7856464196592341632879165440 }, { target := 168, numerator := 93431993193459819988647936 }, { target := 180, numerator := 1494881564648099941315510272 }, { target := 181, numerator := 125703457471924723304569503744 }, { target := 186, numerator := 125703427145477466126066647040 }, { target := 194, numerator := 1494911891095357119818366976 }, { target := 215, numerator := 109001780755590620720922624 }, { target := 216, numerator := 9165877107327844407624859648 }, { target := 221, numerator := 9165874896024398571692359680 }, { target := 229, numerator := 109003992059036456653422592 }, { target := 295, numerator := 2834046299645356138743988224 }, { target := 296, numerator := 238312804790523954598246350848 }, { target := 301, numerator := 238312747296634362864001351680 }, { target := 309, numerator := 2834103793534947872988987392 }, { target := 321, numerator := 2834046299645356138743988224 }, { target := 322, numerator := 238312804790523954598246350848 }, { target := 327, numerator := 238312747296634362864001351680 }, { target := 335, numerator := 2834103793534947872988987392 }, { target := 492, numerator := 16332716650442564919361536000 }, { target := 493, numerator := 12703224061455328270614528000 }, { target := 494, numerator := 14517970355948946594988032000 }, { target := 495, numerator := 17058615168240012249110937600 }, { target := 496, numerator := 201436838688791634005458944000 }, { target := 497, numerator := 452960675105607133763626598400 }, { target := 498, numerator := 12703224061455328270614528000 }, { target := 499, numerator := 201436838688791634005458944000 }, { target := 500, numerator := 14517970355948946594988032000 }, { target := 501, numerator := 14155021097050222930113331200 }, { target := 502, numerator := 14155021097050222930113331200 }, { target := 503, numerator := 14155021097050222930113331200 }, { target := 504, numerator := 452960675105607133763626598400 }, { target := 505, numerator := 14155021097050222930113331200 }, { target := 506, numerator := 16332716650442564919361536000 }, { target := 507, numerator := 17058615168240012249110937600 }, { target := 890, numerator := 102293392841806725513216000 }, { target := 891, numerator := 79561527765849675399168000 }, { target := 892, numerator := 90927460303828200456192000 }, { target := 893, numerator := 106839765856998135536025600 }, { target := 894, numerator := 1261618511715616281329664000 }, { target := 895, numerator := 2836936761479439854233190400 }, { target := 896, numerator := 79561527765849675399168000 }, { target := 897, numerator := 1261618511715616281329664000 }, { target := 898, numerator := 90927460303828200456192000 }, { target := 899, numerator := 88654273796232495444787200 }, { target := 900, numerator := 88654273796232495444787200 }, { target := 901, numerator := 88654273796232495444787200 }, { target := 902, numerator := 2836936761479439854233190400 }, { target := 903, numerator := 88654273796232495444787200 }, { target := 904, numerator := 102293392841806725513216000 }, { target := 905, numerator := 106839765856998135536025600 }]

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
    Slot8.Left8.expected,
    Slot8.Left9.expected,
    Slot8.Left10.expected,
    Slot8.Left11.expected,
    Slot8.Left12.expected,
    Slot8.Left13.expected,
    Slot8.Left14.expected,
    Slot8.Left15.expected,
    Slot8.Left16.expected,
    Slot8.Left17.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 213426080367952529473929216 }, { target := 11, numerator := 5108456504290992802246950912 }, { target := 12, numerator := 3821015309813343672839700480 }, { target := 13, numerator := 4433754701837465451006787584 }, { target := 14, numerator := 213426080367952529473929216 }, { target := 15, numerator := 4426869989567531498443112448 }, { target := 16, numerator := 4447524126377333356134137856 }, { target := 17, numerator := 213426080367952529473929216 }, { target := 18, numerator := 5108456504290992802246950912 }, { target := 19, numerator := 213426080367952529473929216 }, { target := 55, numerator := 7881541207771604424358625280 }, { target := 56, numerator := 188648502456984854286261288960 }, { target := 57, numerator := 141105011945588401790936678400 }, { target := 58, numerator := 163732662509835911267321118720 }, { target := 59, numerator := 7881541207771604424358625280 }, { target := 60, numerator := 163478419245069085318148259840 }, { target := 61, numerator := 164241149039369563165666836480 }, { target := 62, numerator := 7881541207771604424358625280 }, { target := 63, numerator := 188648502456984854286261288960 }, { target := 64, numerator := 7881541207771604424358625280 }, { target := 370, numerator := 1494881564648099941315510272 }, { target := 371, numerator := 125703457471924723304569503744 }, { target := 376, numerator := 125703427145477466126066647040 }, { target := 384, numerator := 1494911891095357119818366976 }, { target := 396, numerator := 34973999939579504877027459072 }, { target := 397, numerator := 2940937140436905505646490681344 }, { target := 402, numerator := 2940936430924399884574434263040 }, { target := 410, numerator := 34974709452085125949083877376 }, { target := 431, numerator := 2802902933715187389966581760 }, { target := 432, numerator := 235693982759858856196067819520 }, { target := 437, numerator := 235693925897770248986374963200 }, { target := 445, numerator := 2802959795803794599659438080 }, { target := 492, numerator := 1308021369067087448651071488 }, { target := 493, numerator := 109990525287934132891498315776 }, { target := 498, numerator := 109990498752292782860308316160 }, { target := 506, numerator := 1308047904708437479841071104 }, { target := 527, numerator := 2834046299645356138743988224 }, { target := 528, numerator := 238312804790523954598246350848 }, { target := 533, numerator := 238312747296634362864001351680 }, { target := 541, numerator := 2834103793534947872988987392 }, { target := 637, numerator := 109001780755590620720922624 }, { target := 638, numerator := 9165877107327844407624859648 }, { target := 643, numerator := 9165874896024398571692359680 }, { target := 651, numerator := 109003992059036456653422592 }, { target := 663, numerator := 2802902933715187389966581760 }, { target := 664, numerator := 235693982759858856196067819520 }, { target := 669, numerator := 235693925897770248986374963200 }, { target := 677, numerator := 2802959795803794599659438080 }, { target := 698, numerator := 109001780755590620720922624 }, { target := 699, numerator := 9165877107327844407624859648 }, { target := 704, numerator := 9165874896024398571692359680 }, { target := 712, numerator := 109003992059036456653422592 }, { target := 759, numerator := 2834046299645356138743988224 }, { target := 760, numerator := 238312804790523954598246350848 }, { target := 765, numerator := 238312747296634362864001351680 }, { target := 773, numerator := 2834103793534947872988987392 }, { target := 794, numerator := 2834046299645356138743988224 }, { target := 795, numerator := 238312804790523954598246350848 }, { target := 800, numerator := 238312747296634362864001351680 }, { target := 808, numerator := 2834103793534947872988987392 }, { target := 890, numerator := 93430097790506246332219392 }, { target := 891, numerator := 7856466091995295206535593984 }, { target := 896, numerator := 7856464196592341632879165440 }, { target := 904, numerator := 93431993193459819988647936 }]

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
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left2.expected,
    Slot10.Left3.expected,
    Slot10.Left4.expected,
    Slot10.Left5.expected,
    Slot10.Left6.expected,
    Slot10.Left7.expected,
    Slot10.Left8.expected,
    Slot10.Left9.expected,
    Slot10.Left10.expected,
    Slot10.Left11.expected,
    Slot10.Left12.expected,
    Slot10.Left13.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 211865873200942249307799552 }, { target := 12, numerator := 2052148332168876051182649344 }, { target := 17, numerator := 211865873200942249307799552 }, { target := 24, numerator := 251590724426118921053011968 }, { target := 26, numerator := 2436926144450540310779396096 }, { target := 31, numerator := 251590724426118921053011968 }, { target := 55, numerator := 192003447588353913435193344 }, { target := 57, numerator := 1859759426028043921384275968 }, { target := 62, numerator := 192003447588353913435193344 }, { target := 69, numerator := 1979621752721304141969752064 }, { target := 71, numerator := 19174760978702935603237879808 }, { target := 76, numerator := 1979621752721304141969752064 }, { target := 95, numerator := 238349107351060030471274496 }, { target := 97, numerator := 2308666873689985557580480512 }, { target := 102, numerator := 238349107351060030471274496 }, { target := 144, numerator := 8073542725369359625931980800 }, { target := 145, numerator := 188648456261726007699116654592 }, { target := 146, numerator := 142964736818558952645117083648 }, { target := 147, numerator := 163732622415837667059610681344 }, { target := 148, numerator := 7881539277781005712496787456 }, { target := 149, numerator := 163478379213328602359207559168 }, { target := 150, numerator := 164241108820855796460416925696 }, { target := 151, numerator := 8073542725369359625931980800 }, { target := 152, numerator := 188648456261726007699116654592 }, { target := 153, numerator := 7881539277781005712496787456 }, { target := 170, numerator := 238349107351060030471274496 }, { target := 172, numerator := 2308666873689985557580480512 }, { target := 177, numerator := 238349107351060030471274496 }, { target := 271, numerator := 238349107351060030471274496 }, { target := 273, numerator := 2308666873689985557580480512 }, { target := 278, numerator := 238349107351060030471274496 }, { target := 285, numerator := 10209286764870404638519590912 }, { target := 287, numerator := 98887897756387714716363915264 }, { target := 292, numerator := 10209286764870404638519590912 }, { target := 311, numerator := 238349107351060030471274496 }, { target := 313, numerator := 2308666873689985557580480512 }, { target := 318, numerator := 238349107351060030471274496 }, { target := 360, numerator := 1979621752721304141969752064 }, { target := 362, numerator := 19174760978702935603237879808 }, { target := 367, numerator := 1979621752721304141969752064 }, { target := 386, numerator := 10209286764870404638519590912 }, { target := 388, numerator := 98887897756387714716363915264 }, { target := 393, numerator := 10209286764870404638519590912 }, { target := 482, numerator := 425293883559493490643566592 }, { target := 483, numerator := 5108502699549839389391585280 }, { target := 484, numerator := 5873198195039712791226220544 }, { target := 485, numerator := 4433794795835709658717224960 }, { target := 486, numerator := 213428010358551241335767040 }, { target := 487, numerator := 4426910021308014457383813120 }, { target := 488, numerator := 4447564344891100061384048640 }, { target := 489, numerator := 425293883559493490643566592 }, { target := 490, numerator := 5108502699549839389391585280 }, { target := 491, numerator := 213428010358551241335767040 }, { target := 627, numerator := 238349107351060030471274496 }, { target := 629, numerator := 2308666873689985557580480512 }, { target := 634, numerator := 238349107351060030471274496 }]

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
    Slot10.Left14.expected,
    Slot10.Left15.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 1, numerator := 3551282166473871223498473472 }, { target := 2, numerator := 3551282166473871223498473472 }, { target := 3, numerator := 3551282166473871223498473472 }, { target := 4, numerator := 3551282166473871223498473472 }, { target := 51, numerator := 12704477476209962668800344064 }, { target := 52, numerator := 12704477476209962668800344064 }, { target := 53, numerator := 12704477476209962668800344064 }, { target := 54, numerator := 12704477476209962668800344064 }, { target := 140, numerator := 3551280985882250506087170048 }, { target := 141, numerator := 3551280985882250506087170048 }, { target := 142, numerator := 3551280985882250506087170048 }, { target := 143, numerator := 3551280985882250506087170048 }, { target := 653, numerator := 238349107351060030471274496 }, { target := 655, numerator := 2308666873689985557580480512 }, { target := 660, numerator := 238349107351060030471274496 }, { target := 749, numerator := 251590724426118921053011968 }, { target := 751, numerator := 2436926144450540310779396096 }, { target := 756, numerator := 251590724426118921053011968 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14.Parent2
