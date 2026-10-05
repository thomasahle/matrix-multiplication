import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk22Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 93; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk22.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot0.Left1.expected,
    Slot0.Left3.expected,
    Slot0.Left11.expected,
    Slot0.Left18.expected,
    Slot1.Left0.expected,
    Slot1.Left2.expected,
    Slot1.Left5.expected,
    Slot1.Left12.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left3.expected,
    Slot2.Left11.expected,
    Slot2.Left18.expected,
    Slot3.Left0.expected,
    Slot3.Left3.expected,
    Slot3.Left5.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot4.Left5.expected,
    Slot4.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 4644787815223944156316434432 }, { target := 36, numerator := 92895756304478883126328688640 }, { target := 37, numerator := 4810673094339085019042021376 }, { target := 38, numerator := 86426230418988389480030797824 }, { target := 39, numerator := 129390517709809872925957816320 }, { target := 40, numerator := 4644787815223944156316434432 }, { target := 41, numerator := 129556402988925013788683403264 }, { target := 42, numerator := 129556402988925013788683403264 }, { target := 43, numerator := 92729871025363742263603101696 }, { target := 44, numerator := 4810673094339085019042021376 }, { target := 71, numerator := 22341990243820379168244236288 }, { target := 72, numerator := 3874831748740263550176460800 }, { target := 73, numerator := 22341990243820379168244236288 }, { target := 74, numerator := 3874831748740263550176460800 }, { target := 89, numerator := 330301201277834464826753024 }, { target := 106, numerator := 16707163645018595268646404096 }, { target := 107, numerator := 334143272900371905372928081920 }, { target := 108, numerator := 17303848060912116528240918528 }, { target := 109, numerator := 310872580680524576248742019072 }, { target := 110, numerator := 465413844396946582483721256960 }, { target := 111, numerator := 16707163645018595268646404096 }, { target := 112, numerator := 466010528812840103743315771392 }, { target := 113, numerator := 466010528812840103743315771392 }, { target := 114, numerator := 333546588484478384113333567488 }, { target := 115, numerator := 17303848060912116528240918528 }, { target := 116, numerator := 871915035359919371435269685248 }, { target := 117, numerator := 151641385686485633484026019840 }, { target := 118, numerator := 871915035359919371435269685248 }, { target := 119, numerator := 151641385686485633484026019840 }, { target := 134, numerator := 58877728619247408859708391424 }, { target := 140, numerator := 4644789364750446347918770176 }, { target := 141, numerator := 92895787295008926958375403520 }, { target := 142, numerator := 4810674699205819431773011968 }, { target := 143, numerator := 86426259251249376688059973632 }, { target := 144, numerator := 129390560875191005406308597760 }, { target := 145, numerator := 4644789364750446347918770176 }, { target := 146, numerator := 129556446209646378490162839552 }, { target := 147, numerator := 129556446209646378490162839552 }, { target := 148, numerator := 92729901960553553874521161728 }, { target := 149, numerator := 4810674699205819431773011968 }, { target := 150, numerator := 871914766185029847865492504576 }, { target := 151, numerator := 151641385686485633484026019840 }, { target := 152, numerator := 871914766185029847865492504576 }, { target := 153, numerator := 151641385686485633484026019840 }, { target := 154, numerator := 594637289650532962821340135424 }, { target := 232, numerator := 22342079968783553691503296512 }, { target := 233, numerator := 3874831748740263550176460800 }, { target := 234, numerator := 22342079968783553691503296512 }, { target := 235, numerator := 3874831748740263550176460800 }, { target := 236, numerator := 58877841956042997731193520128 }, { target := 265, numerator := 330301201277834464826753024 }]

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
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot5.Left4.expected,
    Slot5.Left5.expected,
    Slot5.Left6.expected,
    Slot5.Left7.expected,
    Slot5.Left8.expected,
    Slot5.Left9.expected,
    Slot5.Left10.expected,
    Slot5.Left11.expected,
    Slot5.Left12.expected,
    Slot5.Left13.expected,
    Slot5.Left14.expected,
    Slot5.Left15.expected,
    Slot5.Left16.expected,
    Slot5.Left17.expected,
    Slot5.Left18.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 17060359132648112786975490048 }, { target := 20, numerator := 19429853456627017340722085888 }, { target := 21, numerator := 15164763673464989143978213376 }, { target := 22, numerator := 203302612997390010711457923072 }, { target := 23, numerator := 18008156862239674608474128384 }, { target := 24, numerator := 15164763673464989143978213376 }, { target := 25, numerator := 18008156862239674608474128384 }, { target := 26, numerator := 17534257997443893697724809216 }, { target := 27, numerator := 662510612984501713227548196864 }, { target := 28, numerator := 17534257997443893697724809216 }, { target := 29, numerator := 203302612997390010711457923072 }, { target := 30, numerator := 662510612984501713227548196864 }, { target := 31, numerator := 17060359132648112786975490048 }, { target := 32, numerator := 17534257997443893697724809216 }, { target := 33, numerator := 17534257997443893697724809216 }, { target := 34, numerator := 19429853456627017340722085888 }, { target := 35, numerator := 300041307593083400296087945216 }, { target := 38, numerator := 1095906371171723208984782438400 }, { target := 40, numerator := 300041206504268350822148997120 }, { target := 71, numerator := 16712188538104273750506602496 }, { target := 73, numerator := 16712192522600993671769751552 }, { target := 85, numerator := 19033325835063200660299186176 }, { target := 87, numerator := 19033330372962242792848883712 }, { target := 89, numerator := 812398150781030805402550272 }, { target := 90, numerator := 17060363200155181039931621376 }, { target := 91, numerator := 19429858089065622851033235456 }, { target := 92, numerator := 15164767289026827591050330112 }, { target := 93, numerator := 203302661468515907392518488064 }, { target := 94, numerator := 18008161155719357764372267008 }, { target := 95, numerator := 15164767289026827591050330112 }, { target := 96, numerator := 18008161155719357764372267008 }, { target := 97, numerator := 17534262177937269402151944192 }, { target := 98, numerator := 662510770939359530384011296768 }, { target := 99, numerator := 17534262177937269402151944192 }, { target := 100, numerator := 203302661468515907392518488064 }, { target := 101, numerator := 662510770939359530384011296768 }, { target := 102, numerator := 17060363200155181039931621376 }, { target := 103, numerator := 17534262177937269402151944192 }, { target := 104, numerator := 17534262177937269402151944192 }, { target := 105, numerator := 19429858089065622851033235456 }, { target := 106, numerator := 1095906371171723208984782438400 }, { target := 109, numerator := 4002818091979481324621660160000 }, { target := 111, numerator := 1095906001942974822233407488000 }, { target := 134, numerator := 12185972261715462081038254080 }, { target := 139, numerator := 21393151303900477875600490496 }, { target := 140, numerator := 300041206504268350822148997120 }, { target := 143, numerator := 1095906001942974822233407488000 }, { target := 145, numerator := 300041105415487359820392038400 }, { target := 154, numerator := 812398150781030805402550272 }, { target := 159, numerator := 13539969179683846756709171200 }, { target := 160, numerator := 812398150781030805402550272 }, { target := 205, numerator := 21393151303900477875600490496 }, { target := 210, numerator := 21257751612103639408033398784 }, { target := 225, numerator := 13539969179683846756709171200 }, { target := 230, numerator := 328073453223739606915063218176 }, { target := 231, numerator := 20986952228509962472899215360 }, { target := 236, numerator := 12185972261715462081038254080 }, { target := 237, numerator := 21393151303900477875600490496 }, { target := 252, numerator := 812398150781030805402550272 }, { target := 257, numerator := 20986952228509962472899215360 }, { target := 258, numerator := 812398150781030805402550272 }, { target := 263, numerator := 21393151303900477875600490496 }, { target := 264, numerator := 21393151303900477875600490496 }, { target := 265, numerator := 812398150781030805402550272 }]

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
    Slot8.Left2.expected,
    Slot8.Left3.expected,
    Slot8.Left4.expected,
    Slot8.Left5.expected,
    Slot8.Left6.expected,
    Slot8.Left7.expected,
    Slot8.Left8.expected,
    Slot8.Left9.expected,
    Slot8.Left10.expected,
    Slot8.Left11.expected,
    Slot8.Left12.expected,
    Slot8.Left13.expected,
    Slot8.Left14.expected,
    Slot8.Left15.expected,
    Slot9.Left0.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 812398150781030805402550272 }, { target := 1, numerator := 12185972261715462081038254080 }, { target := 2, numerator := 21393151303900477875600490496 }, { target := 3, numerator := 812398150781030805402550272 }, { target := 4, numerator := 13539969179683846756709171200 }, { target := 5, numerator := 812398150781030805402550272 }, { target := 6, numerator := 21393151303900477875600490496 }, { target := 7, numerator := 21257751612103639408033398784 }, { target := 8, numerator := 13539969179683846756709171200 }, { target := 9, numerator := 328073453223739606915063218176 }, { target := 10, numerator := 20986952228509962472899215360 }, { target := 11, numerator := 12185972261715462081038254080 }, { target := 12, numerator := 21393151303900477875600490496 }, { target := 13, numerator := 812398150781030805402550272 }, { target := 14, numerator := 20986952228509962472899215360 }, { target := 15, numerator := 812398150781030805402550272 }, { target := 16, numerator := 21393151303900477875600490496 }, { target := 17, numerator := 21393151303900477875600490496 }, { target := 18, numerator := 812398150781030805402550272 }, { target := 19, numerator := 19804377213869745918485463040 }, { target := 21, numerator := 772477342376103287409858314240 }, { target := 24, numerator := 772477059034114315231145492480 }, { target := 31, numerator := 19804471661199403311389736960 }, { target := 35, numerator := 4644787815223944156316434432 }, { target := 38, numerator := 16707163645018595268646404096 }, { target := 40, numerator := 4644789364750446347918770176 }, { target := 61, numerator := 92895756304478883126328688640 }, { target := 64, numerator := 334143272900371905372928081920 }, { target := 66, numerator := 92895787295008926958375403520 }, { target := 75, numerator := 4810673094339085019042021376 }, { target := 78, numerator := 17303848060912116528240918528 }, { target := 80, numerator := 4810674699205819431773011968 }, { target := 90, numerator := 19804377213869745918485463040 }, { target := 92, numerator := 772477342376103287409858314240 }, { target := 95, numerator := 772477059034114315231145492480 }, { target := 102, numerator := 19804471661199403311389736960 }, { target := 116, numerator := 14855278700537132222672535552 }, { target := 118, numerator := 14855282242311994374906445824 }, { target := 130, numerator := 199153580079075928860203679744 }, { target := 132, numerator := 199153627560995174588589539328 }, { target := 135, numerator := 17640643456887844514423635968 }, { target := 137, numerator := 17640647662745493320201404416 }, { target := 150, numerator := 14855278700537132222672535552 }, { target := 152, numerator := 14855282242311994374906445824 }, { target := 155, numerator := 17640643456887844514423635968 }, { target := 157, numerator := 17640647662745493320201404416 }, { target := 187, numerator := 17176415997496059132465119232 }, { target := 189, numerator := 17176420092673243495985577984 }, { target := 201, numerator := 648989988229715963978006396928 }, { target := 203, numerator := 648990142961005254253725351936 }, { target := 206, numerator := 17176415997496059132465119232 }, { target := 208, numerator := 17176420092673243495985577984 }, { target := 221, numerator := 199153580079075928860203679744 }, { target := 223, numerator := 199153627560995174588589539328 }, { target := 226, numerator := 648989988229715963978006396928 }, { target := 228, numerator := 648990142961005254253725351936 }, { target := 232, numerator := 16712188538104273750506602496 }, { target := 234, numerator := 16712192522600993671769751552 }, { target := 248, numerator := 17176415997496059132465119232 }, { target := 250, numerator := 17176420092673243495985577984 }, { target := 253, numerator := 17176415997496059132465119232 }, { target := 255, numerator := 17176420092673243495985577984 }, { target := 259, numerator := 19033325835063200660299186176 }, { target := 261, numerator := 19033330372962242792848883712 }]

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
    Slot11.Left3.expected,
    Slot11.Left4.expected,
    Slot11.Left5.expected,
    Slot11.Left6.expected,
    Slot11.Left7.expected,
    Slot11.Left8.expected,
    Slot11.Left9.expected,
    Slot12.Left0.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left2.expected,
    Slot13.Left3.expected,
    Slot14.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 330301201277834464826753024 }, { target := 1, numerator := 58877728619247408859708391424 }, { target := 3, numerator := 594637289650532962821340135424 }, { target := 11, numerator := 58877841956042997731193520128 }, { target := 18, numerator := 330301201277834464826753024 }, { target := 19, numerator := 3527831890644120545683046400 }, { target := 21, numerator := 138061560102621248395904286720 }, { target := 24, numerator := 138061560102621248395904286720 }, { target := 31, numerator := 3527831890644120545683046400 }, { target := 45, numerator := 3874831748740263550176460800 }, { target := 47, numerator := 151641385686485633484026019840 }, { target := 50, numerator := 151641385686485633484026019840 }, { target := 57, numerator := 3874831748740263550176460800 }, { target := 90, numerator := 3527831890644120545683046400 }, { target := 92, numerator := 138061560102621248395904286720 }, { target := 95, numerator := 138061560102621248395904286720 }, { target := 102, numerator := 3527831890644120545683046400 }, { target := 106, numerator := 86426230418988389480030797824 }, { target := 109, numerator := 310872580680524576248742019072 }, { target := 111, numerator := 86426259251249376688059973632 }, { target := 120, numerator := 129390517709809872925957816320 }, { target := 123, numerator := 465413844396946582483721256960 }, { target := 125, numerator := 129390560875191005406308597760 }, { target := 140, numerator := 4644787815223944156316434432 }, { target := 143, numerator := 16707163645018595268646404096 }, { target := 145, numerator := 4644789364750446347918770176 }, { target := 161, numerator := 3874831748740263550176460800 }, { target := 163, numerator := 151641385686485633484026019840 }, { target := 166, numerator := 151641385686485633484026019840 }, { target := 173, numerator := 3874831748740263550176460800 }, { target := 177, numerator := 129556402988925013788683403264 }, { target := 180, numerator := 466010528812840103743315771392 }, { target := 182, numerator := 129556446209646378490162839552 }, { target := 191, numerator := 129556402988925013788683403264 }, { target := 194, numerator := 466010528812840103743315771392 }, { target := 196, numerator := 129556446209646378490162839552 }, { target := 211, numerator := 92729871025363742263603101696 }, { target := 214, numerator := 333546588484478384113333567488 }, { target := 216, numerator := 92729901960553553874521161728 }, { target := 238, numerator := 4810673094339085019042021376 }, { target := 241, numerator := 17303848060912116528240918528 }, { target := 243, numerator := 4810674699205819431773011968 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk22.Parent3
