import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk19Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 79; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk19.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot1.Left0.expected,
    Slot1.Left3.expected,
    Slot1.Left5.expected,
    Slot2.Left0.expected,
    Slot2.Left2.expected,
    Slot2.Left5.expected,
    Slot2.Left12.expected,
    Slot3.Left0.expected,
    Slot3.Left2.expected,
    Slot4.Left0.expected,
    Slot4.Left3.expected,
    Slot4.Left5.expected,
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot5.Left5.expected,
    Slot5.Left12.expected,
    Slot6.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 16712190530352633711138177024 }, { target := 1, numerator := 19033328104012721726574034944 }, { target := 2, numerator := 14855280471424563298789490688 }, { target := 3, numerator := 199153603820035551724396609536 }, { target := 4, numerator := 17640645559816668917312520192 }, { target := 5, numerator := 14855280471424563298789490688 }, { target := 6, numerator := 17640645559816668917312520192 }, { target := 7, numerator := 17176418045084651314225348608 }, { target := 8, numerator := 648990065595360609115865874432 }, { target := 9, numerator := 17176418045084651314225348608 }, { target := 10, numerator := 199153603820035551724396609536 }, { target := 11, numerator := 648990065595360609115865874432 }, { target := 12, numerator := 16712190530352633711138177024 }, { target := 13, numerator := 17176418045084651314225348608 }, { target := 14, numerator := 17176418045084651314225348608 }, { target := 15, numerator := 19033328104012721726574034944 }, { target := 16, numerator := 1895595007237893837113262080 }, { target := 17, numerator := 37911900144757876742265241600 }, { target := 18, numerator := 1963294828924961474153021440 }, { target := 19, numerator := 35271607098962238897714626560 }, { target := 20, numerator := 52805860915912756891012300800 }, { target := 21, numerator := 1895595007237893837113262080 }, { target := 22, numerator := 52873560737599824528052060160 }, { target := 23, numerator := 52873560737599824528052060160 }, { target := 24, numerator := 37844200323070809105225482240 }, { target := 25, numerator := 1963294828924961474153021440 }, { target := 26, numerator := 436039463558924605290230841344 }, { target := 27, numerator := 3674707191248749283053142016 }, { target := 28, numerator := 436039463558924605290230841344 }, { target := 29, numerator := 3674707191248749283053142016 }, { target := 44, numerator := 85787151769651645223750598656 }, { target := 50, numerator := 1895596363073583254765305856 }, { target := 51, numerator := 37911927261471665095306117120 }, { target := 52, numerator := 1963296233183354085292638208 }, { target := 53, numerator := 35271632327190602704740155392 }, { target := 54, numerator := 52805898685621247811319234560 }, { target := 55, numerator := 1895596363073583254765305856 }, { target := 56, numerator := 52873598555731018641846566912 }, { target := 57, numerator := 52873598555731018641846566912 }, { target := 58, numerator := 37844227391361894264778784768 }, { target := 59, numerator := 1963296233183354085292638208 }, { target := 60, numerator := 1563132872824656229613992673280 }, { target := 61, numerator := 13386078803668915161374130176 }, { target := 62, numerator := 1563132872824656229613992673280 }, { target := 63, numerator := 13386078803668915161374130176 }, { target := 64, numerator := 3360636760621058737032333885440 }, { target := 71, numerator := 436165205900583510891078615040 }, { target := 72, numerator := 3674709663112455160133058560 }, { target := 73, numerator := 436165205900583510891078615040 }, { target := 74, numerator := 3674709663112455160133058560 }, { target := 75, numerator := 3360637898711381108616830386176 }, { target := 104, numerator := 85788327638905879765408808960 }]

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
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot10.Left0.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left1.expected,
    Slot17.Left2.expected,
    Slot17.Left3.expected,
    Slot17.Left4.expected,
    Slot17.Left5.expected,
    Slot17.Left6.expected,
    Slot17.Left7.expected,
    Slot17.Left8.expected,
    Slot17.Left9.expected,
    Slot17.Left10.expected,
    Slot17.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1261945457334243271547939717120 }, { target := 2, numerator := 49325238551147615645011349078016 }, { target := 5, numerator := 49325231821775377555766919561216 }, { target := 12, numerator := 1261947700458322634629416222720 }, { target := 16, numerator := 39040441901893076218533491245056 }, { target := 19, numerator := 141938026834663327633336199806976 }, { target := 21, numerator := 39038144506292697095415537860608 }, { target := 26, numerator := 38998627293238291072937189441536 }, { target := 28, numerator := 38998625099548824762967488724992 }, { target := 44, numerator := 1280641282628091782600736112640 }, { target := 49, numerator := 19033328104012721726574034944 }, { target := 50, numerator := 39040439714798045632387732209664 }, { target := 53, numerator := 141938019327930894581112701452288 }, { target := 55, numerator := 39038142318646089833757437591552 }, { target := 60, numerator := 141783965746475294385437650452480 }, { target := 62, numerator := 141783958215151408179720109424640 }, { target := 64, numerator := 49417338373536908117170959941632 }, { target := 69, numerator := 199153603820035551724396609536 }, { target := 70, numerator := 17640645559816668917312520192 }, { target := 71, numerator := 38996335734482188407608338022400 }, { target := 73, numerator := 38996333540242538160311060398080 }, { target := 75, numerator := 49417331601663371682099723501568 }, { target := 76, numerator := 17640645559816668917312520192 }, { target := 91, numerator := 17176418045084651314225348608 }, { target := 96, numerator := 648990065595360609115865874432 }, { target := 97, numerator := 17176418045084651314225348608 }, { target := 102, numerator := 199153603820035551724396609536 }, { target := 103, numerator := 648990065595360609115865874432 }, { target := 104, numerator := 1263931349388917960580010082304 }]

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
    Slot17.Left12.expected,
    Slot17.Left13.expected,
    Slot17.Left14.expected,
    Slot17.Left15.expected,
    Slot18.Left0.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot20.Left0.expected,
    Slot20.Left1.expected,
    Slot20.Left2.expected,
    Slot20.Left3.expected,
    Slot20.Left4.expected,
    Slot20.Left5.expected,
    Slot20.Left6.expected,
    Slot20.Left7.expected,
    Slot20.Left8.expected,
    Slot20.Left9.expected,
    Slot21.Left0.expected,
    Slot22.Left0.expected,
    Slot22.Left1.expected,
    Slot22.Left2.expected,
    Slot22.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 89735125707194394536723873792 }, { target := 2, numerator := 3515145055043646868470705946624 }, { target := 5, numerator := 3515146249802367034490945011712 }, { target := 12, numerator := 89736358244846423514124648448 }, { target := 16, numerator := 428946122007717907260336242688 }, { target := 19, numerator := 1537707535982907229477145673728 }, { target := 21, numerator := 429069803036407040261048238080 }, { target := 26, numerator := 1895595007237893837113262080 }, { target := 28, numerator := 1895596363073583254765305856 }, { target := 30, numerator := 3674707191248749283053142016 }, { target := 33, numerator := 13386078803668915161374130176 }, { target := 35, numerator := 3674709663112455160133058560 }, { target := 40, numerator := 37911900144757876742265241600 }, { target := 42, numerator := 37911927261471665095306117120 }, { target := 45, numerator := 1963294828924961474153021440 }, { target := 47, numerator := 1963296233183354085292638208 }, { target := 50, numerator := 428946122007717907260336242688 }, { target := 53, numerator := 1537707535982907229477145673728 }, { target := 55, numerator := 429069803036407040261048238080 }, { target := 60, numerator := 35271607098962238897714626560 }, { target := 62, numerator := 35271632327190602704740155392 }, { target := 65, numerator := 52805860915912756891012300800 }, { target := 67, numerator := 52805898685621247811319234560 }, { target := 71, numerator := 1895595007237893837113262080 }, { target := 73, numerator := 1895596363073583254765305856 }, { target := 77, numerator := 3674707191248749283053142016 }, { target := 80, numerator := 13386078803668915161374130176 }, { target := 82, numerator := 3674709663112455160133058560 }, { target := 87, numerator := 52873560737599824528052060160 }, { target := 89, numerator := 52873598555731018641846566912 }, { target := 92, numerator := 52873560737599824528052060160 }, { target := 94, numerator := 52873598555731018641846566912 }, { target := 98, numerator := 37844200323070809105225482240 }, { target := 100, numerator := 37844227391361894264778784768 }, { target := 104, numerator := 16712190530352633711138177024 }, { target := 105, numerator := 1963294828924961474153021440 }, { target := 107, numerator := 1963296233183354085292638208 }, { target := 109, numerator := 17176418045084651314225348608 }, { target := 110, numerator := 17176418045084651314225348608 }, { target := 111, numerator := 19033328104012721726574034944 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk19.Parent1
