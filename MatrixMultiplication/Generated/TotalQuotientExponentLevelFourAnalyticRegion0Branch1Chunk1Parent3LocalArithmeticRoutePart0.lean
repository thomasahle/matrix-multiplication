import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk1Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 34; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk1.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left6.expected,
    Slot9.Left14.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected,
    Slot15.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 10028217784223140073701376 }, { target := 30, numerator := 519856364323613949625892864 }, { target := 35, numerator := 519952505240918414459928576 }, { target := 43, numerator := 9937509270918796117278720 }, { target := 71, numerator := 972236992981150501699584 }, { target := 72, numerator := 45230134578774584613404672 }, { target := 74, numerator := 468092691096760926691393536 }, { target := 82, numerator := 45230478415095335468662784 }, { target := 89, numerator := 972136768186193138417664 }, { target := 104, numerator := 364653759266466372079583232 }, { target := 105, numerator := 18903416500132268053729640448 }, { target := 110, numerator := 18906912450027727512385093632 }, { target := 118, numerator := 361355346618713558262743040 }, { target := 146, numerator := 20726563031350585250021376 }, { target := 147, numerator := 1044755185900931615333285888 }, { target := 149, numerator := 11475246172879472550060490752 }, { target := 157, numerator := 1044762484843189398142976000 }, { target := 164, numerator := 20724130050597990980124672 }, { target := 200, numerator := 10028217784223140073701376 }, { target := 202, numerator := 364653759266466372079583232 }, { target := 205, numerator := 364823610149637946991443968 }, { target := 212, numerator := 10198426154125936400793600 }, { target := 226, numerator := 364823610149637946991443968 }, { target := 227, numerator := 18912221460744675621026660352 }, { target := 232, numerator := 18915719039007215297985773568 }, { target := 240, numerator := 361523661145034151910440960 }, { target := 242, numerator := 198953547863909088154877952 }, { target := 243, numerator := 10028568198683339501261029376 }, { target := 245, numerator := 110150483476340655338400251904 }, { target := 253, numerator := 10028638260972762171441152000 }, { target := 260, numerator := 198930193767434864761503744 }, { target := 296, numerator := 519856364323613949625892864 }, { target := 298, numerator := 18903416500132268053729640448 }, { target := 301, numerator := 18912221460744675621026660352 }, { target := 308, numerator := 528679856818394382100070400 }, { target := 624, numerator := 10198426154125936400793600 }, { target := 625, numerator := 528679856818394382100070400 }, { target := 630, numerator := 528777629530018381666713600 }, { target := 638, numerator := 10106178050386078728192000 }, { target := 640, numerator := 20726735679094100311670784 }, { target := 641, numerator := 1044763888483462960425992192 }, { target := 643, numerator := 11475341759173979304590573568 }, { target := 651, numerator := 1044771187486519338205184000 }, { target := 658, numerator := 20724302678075307718606848 }, { target := 659, numerator := 519952505240918414459928576 }, { target := 661, numerator := 18906912450027727512385093632 }, { target := 664, numerator := 18915719039007215297985773568 }, { target := 671, numerator := 528777629530018381666713600 }, { target := 1017, numerator := 486075334554696485437440 }, { target := 1018, numerator := 24501395901791163090206720 }, { target := 1020, numerator := 269115246659225149903994880 }, { target := 1028, numerator := 24501567075168750141440000 }, { target := 1035, numerator := 486018276762167468359680 }, { target := 1036, numerator := 9937509270918796117278720 }, { target := 1038, numerator := 361355346618713558262743040 }, { target := 1041, numerator := 361523661145034151910440960 }, { target := 1048, numerator := 10106178050386078728192000 }]

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
    Slot15.Left1.expected,
    Slot15.Left3.expected,
    Slot15.Left11.expected,
    Slot15.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 146, numerator := 24503571547423999363383296 }, { target := 147, numerator := 1044755185900931615333285888 }, { target := 149, numerator := 10028568198683339501261029376 }, { target := 157, numerator := 1044763888483462960425992192 }, { target := 164, numerator := 24501395901791163090206720 }, { target := 242, numerator := 269139143232851838536515584 }, { target := 243, numerator := 11475246172879472550060490752 }, { target := 245, numerator := 110150483476340655338400251904 }, { target := 253, numerator := 11475341759173979304590573568 }, { target := 260, numerator := 269115246659225149903994880 }, { target := 640, numerator := 24503742736001235156992000 }, { target := 641, numerator := 1044762484843189398142976000 }, { target := 643, numerator := 10028638260972762171441152000 }, { target := 651, numerator := 1044771187486519338205184000 }, { target := 658, numerator := 24501567075168750141440000 }, { target := 1017, numerator := 486061433631496652980224 }, { target := 1018, numerator := 20724130050597990980124672 }, { target := 1020, numerator := 198930193767434864761503744 }, { target := 1028, numerator := 20724302678075307718606848 }, { target := 1035, numerator := 486018276762167468359680 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk1.Parent3
