import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk2Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 45; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk2.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left3.expected,
    Slot6.Left11.expected,
    Slot6.Left18.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 803609844972344988466675712 }, { target := 37, numerator := 27784973317330218874270908416 }, { target := 40, numerator := 27785048294761017613830062080 }, { target := 47, numerator := 803601325901365359560097792 }, { target := 86, numerator := 1090317952050623840362954752 }, { target := 89, numerator := 3875451347980454279172325376 }, { target := 91, numerator := 1090736549746484911708045312 }, { target := 122, numerator := 110864896835982105014960128 }, { target := 124, numerator := 110958823963853739607982080 }, { target := 145, numerator := 2846084677026344528013950976 }, { target := 147, numerator := 98404449443715668540733259776 }, { target := 150, numerator := 98404714975229122364798140416 }, { target := 157, numerator := 2846054490870156391775993856 }, { target := 161, numerator := 41674183053723075100947775488 }, { target := 164, numerator := 148270809116030903379292061696 }, { target := 166, numerator := 41682947021963125442341765120 }, { target := 197, numerator := 3183861501668504542226939904 }, { target := 199, numerator := 3186558937691335284951613440 }, { target := 216, numerator := 804417932811545500851372032 }, { target := 218, numerator := 27812605640379720838588399616 }, { target := 221, numerator := 27812680699685960803743170560 }, { target := 228, numerator := 804409414373884569543770112 }, { target := 232, numerator := 34722650064021423331278323712 }, { target := 235, numerator := 123639003434091223955483394048 }, { target := 237, numerator := 34731931031482086390352576512 }, { target := 242, numerator := 33007956102264062176982466560 }, { target := 244, numerator := 33035921153439687467702681600 }, { target := 406, numerator := 895549450220320240739287040 }, { target := 409, numerator := 3185318173549743020349325312 }, { target := 411, numerator := 895982466494944263528251392 }, { target := 416, numerator := 3183712810111638536806465536 }, { target := 418, numerator := 3186410120159780502723624960 }, { target := 498, numerator := 110912100504828455942094848 }, { target := 500, numerator := 111006067624664781585121280 }]

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
    Slot19.Left5.expected,
    Slot19.Left12.expected,
    Slot20.Left0.expected,
    Slot20.Left3.expected,
    Slot20.Left5.expected,
    Slot21.Left0.expected,
    Slot21.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 110864896835982105014960128 }, { target := 17, numerator := 3183861501668504542226939904 }, { target := 19, numerator := 33007956102264062176982466560 }, { target := 27, numerator := 3183712810111638536806465536 }, { target := 34, numerator := 110912100504828455942094848 }, { target := 35, numerator := 286708107078278851896279040 }, { target := 37, numerator := 13889209736392856226676867072 }, { target := 40, numerator := 13889111722304617748700856320 }, { target := 47, numerator := 286755424224325013677801472 }, { target := 126, numerator := 110958823963853739607982080 }, { target := 127, numerator := 3186558937691335284951613440 }, { target := 129, numerator := 33035921153439687467702681600 }, { target := 137, numerator := 3186410120159780502723624960 }, { target := 144, numerator := 111006067624664781585121280 }, { target := 145, numerator := 1029366670954109751158374400 }, { target := 147, numerator := 49866359672315234838558801920 }, { target := 150, numerator := 49866007772828524132643635200 }, { target := 157, numerator := 1029536553464935609186385920 }, { target := 216, numerator := 286318616934939410856673280 }, { target := 218, numerator := 13870341381583404603753365504 }, { target := 221, numerator := 13870243500646340908799754240 }, { target := 228, numerator := 286365869801108091179106304 }, { target := 232, numerator := 6951509953044212031252594688 }, { target := 235, numerator := 24631719313966422541958381568 }, { target := 237, numerator := 6950993168850215322190348288 }, { target := 406, numerator := 194807299905370132498612224 }, { target := 409, numerator := 690272870785348980613054464 }, { target := 411, numerator := 194792817680048397194625024 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk2.Parent2
