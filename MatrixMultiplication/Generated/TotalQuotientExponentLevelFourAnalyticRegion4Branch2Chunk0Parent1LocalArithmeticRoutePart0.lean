import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk0Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 19; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk0.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left6.expected,
    Slot9.Left14.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
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
  [{ target := 29, numerator := 8201689487073419020206080 }, { target := 30, numerator := 388698241956341153838137344 }, { target := 35, numerator := 388594576424216328425963520 }, { target := 43, numerator := 8306963703859241266708480 }, { target := 71, numerator := 865801878815781335072768 }, { target := 72, numerator := 26835464878832879992307712 }, { target := 74, numerator := 314991250121183903505973248 }, { target := 82, numerator := 26835663573707789904642048 }, { target := 89, numerator := 865912264857397953036288 }, { target := 104, numerator := 401097277953487040403210240 }, { target := 105, numerator := 19008986750804883871610437632 }, { target := 110, numerator := 19003917068172006718502338560 }, { target := 118, numerator := 406245632064920936188477440 }, { target := 146, numerator := 26835464878832879992307712 }, { target := 147, numerator := 831763239239053801955524608 }, { target := 149, numerator := 9763130384203341098523820032 }, { target := 157, numerator := 831769397771932642660319232 }, { target := 164, numerator := 26838886285987791494971392 }, { target := 200, numerator := 8201689487073419020206080 }, { target := 202, numerator := 401097277953487040403210240 }, { target := 205, numerator := 401097424330326554129203200 }, { target := 212, numerator := 8202226202151636015513600 }, { target := 226, numerator := 401097424330326554129203200 }, { target := 227, numerator := 19008993687963413438540021760 }, { target := 232, numerator := 19003924003480401263512780800 }, { target := 240, numerator := 406245780320605919458099200 }, { target := 242, numerator := 314991250121183903505973248 }, { target := 243, numerator := 9763130384203341098523820032 }, { target := 245, numerator := 114598374155315731296606486528 }, { target := 253, numerator := 9763202672273593556772323328 }, { target := 260, numerator := 315031410160213046977363968 }, { target := 296, numerator := 388698241956341153838137344 }, { target := 298, numerator := 19008986750804883871610437632 }, { target := 301, numerator := 19008993687963413438540021760 }, { target := 308, numerator := 388723678204282899246612480 }, { target := 624, numerator := 8202226202151636015513600 }, { target := 625, numerator := 388723678204282899246612480 }, { target := 630, numerator := 388620005888329660130918400 }, { target := 638, numerator := 8307507308037513255321600 }, { target := 640, numerator := 26835663573707789904642048 }, { target := 641, numerator := 831769397771932642660319232 }, { target := 643, numerator := 9763202672273593556772323328 }, { target := 651, numerator := 831775556350410429592240128 }, { target := 658, numerator := 26839085006195449311264768 }, { target := 659, numerator := 388594576424216328425963520 }, { target := 661, numerator := 19003917068172006718502338560 }, { target := 664, numerator := 19003924003480401263512780800 }, { target := 671, numerator := 388620005888329660130918400 }, { target := 1017, numerator := 865912264857397953036288 }, { target := 1018, numerator := 26838886285987791494971392 }, { target := 1020, numerator := 315031410160213046977363968 }, { target := 1028, numerator := 26839085006195449311264768 }, { target := 1035, numerator := 866022664972763406532608 }, { target := 1036, numerator := 8306963703859241266708480 }, { target := 1038, numerator := 406245632064920936188477440 }, { target := 1041, numerator := 406245780320605919458099200 }, { target := 1048, numerator := 8307507308037513255321600 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk0.Parent1
