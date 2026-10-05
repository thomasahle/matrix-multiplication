import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk7Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 74; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk7.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left3.expected,
    Slot11.Left11.expected,
    Slot11.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 40934430767047011697950720 }, { target := 27, numerator := 1121619565822253829028052992 }, { target := 29, numerator := 11946836967086303402631626752 }, { target := 37, numerator := 1124637757018460869707694080 }, { target := 44, numerator := 37911986201059521411940352 }, { target := 80, numerator := 61198657114808005674663936 }, { target := 82, numerator := 2144422371936325767239041024 }, { target := 85, numerator := 2144426917435192270976450560 }, { target := 92, numerator := 61199587758901203837124608 }, { target := 131, numerator := 40934430767047011697950720 }, { target := 134, numerator := 145425808638324640422297600 }, { target := 136, numerator := 40880035750315675562803200 }, { target := 157, numerator := 145425808638324640422297600 }, { target := 158, numerator := 3984724577520604876751503360 }, { target := 160, numerator := 42442960462696304766783324160 }, { target := 168, numerator := 3995447162081053252150886400 }, { target := 175, numerator := 134688113333005283659612160 }, { target := 176, numerator := 2144422371936325767239041024 }, { target := 178, numerator := 74877920774006194718231232512 }, { target := 181, numerator := 74878076788758328399758360576 }, { target := 188, numerator := 2144459220190318529033011200 }, { target := 227, numerator := 1121619565822253829028052992 }, { target := 230, numerator := 3984724577520604876751503360 }, { target := 232, numerator := 1120129120886148595995115520 }, { target := 267, numerator := 40880035750315675562803200 }, { target := 268, numerator := 1120129120886148595995115520 }, { target := 270, numerator := 11930961617544754513439621120 }, { target := 278, numerator := 1123143301410714681134284800 }, { target := 285, numerator := 37861607507986673167237120 }, { target := 286, numerator := 2144426917435192270976450560 }, { target := 288, numerator := 74878076788758328399758360576 }, { target := 291, numerator := 74878232803807699656691941376 }, { target := 298, numerator := 2144463765810782222709424128 }, { target := 302, numerator := 11946836967086303402631626752 }, { target := 305, numerator := 42442960462696304766783324160 }, { target := 307, numerator := 11930961617544754513439621120 }, { target := 573, numerator := 61199587758901203837124608 }, { target := 575, numerator := 2144459220190318529033011200 }, { target := 578, numerator := 2144463765810782222709424128 }, { target := 585, numerator := 61200518348951206471139328 }, { target := 589, numerator := 1124637757018460869707694080 }, { target := 592, numerator := 3995447162081053252150886400 }, { target := 594, numerator := 1123143301410714681134284800 }, { target := 763, numerator := 37911986201059521411940352 }, { target := 766, numerator := 134688113333005283659612160 }, { target := 768, numerator := 37861607507986673167237120 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk7.Parent1
