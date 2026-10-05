import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk22Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 93; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk22.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot0.Left3.expected,
    Slot0.Left5.expected,
    Slot1.Left0.expected,
    Slot1.Left3.expected,
    Slot1.Left5.expected,
    Slot2.Left0.expected,
    Slot2.Left2.expected,
    Slot3.Left0.expected,
    Slot3.Left3.expected,
    Slot3.Left5.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot5.Left0.expected,
    Slot6.Left0.expected,
    Slot6.Left3.expected,
    Slot6.Left5.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot8.Left0.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left2.expected,
    Slot9.Left3.expected,
    Slot9.Left4.expected,
    Slot9.Left5.expected,
    Slot9.Left6.expected,
    Slot9.Left7.expected,
    Slot9.Left8.expected,
    Slot9.Left9.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot11.Left0.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1360523455121301703099215249408 }, { target := 1, numerator := 72303435419511741680826974208 }, { target := 2, numerator := 4061990753905154027012751360 }, { target := 3, numerator := 4957295752911672760673153056768 }, { target := 4, numerator := 109809150047235997196911378432 }, { target := 5, numerator := 1360523228447710525356244992000 }, { target := 6, numerator := 109809150047235997196911378432 }, { target := 7, numerator := 109809150047235997196911378432 }, { target := 8, numerator := 72303435419511741680826974208 }, { target := 9, numerator := 4061990753905154027012751360 }, { target := 10, numerator := 4016342083301091293208172822528 }, { target := 11, numerator := 41857847578336920545026637824 }, { target := 12, numerator := 4016341705511772663636555726848 }, { target := 13, numerator := 41857847578336920545026637824 }, { target := 14, numerator := 1666976294814760449937669881856 }, { target := 15, numerator := 41857847578336920545026637824 }, { target := 17, numerator := 41857847578336920545026637824 }, { target := 19, numerator := 72303435419511741680826974208 }, { target := 20, numerator := 4061990753905154027012751360 }, { target := 21, numerator := 4016341724401238595115136581632 }, { target := 22, numerator := 41857847578336920545026637824 }, { target := 23, numerator := 4016341346611919965543519485952 }, { target := 24, numerator := 41857847578336920545026637824 }, { target := 25, numerator := 6008181491046672839330311962624 }, { target := 26, numerator := 109809150047235997196911378432 }, { target := 27, numerator := 1666976063418802789325054410752 }, { target := 32, numerator := 109809150047235997196911378432 }, { target := 33, numerator := 109809150047235997196911378432 }, { target := 34, numerator := 72303435419511741680826974208 }, { target := 35, numerator := 4061990753905154027012751360 }]

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
    Slot12.Left3.expected,
    Slot13.Left0.expected,
    Slot14.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 292247711027563261944460738560 }, { target := 3, numerator := 1000067828230160227981957529600 }, { target := 5, numerator := 292247711027563261944460738560 }, { target := 28, numerator := 41857847578336920545026637824 }, { target := 30, numerator := 41857847578336920545026637824 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk22.Parent3
