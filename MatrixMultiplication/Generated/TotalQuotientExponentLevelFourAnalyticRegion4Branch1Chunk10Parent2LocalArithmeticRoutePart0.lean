import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk10Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 81; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk10.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 89182114286500527451668480 }, { target := 17, numerator := 3030980595705831945255518208 }, { target := 19, numerator := 33373819589006357973904130048 }, { target := 27, numerator := 3031027819488880131926130688 }, { target := 34, numerator := 89170308340738480784015360 }, { target := 35, numerator := 741840594908238455106437120 }, { target := 37, numerator := 28319868812301715324587212800 }, { target := 40, numerator := 28323992442987863466752081920 }, { target := 47, numerator := 737751504939720401150279680 }, { target := 86, numerator := 741840594908238455106437120 }, { target := 89, numerator := 2559563030030101799753482240 }, { target := 91, numerator := 741962115558375891430014976 }, { target := 122, numerator := 89182114286500527451668480 }, { target := 124, numerator := 89181667771485972269629440 }, { target := 126, numerator := 89181667771485972269629440 }, { target := 127, numerator := 3030965420259996917273985024 }, { target := 129, numerator := 33373652493713105850460012544 }, { target := 137, numerator := 3031012643806606123507646464 }, { target := 144, numerator := 89169861884833670711214080 }, { target := 145, numerator := 2559563030030101799753482240 }, { target := 147, numerator := 97768243032470017864198258688 }, { target := 150, numerator := 97782534673793093133941080064 }, { target := 157, numerator := 2545391193545378633237921792 }, { target := 161, numerator := 28319868812301715324587212800 }, { target := 164, numerator := 97768243032470017864198258688 }, { target := 166, numerator := 28324752995930568459108220928 }, { target := 197, numerator := 3030980595705831945255518208 }, { target := 199, numerator := 3030965420259996917273985024 }, { target := 216, numerator := 528291446783768147464814592 }, { target := 218, numerator := 21218712242381385942423306240 }, { target := 221, numerator := 21222836825594899347120586752 }, { target := 228, numerator := 524203157828576042368892928 }, { target := 232, numerator := 28323992442987863466752081920 }, { target := 235, numerator := 97782534673793093133941080064 }, { target := 237, numerator := 28328877579144081863805501440 }, { target := 242, numerator := 33373819589006357973904130048 }, { target := 244, numerator := 33373652493713105850460012544 }, { target := 406, numerator := 737751504939720401150279680 }, { target := 409, numerator := 2545391193545378633237921792 }, { target := 411, numerator := 737872081448195081105309696 }, { target := 416, numerator := 3031027819488880131926130688 }, { target := 418, numerator := 3031012643806606123507646464 }, { target := 498, numerator := 89170308340738480784015360 }, { target := 500, numerator := 89169861884833670711214080 }]

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
    Slot16.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 216, numerator := 213670668774607743965200384 }, { target := 218, numerator := 7106040753549182516684914688 }, { target := 221, numerator := 7106040753549182516684914688 }, { target := 228, numerator := 213668923619619038736416768 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk10.Parent2
