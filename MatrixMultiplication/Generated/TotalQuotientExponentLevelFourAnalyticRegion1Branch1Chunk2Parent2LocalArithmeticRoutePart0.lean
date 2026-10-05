import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk2Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 11; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2.Parent2

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
    Slot0.Left2.expected,
    Slot0.Left3.expected,
    Slot0.Left4.expected,
    Slot0.Left5.expected,
    Slot0.Left6.expected,
    Slot0.Left7.expected,
    Slot0.Left8.expected,
    Slot0.Left9.expected,
    Slot0.Left10.expected,
    Slot0.Left11.expected,
    Slot0.Left12.expected,
    Slot0.Left13.expected,
    Slot0.Left14.expected,
    Slot0.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 3, numerator := 227278054087550284844761088 }, { target := 4, numerator := 227278054087550284844761088 }, { target := 5, numerator := 227278054087550284844761088 }, { target := 6, numerator := 227278054087550284844761088 }, { target := 9, numerator := 169249614746048084458864640 }, { target := 10, numerator := 169249614746048084458864640 }, { target := 11, numerator := 169249614746048084458864640 }, { target := 12, numerator := 169249614746048084458864640 }, { target := 14, numerator := 178921021302965117856514048 }, { target := 15, numerator := 178921021302965117856514048 }, { target := 16, numerator := 178921021302965117856514048 }, { target := 17, numerator := 178921021302965117856514048 }, { target := 30, numerator := 232113757366008801543585792 }, { target := 31, numerator := 232113757366008801543585792 }, { target := 32, numerator := 232113757366008801543585792 }, { target := 33, numerator := 232113757366008801543585792 }, { target := 36, numerator := 3109357208048826237344284672 }, { target := 37, numerator := 3109357208048826237344284672 }, { target := 38, numerator := 3109357208048826237344284672 }, { target := 39, numerator := 3109357208048826237344284672 }, { target := 41, numerator := 5623922912847254920733130752 }, { target := 42, numerator := 5623922912847254920733130752 }, { target := 43, numerator := 5623922912847254920733130752 }, { target := 44, numerator := 5623922912847254920733130752 }, { target := 56, numerator := 169249614746048084458864640 }, { target := 57, numerator := 169249614746048084458864640 }, { target := 58, numerator := 169249614746048084458864640 }, { target := 59, numerator := 169249614746048084458864640 }, { target := 61, numerator := 3109357208048826237344284672 }, { target := 62, numerator := 3109357208048826237344284672 }, { target := 63, numerator := 3109357208048826237344284672 }, { target := 64, numerator := 3109357208048826237344284672 }, { target := 75, numerator := 183756724581423634555338752 }, { target := 76, numerator := 183756724581423634555338752 }, { target := 77, numerator := 183756724581423634555338752 }, { target := 78, numerator := 183756724581423634555338752 }, { target := 107, numerator := 183756724581423634555338752 }, { target := 108, numerator := 183756724581423634555338752 }, { target := 109, numerator := 183756724581423634555338752 }, { target := 110, numerator := 183756724581423634555338752 }, { target := 112, numerator := 178921021302965117856514048 }, { target := 113, numerator := 178921021302965117856514048 }, { target := 114, numerator := 178921021302965117856514048 }, { target := 115, numerator := 178921021302965117856514048 }, { target := 127, numerator := 178921021302965117856514048 }, { target := 128, numerator := 178921021302965117856514048 }, { target := 129, numerator := 178921021302965117856514048 }, { target := 130, numerator := 178921021302965117856514048 }, { target := 132, numerator := 5623922912847254920733130752 }, { target := 133, numerator := 5623922912847254920733130752 }, { target := 134, numerator := 5623922912847254920733130752 }, { target := 135, numerator := 5623922912847254920733130752 }, { target := 146, numerator := 178921021302965117856514048 }, { target := 147, numerator := 178921021302965117856514048 }, { target := 148, numerator := 178921021302965117856514048 }, { target := 149, numerator := 178921021302965117856514048 }, { target := 177, numerator := 227278054087550284844761088 }, { target := 178, numerator := 227278054087550284844761088 }, { target := 179, numerator := 227278054087550284844761088 }, { target := 180, numerator := 227278054087550284844761088 }, { target := 191, numerator := 232113757366008801543585792 }, { target := 192, numerator := 232113757366008801543585792 }, { target := 193, numerator := 232113757366008801543585792 }, { target := 194, numerator := 232113757366008801543585792 }]

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
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot3.Left0.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left3.expected,
    Slot4.Left11.expected,
    Slot4.Left18.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left6.expected,
    Slot5.Left14.expected,
    Slot7.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 117841933213529126662569984 }, { target := 1, numerator := 19312023284365756708505518080 }, { target := 3, numerator := 49876910757364299647156224 }, { target := 4, numerator := 49731355570329189823283200 }, { target := 5, numerator := 49391726800580600234246144 }, { target := 6, numerator := 49731355570329189823283200 }, { target := 7, numerator := 198824757107634441110295674880 }, { target := 9, numerator := 9892329029753346033136435200 }, { target := 10, numerator := 9863460365269630042767360000 }, { target := 11, numerator := 9796100148140959398572851200 }, { target := 12, numerator := 9863460365269630042767360000 }, { target := 55, numerator := 19312023284365756708505518080 }, { target := 56, numerator := 9892329029753346033136435200 }, { target := 57, numerator := 9863460365269630042767360000 }, { target := 58, numerator := 9796100148140959398572851200 }, { target := 59, numerator := 9863460365269630042767360000 }, { target := 89, numerator := 277154964844914584491917312 }, { target := 90, numerator := 10061578644499394117595299840 }, { target := 91, numerator := 178921021302965117856514048 }, { target := 92, numerator := 232113757366008801543585792 }, { target := 93, numerator := 3109357208048826237344284672 }, { target := 94, numerator := 5623922912847254920733130752 }, { target := 95, numerator := 10061578644499394117595299840 }, { target := 96, numerator := 3109357208048826237344284672 }, { target := 97, numerator := 183756724581423634555338752 }, { target := 98, numerator := 183756724581423634555338752 }, { target := 99, numerator := 178921021302965117856514048 }, { target := 100, numerator := 178921021302965117856514048 }, { target := 101, numerator := 5623922912847254920733130752 }, { target := 102, numerator := 178921021302965117856514048 }, { target := 103, numerator := 277154964844914584491917312 }, { target := 104, numerator := 232113757366008801543585792 }, { target := 160, numerator := 49731355570329189823283200 }, { target := 161, numerator := 9863460365269630042767360000 }, { target := 166, numerator := 9863460365269630042767360000 }, { target := 174, numerator := 49731355570329189823283200 }, { target := 176, numerator := 117841933213529126662569984 }, { target := 177, numerator := 49876910757364299647156224 }, { target := 178, numerator := 49731355570329189823283200 }, { target := 179, numerator := 49391726800580600234246144 }, { target := 180, numerator := 49731355570329189823283200 }, { target := 205, numerator := 49391726800580600234246144 }, { target := 206, numerator := 9796100148140959398572851200 }, { target := 211, numerator := 9796100148140959398572851200 }, { target := 219, numerator := 49391726800580600234246144 }, { target := 231, numerator := 49731355570329189823283200 }, { target := 232, numerator := 9863460365269630042767360000 }, { target := 237, numerator := 9863460365269630042767360000 }, { target := 245, numerator := 49731355570329189823283200 }, { target := 247, numerator := 117841933213529126662569984 }, { target := 248, numerator := 19312023284365756708505518080 }, { target := 250, numerator := 198824757107634441110295674880 }, { target := 258, numerator := 19312023284365756708505518080 }, { target := 265, numerator := 117841933213529126662569984 }]

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
    Slot7.Left1.expected,
    Slot7.Left2.expected,
    Slot7.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 160, numerator := 227278054087550284844761088 }, { target := 161, numerator := 169249614746048084458864640 }, { target := 162, numerator := 178921021302965117856514048 }, { target := 163, numerator := 232113757366008801543585792 }, { target := 164, numerator := 3109357208048826237344284672 }, { target := 165, numerator := 5623922912847254920733130752 }, { target := 166, numerator := 169249614746048084458864640 }, { target := 167, numerator := 3109357208048826237344284672 }, { target := 168, numerator := 183756724581423634555338752 }, { target := 169, numerator := 183756724581423634555338752 }, { target := 170, numerator := 178921021302965117856514048 }, { target := 171, numerator := 178921021302965117856514048 }, { target := 172, numerator := 5623922912847254920733130752 }, { target := 173, numerator := 178921021302965117856514048 }, { target := 174, numerator := 227278054087550284844761088 }, { target := 175, numerator := 232113757366008801543585792 }, { target := 205, numerator := 227278054087550284844761088 }, { target := 206, numerator := 169249614746048084458864640 }, { target := 207, numerator := 178921021302965117856514048 }, { target := 208, numerator := 232113757366008801543585792 }, { target := 209, numerator := 3109357208048826237344284672 }, { target := 210, numerator := 5623922912847254920733130752 }, { target := 211, numerator := 169249614746048084458864640 }, { target := 212, numerator := 3109357208048826237344284672 }, { target := 213, numerator := 183756724581423634555338752 }, { target := 214, numerator := 183756724581423634555338752 }, { target := 215, numerator := 178921021302965117856514048 }, { target := 216, numerator := 178921021302965117856514048 }, { target := 217, numerator := 5623922912847254920733130752 }, { target := 218, numerator := 178921021302965117856514048 }, { target := 219, numerator := 227278054087550284844761088 }, { target := 220, numerator := 232113757366008801543585792 }, { target := 231, numerator := 227278054087550284844761088 }, { target := 232, numerator := 169249614746048084458864640 }, { target := 233, numerator := 178921021302965117856514048 }, { target := 234, numerator := 232113757366008801543585792 }, { target := 235, numerator := 3109357208048826237344284672 }, { target := 236, numerator := 5623922912847254920733130752 }, { target := 237, numerator := 169249614746048084458864640 }, { target := 238, numerator := 3109357208048826237344284672 }, { target := 239, numerator := 183756724581423634555338752 }, { target := 240, numerator := 183756724581423634555338752 }, { target := 241, numerator := 178921021302965117856514048 }, { target := 242, numerator := 178921021302965117856514048 }, { target := 243, numerator := 5623922912847254920733130752 }, { target := 244, numerator := 178921021302965117856514048 }, { target := 245, numerator := 227278054087550284844761088 }, { target := 246, numerator := 232113757366008801543585792 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2.Parent2
