import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk3Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 47; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk3.Parent3

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
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left6.expected,
    Slot10.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 1322949302964058859765760 }, { target := 35, numerator := 59020868429452349458612224 }, { target := 40, numerator := 59022853878502772667580416 }, { target := 48, numerator := 1322848591780341740470272 }, { target := 79, numerator := 66685351684459136423034880 }, { target := 80, numerator := 2975040206848461248147750912 }, { target := 85, numerator := 2975140286547571716713873408 }, { target := 93, numerator := 66680275177982518452289536 }, { target := 121, numerator := 1322949302964058859765760 }, { target := 122, numerator := 66685351684459136423034880 }, { target := 124, numerator := 732449895469362160620011520 }, { target := 132, numerator := 66685817566359464181760000 }, { target := 139, numerator := 1322794008997282940190720 }, { target := 154, numerator := 732449895469362160620011520 }, { target := 155, numerator := 32676859812244667849609576448 }, { target := 160, numerator := 32677959054631495526705528832 }, { target := 168, numerator := 732394136797566553810796544 }, { target := 196, numerator := 59020868429452349458612224 }, { target := 197, numerator := 2975040206848461248147750912 }, { target := 199, numerator := 32676859812244667849609576448 }, { target := 207, numerator := 2975060991283874836250624000 }, { target := 214, numerator := 59013940284314486757654528 }, { target := 492, numerator := 66685817566359464181760000 }, { target := 493, numerator := 2975060991283874836250624000 }, { target := 498, numerator := 2975161071682169146966016000 }, { target := 506, numerator := 66680741024416999145472000 }, { target := 508, numerator := 59022853878502772667580416 }, { target := 509, numerator := 2975140286547571716713873408 }, { target := 511, numerator := 32677959054631495526705528832 }, { target := 519, numerator := 2975161071682169146966016000 }, { target := 526, numerator := 59015925500303629250199552 }, { target := 890, numerator := 1322794008997282940190720 }, { target := 891, numerator := 59013940284314486757654528 }, { target := 896, numerator := 59015925500303629250199552 }, { target := 904, numerator := 1322693309635514842742784 }, { target := 906, numerator := 1322848591780341740470272 }, { target := 907, numerator := 66680275177982518452289536 }, { target := 909, numerator := 732394136797566553810796544 }, { target := 917, numerator := 66680741024416999145472000 }, { target := 924, numerator := 1322693309635514842742784 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk3.Parent3
