import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk2Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 35; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk2.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left3.expected,
    Slot12.Left11.expected,
    Slot12.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 1142036048728213633892352 }, { target := 35, numerator := 59202414725414416577200128 }, { target := 40, numerator := 59213363469815663403466752 }, { target := 48, numerator := 1131705958741229111869440 }, { target := 79, numerator := 57566133014425897403416576 }, { target := 80, numerator := 2984191334987776085840625664 }, { target := 85, numerator := 2984743223763305553803083776 }, { target := 93, numerator := 57045428492967082689822720 }, { target := 121, numerator := 1142036048728213633892352 }, { target := 122, numerator := 57566133014425897403416576 }, { target := 124, numerator := 632287407113096757409480704 }, { target := 132, numerator := 57566535186998521495552000 }, { target := 139, numerator := 1141901991204005603180544 }, { target := 154, numerator := 632287407113096757409480704 }, { target := 155, numerator := 32777372783680791352763744256 }, { target := 160, numerator := 32783434547857428035879829504 }, { target := 168, numerator := 626568160491775944692858880 }, { target := 196, numerator := 59202414725414416577200128 }, { target := 197, numerator := 2984191334987776085840625664 }, { target := 199, numerator := 32777372783680791352763744256 }, { target := 207, numerator := 2984212183355445559164928000 }, { target := 214, numerator := 59195465269524592135766016 }, { target := 492, numerator := 57566535186998521495552000 }, { target := 493, numerator := 2984212183355445559164928000 }, { target := 498, numerator := 2984764075986619258109952000 }, { target := 506, numerator := 57045827027757107773440000 }, { target := 508, numerator := 59213363469815663403466752 }, { target := 509, numerator := 2984743223763305553803083776 }, { target := 511, numerator := 32783434547857428035879829504 }, { target := 519, numerator := 2984764075986619258109952000 }, { target := 526, numerator := 59206412728711095301177344 }, { target := 890, numerator := 1141901991204005603180544 }, { target := 891, numerator := 59195465269524592135766016 }, { target := 896, numerator := 59206412728711095301177344 }, { target := 904, numerator := 1131573113811220750663680 }, { target := 906, numerator := 1131705958741229111869440 }, { target := 907, numerator := 57045428492967082689822720 }, { target := 909, numerator := 626568160491775944692858880 }, { target := 917, numerator := 57045827027757107773440000 }, { target := 924, numerator := 1131573113811220750663680 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk2.Parent0
