import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk0Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 20; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk0.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
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
  [{ target := 56, numerator := 2243197707587489449902080 }, { target := 57, numerator := 64421029790746594970173440 }, { target := 59, numerator := 667870295953911433501081600 }, { target := 67, numerator := 64418021222940024986664960 }, { target := 74, numerator := 2244152808478464047841280 }, { target := 110, numerator := 2243197707587489449902080 }, { target := 112, numerator := 108668861018191648306233344 }, { target := 115, numerator := 108668094158194948586864640 }, { target := 122, numerator := 2243567915861758279942144 }, { target := 152, numerator := 108668861018191648306233344 }, { target := 153, numerator := 3120794885488883687586004992 }, { target := 155, numerator := 32354127379725614624674938880 }, { target := 163, numerator := 3120649139246486010753712128 }, { target := 170, numerator := 108715129666571863173627904 }, { target := 206, numerator := 64421029790746594970173440 }, { target := 208, numerator := 3120794885488883687586004992 }, { target := 211, numerator := 3120772862503336927580651520 }, { target := 218, numerator := 64431661576872617041723392 }, { target := 283, numerator := 108668094158194948586864640 }, { target := 284, numerator := 3120772862503336927580651520 }, { target := 286, numerator := 32353899061458696512785612800 }, { target := 294, numerator := 3120627117289448815649095680 }, { target := 301, numerator := 108714362480064190469898240 }, { target := 302, numerator := 667870295953911433501081600 }, { target := 304, numerator := 32354127379725614624674938880 }, { target := 307, numerator := 32353899061458696512785612800 }, { target := 314, numerator := 667980518565527073723514880 }, { target := 660, numerator := 2243567915861758279942144 }, { target := 661, numerator := 64431661576872617041723392 }, { target := 663, numerator := 667980518565527073723514880 }, { target := 671, numerator := 64428652512544188140617728 }, { target := 678, numerator := 2244523174378719835848704 }, { target := 679, numerator := 64418021222940024986664960 }, { target := 681, numerator := 3120649139246486010753712128 }, { target := 684, numerator := 3120627117289448815649095680 }, { target := 691, numerator := 64428652512544188140617728 }, { target := 966, numerator := 2244152808478464047841280 }, { target := 968, numerator := 108715129666571863173627904 }, { target := 971, numerator := 108714362480064190469898240 }, { target := 978, numerator := 2244523174378719835848704 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk0.Parent1
