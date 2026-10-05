import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk0Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 20; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk0.Parent1

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
    Slot11.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 2211166768342641246470144 }, { target := 57, numerator := 94277193169443760407314432 }, { target := 59, numerator := 904963453677331752119435264 }, { target := 67, numerator := 94277978477873383696498688 }, { target := 74, numerator := 2210970441235235424174080 }, { target := 110, numerator := 2211166768342641246470144 }, { target := 112, numerator := 77568397488492013997260800 }, { target := 115, numerator := 77568140705626160306847744 }, { target := 122, numerator := 2211613760738756929781760 }, { target := 152, numerator := 77568397488492013997260800 }, { target := 153, numerator := 3307272386039020784084582400 }, { target := 155, numerator := 31746391042235569783229644800 }, { target := 163, numerator := 3307299934895711381461401600 }, { target := 170, numerator := 77561510274319364653056000 }, { target := 206, numerator := 94277193169443760407314432 }, { target := 208, numerator := 3307272386039020784084582400 }, { target := 211, numerator := 3307261437625634109870047232 }, { target := 218, numerator := 94296251518672415521505280 }, { target := 283, numerator := 77568140705626160306847744 }, { target := 284, numerator := 3307261437625634109870047232 }, { target := 286, numerator := 31746285948801435777959460864 }, { target := 294, numerator := 3307288986391126814792613888 }, { target := 301, numerator := 77561253514252984076206080 }, { target := 302, numerator := 904963453677331752119435264 }, { target := 304, numerator := 31746391042235569783229644800 }, { target := 307, numerator := 31746285948801435777959460864 }, { target := 314, numerator := 905146394099713168700866560 }, { target := 660, numerator := 2211613760738756929781760 }, { target := 661, numerator := 94296251518672415521505280 }, { target := 663, numerator := 905146394099713168700866560 }, { target := 671, numerator := 94297036985853925675499520 }, { target := 678, numerator := 2211417393943379391283200 }, { target := 679, numerator := 94277978477873383696498688 }, { target := 681, numerator := 3307299934895711381461401600 }, { target := 684, numerator := 3307288986391126814792613888 }, { target := 691, numerator := 94297036985853925675499520 }, { target := 966, numerator := 2210970441235235424174080 }, { target := 968, numerator := 77561510274319364653056000 }, { target := 971, numerator := 77561253514252984076206080 }, { target := 978, numerator := 2211417393943379391283200 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk0.Parent1
