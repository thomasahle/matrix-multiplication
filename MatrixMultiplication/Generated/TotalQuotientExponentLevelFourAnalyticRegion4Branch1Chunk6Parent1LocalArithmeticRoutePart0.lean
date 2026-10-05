import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk6Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 58; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk6.Parent1

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
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 1701817558807983811461120 }, { target := 35, numerator := 87479658849100321951580160 }, { target := 40, numerator := 87499996544882323457310720 }, { target := 48, numerator := 1682309105195870500945920 }, { target := 79, numerator := 57838682559236646950141952 }, { target := 80, numerator := 2973120233938259544046043136 }, { target := 85, numerator := 2973811439364031175681114112 }, { target := 93, numerator := 57175660104301495852204032 }, { target := 121, numerator := 1701817558807983811461120 }, { target := 122, numerator := 57838682559236646950141952 }, { target := 124, numerator := 636855861014926486679846912 }, { target := 132, numerator := 57839583707004085649539072 }, { target := 139, numerator := 1701592271866124136611840 }, { target := 154, numerator := 636855861014926486679846912 }, { target := 155, numerator := 32736725020429642739446972416 }, { target := 160, numerator := 32744335813191340647746895872 }, { target := 168, numerator := 629555388083553950490427392 }, { target := 196, numerator := 87479658849100321951580160 }, { target := 197, numerator := 2973120233938259544046043136 }, { target := 199, numerator := 32736725020429642739446972416 }, { target := 207, numerator := 2973166556235770319964471296 }, { target := 214, numerator := 87468078274722627971973120 }, { target := 492, numerator := 57839583707004085649539072 }, { target := 493, numerator := 2973166556235770319964471296 }, { target := 498, numerator := 2973857772430774560549240832 }, { target := 506, numerator := 57176550921937289270525952 }, { target := 508, numerator := 87499996544882323457310720 }, { target := 509, numerator := 2973811439364031175681114112 }, { target := 511, numerator := 32744335813191340647746895872 }, { target := 519, numerator := 2973857772430774560549240832 }, { target := 526, numerator := 87488413278196477240279040 }, { target := 890, numerator := 1701592271866124136611840 }, { target := 891, numerator := 87468078274722627971973120 }, { target := 896, numerator := 87488413278196477240279040 }, { target := 904, numerator := 1682086400786922146365440 }, { target := 906, numerator := 1682309105195870500945920 }, { target := 907, numerator := 57175660104301495852204032 }, { target := 909, numerator := 629555388083553950490427392 }, { target := 917, numerator := 57176550921937289270525952 }, { target := 924, numerator := 1682086400786922146365440 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk6.Parent1
