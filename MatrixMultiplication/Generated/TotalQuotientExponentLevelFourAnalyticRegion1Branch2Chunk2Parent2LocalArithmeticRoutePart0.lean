import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk2Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 11; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk2.Parent2

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
    Slot0.Left15.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot3.Left0.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot4.Left5.expected,
    Slot4.Left12.expected,
    Slot5.Left0.expected,
    Slot5.Left3.expected,
    Slot5.Left5.expected,
    Slot7.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 4229856715271721305424003072 }, { target := 1, numerator := 909112216350201139379044352 }, { target := 2, numerator := 116256512003701232153556680704 }, { target := 3, numerator := 22495691651389019682932523008 }, { target := 4, numerator := 715684085211860471426056192 }, { target := 5, numerator := 116256568672099026589299245056 }, { target := 6, numerator := 735026898325694538221355008 }, { target := 7, numerator := 735026898325694538221355008 }, { target := 8, numerator := 12437428832195304949377138688 }, { target := 9, numerator := 676998458984192337835458560 }, { target := 10, numerator := 22495691651389019682932523008 }, { target := 11, numerator := 12437428832195304949377138688 }, { target := 12, numerator := 4229828381072824087552720896 }, { target := 13, numerator := 715684085211860471426056192 }, { target := 14, numerator := 676998458984192337835458560 }, { target := 15, numerator := 909112216350201139379044352 }, { target := 16, numerator := 3658633832937679312912384000 }, { target := 19, numerator := 12509116957549102061374668800 }, { target := 21, numerator := 3658632651193137090894233600 }, { target := 26, numerator := 3658633832937679312912384000 }, { target := 27, numerator := 3633648040907861015165665280 }, { target := 28, numerator := 3658633832937679312912384000 }, { target := 29, numerator := 3669342029521887154803834880 }, { target := 30, numerator := 3633648040907861015165665280 }, { target := 33, numerator := 12423688841741449657053085696 }, { target := 35, numerator := 3633646867233769325395443712 }, { target := 44, numerator := 4229856715271721305424003072 }, { target := 49, numerator := 909112216350201139379044352 }, { target := 50, numerator := 3658633832937679312912384000 }, { target := 53, numerator := 12509116957549102061374668800 }, { target := 55, numerator := 3658632651193137090894233600 }, { target := 60, numerator := 12509116957549102061374668800 }, { target := 61, numerator := 12423688841741449657053085696 }, { target := 62, numerator := 12509116957549102061374668800 }, { target := 63, numerator := 12545729007180953091798204416 }, { target := 64, numerator := 116256512003701232153556680704 }, { target := 69, numerator := 22495691651389019682932523008 }, { target := 70, numerator := 715684085211860471426056192 }, { target := 71, numerator := 3658632651193137090894233600 }, { target := 72, numerator := 3633646867233769325395443712 }, { target := 73, numerator := 3658632651193137090894233600 }, { target := 74, numerator := 3669340844318580418965143552 }, { target := 75, numerator := 116256568672099026589299245056 }, { target := 76, numerator := 735026898325694538221355008 }, { target := 77, numerator := 3669342029521887154803834880 }, { target := 80, numerator := 12545729007180953091798204416 }, { target := 82, numerator := 3669340844318580418965143552 }, { target := 91, numerator := 735026898325694538221355008 }, { target := 96, numerator := 12437428832195304949377138688 }, { target := 97, numerator := 676998458984192337835458560 }, { target := 102, numerator := 22495691651389019682932523008 }, { target := 103, numerator := 12437428832195304949377138688 }, { target := 104, numerator := 4229828381072824087552720896 }, { target := 109, numerator := 715684085211860471426056192 }, { target := 110, numerator := 676998458984192337835458560 }, { target := 111, numerator := 909112216350201139379044352 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk2.Parent2
