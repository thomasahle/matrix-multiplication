import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk11Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 86; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk11.Parent1

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
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 420722358476311572057686016 }, { target := 21, numerator := 19386448135336936727598071808 }, { target := 24, numerator := 19386417439808431087014641664 }, { target := 31, numerator := 420682218169804195910123520 }, { target := 35, numerator := 4912411035584053165749698560 }, { target := 38, numerator := 18086094445978898440118075392 }, { target := 40, numerator := 4911898802749231975540719616 }, { target := 71, numerator := 420722358476311572057686016 }, { target := 73, numerator := 420718346174367551409094656 }, { target := 90, numerator := 420718346174367551409094656 }, { target := 92, numerator := 19386263252641795990385328128 }, { target := 95, numerator := 19386232557406024325580980224 }, { target := 102, numerator := 420678206250666143588024320 }, { target := 106, numerator := 18086094445978898440118075392 }, { target := 109, numerator := 66468319370622821288642609152 }, { target := 111, numerator := 18084110790752176259511353344 }, { target := 116, numerator := 19386448135336936727598071808 }, { target := 118, numerator := 19386263252641795990385328128 }, { target := 140, numerator := 4911898802749231975540719616 }, { target := 143, numerator := 18084110790752176259511353344 }, { target := 145, numerator := 4911386543361187382355296256 }, { target := 150, numerator := 19386417439808431087014641664 }, { target := 152, numerator := 19386232557406024325580980224 }, { target := 232, numerator := 420682218169804195910123520 }, { target := 234, numerator := 420678206250666143588024320 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk11.Parent1
