import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk9Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 82; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk9.Parent3

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
    Slot10.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 7996451464558139146240000 }, { target := 82, numerator := 390054472478026987313561600 }, { target := 85, numerator := 389909060886577146337689600 }, { target := 92, numerator := 7994885858516427970969600 }, { target := 176, numerator := 390054472478026987313561600 }, { target := 178, numerator := 19026250853198777959573356544 }, { target := 181, numerator := 19019157901800705264728408064 }, { target := 188, numerator := 389978104648944964824203264 }, { target := 286, numerator := 389909060886577146337689600 }, { target := 288, numerator := 19019157901800705264728408064 }, { target := 291, numerator := 19012067594641895659545821184 }, { target := 298, numerator := 389832721527281643247632384 }, { target := 573, numerator := 7994885858516427970969600 }, { target := 575, numerator := 389978104648944964824203264 }, { target := 578, numerator := 389832721527281643247632384 }, { target := 585, numerator := 7993320559000966433603584 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk9.Parent3
