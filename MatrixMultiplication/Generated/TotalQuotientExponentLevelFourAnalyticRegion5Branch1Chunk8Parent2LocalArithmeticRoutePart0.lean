import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk8Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 81; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk8.Parent2

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
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 401896477616815563757060096 }, { target := 37, numerator := 14025642285224556819990446080 }, { target := 40, numerator := 14025671430749741658423689216 }, { target := 47, numerator := 401903505619142064237182976 }, { target := 86, numerator := 401896477616815563757060096 }, { target := 89, numerator := 1401956068295277034822696960 }, { target := 91, numerator := 401771221210521025283883008 }, { target := 145, numerator := 1401956068295277034822696960 }, { target := 147, numerator := 48976316435696288941641564160 }, { target := 150, numerator := 48976418723973041571674193920 }, { target := 157, numerator := 1401979780698700561766154240 }, { target := 161, numerator := 14025642285224556819990446080 }, { target := 164, numerator := 48976316435696288941641564160 }, { target := 166, numerator := 14020480856524737945498812416 }, { target := 216, numerator := 401771221210521025283883008 }, { target := 218, numerator := 14020480856524737945498812416 }, { target := 221, numerator := 14020509983183218044970205184 }, { target := 228, numerator := 401778259736633955022012416 }, { target := 232, numerator := 14025671430749741658423689216 }, { target := 235, numerator := 48976418723973041571674193920 }, { target := 237, numerator := 14020509983183218044970205184 }, { target := 406, numerator := 401903505619142064237182976 }, { target := 409, numerator := 1401979780698700561766154240 }, { target := 411, numerator := 401778259736633955022012416 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk8.Parent2
