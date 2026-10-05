import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk3Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 42; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk3.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 1621059767330155264403832832 }, { target := 21, numerator := 57800140037536662469839159296 }, { target := 24, numerator := 57798107052060208717396705280 }, { target := 31, numerator := 1623017194699688722644860928 }, { target := 35, numerator := 19952136687573587245599293440 }, { target := 38, numerator := 65307971954493628562007916544 }, { target := 40, numerator := 19921429205777915606820978688 }, { target := 71, numerator := 1621059767330155264403832832 }, { target := 73, numerator := 1621057329651585308833087488 }, { target := 90, numerator := 1621057329651585308833087488 }, { target := 92, numerator := 57800062194741829261563265024 }, { target := 95, numerator := 57798029222676532249476726784 }, { target := 102, numerator := 1623014744096350786474213376 }, { target := 106, numerator := 65307971954493628562007916544 }, { target := 109, numerator := 213878409743023522716768534528 }, { target := 111, numerator := 65208505119583557684572454912 }, { target := 116, numerator := 57800140037536662469839159296 }, { target := 118, numerator := 57800062194741829261563265024 }, { target := 140, numerator := 19921429205777915606820978688 }, { target := 143, numerator := 65208505119583557684572454912 }, { target := 145, numerator := 19890778609543049485637124096 }, { target := 150, numerator := 57798107052060208717396705280 }, { target := 152, numerator := 57798029222676532249476726784 }, { target := 232, numerator := 1623017194699688722644860928 }, { target := 234, numerator := 1623014744096350786474213376 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk3.Parent0
