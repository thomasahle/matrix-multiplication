import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk3Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 46; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk3.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left5.expected,
    Slot6.Left12.expected,
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 894366668776356891223654400 }, { target := 21, numerator := 38718404131967001003336663040 }, { target := 24, numerator := 38727485090612081741015285760 }, { target := 31, numerator := 885304598976836783455600640 }, { target := 35, numerator := 12801286280056807447534239744 }, { target := 38, numerator := 45606853902278828974137147392 }, { target := 40, numerator := 12804277463905765386144972800 }, { target := 71, numerator := 894366668776356891223654400 }, { target := 73, numerator := 894418531269836019272253440 }, { target := 90, numerator := 894418531269836019272253440 }, { target := 92, numerator := 38720954292785212201130524672 }, { target := 95, numerator := 38730035555633248118943776768 }, { target := 102, numerator := 885356158508102428710141952 }, { target := 106, numerator := 45606853902278828974137147392 }, { target := 109, numerator := 162475147845362474817649901568 }, { target := 111, numerator := 45617423636675122453825978368 }, { target := 116, numerator := 38718404131967001003336663040 }, { target := 118, numerator := 38720954292785212201130524672 }, { target := 140, numerator := 12804277463905765386144972800 }, { target := 143, numerator := 45617423636675122453825978368 }, { target := 145, numerator := 12807268440182972074319413248 }, { target := 150, numerator := 38727485090612081741015285760 }, { target := 152, numerator := 38730035555633248118943776768 }, { target := 232, numerator := 885304598976836783455600640 }, { target := 234, numerator := 885356158508102428710141952 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk3.Parent2
