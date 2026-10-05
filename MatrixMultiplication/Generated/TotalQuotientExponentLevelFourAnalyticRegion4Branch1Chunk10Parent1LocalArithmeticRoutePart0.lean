import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk10Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 80; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk10.Parent1

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
  [{ target := 19, numerator := 1540517855912005196117442560 }, { target := 21, numerator := 57880533194369788272678273024 }, { target := 24, numerator := 57888046462426619736240422912 }, { target := 31, numerator := 1533065978457884401311154176 }, { target := 35, numerator := 18671904915617048147106201600 }, { target := 38, numerator := 64413454218527083351146233856 }, { target := 40, numerator := 18674965867856428048209412096 }, { target := 71, numerator := 1540517855912005196117442560 }, { target := 73, numerator := 1540519320339051778880307200 }, { target := 90, numerator := 1540519320339051778880307200 }, { target := 92, numerator := 57880612010011383837252124672 }, { target := 95, numerator := 57888125312103043584759955456 }, { target := 102, numerator := 1533067409173235973392171008 }, { target := 106, numerator := 64413454218527083351146233856 }, { target := 109, numerator := 222222239081817133446890258432 }, { target := 111, numerator := 64424062951056220110855340032 }, { target := 116, numerator := 57880533194369788272678273024 }, { target := 118, numerator := 57880612010011383837252124672 }, { target := 140, numerator := 18674965867856428048209412096 }, { target := 143, numerator := 64424062951056220110855340032 }, { target := 145, numerator := 18678027527536718540389220352 }, { target := 150, numerator := 57888046462426619736240422912 }, { target := 152, numerator := 57888125312103043584759955456 }, { target := 232, numerator := 1533065978457884401311154176 }, { target := 234, numerator := 1533067409173235973392171008 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk10.Parent1
