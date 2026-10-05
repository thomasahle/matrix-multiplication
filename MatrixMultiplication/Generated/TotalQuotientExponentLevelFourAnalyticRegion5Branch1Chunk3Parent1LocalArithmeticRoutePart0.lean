import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk3Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 53; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk3.Parent1

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
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected,
    Slot20.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 2088478578929875405689061376 }, { target := 21, numerator := 77139766576291922944374865920 }, { target := 24, numerator := 77139372259813688486075039744 }, { target := 31, numerator := 2088684001660774002722865152 }, { target := 35, numerator := 16228379206963260201935831040 }, { target := 38, numerator := 55367340216618039744166625280 }, { target := 40, numerator := 16236372871246836353470562304 }, { target := 71, numerator := 2088478578929875405689061376 }, { target := 73, numerator := 2088478187000740134051119104 }, { target := 90, numerator := 1666592866071626856796258304 }, { target := 92, numerator := 57754526658757510977548189696 }, { target := 95, numerator := 57754399154311908442681376768 }, { target := 102, numerator := 1666663701491182807902322688 }, { target := 106, numerator := 55367340216618039744166625280 }, { target := 109, numerator := 188899479776148116286335877120 }, { target := 111, numerator := 55394661680149199415360356352 }, { target := 116, numerator := 77139766576291922944374865920 }, { target := 118, numerator := 77139790580965451488781402112 }, { target := 140, numerator := 16236372871246836353470562304 }, { target := 143, numerator := 55394661680149199415360356352 }, { target := 145, numerator := 16244366566446498046996905984 }, { target := 150, numerator := 77139372259813688486075039744 }, { target := 152, numerator := 77139396262241046716330541056 }, { target := 232, numerator := 2088684001660774002722865152 }, { target := 234, numerator := 2088683610153851196150906880 }]

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

namespace RouteChunk1

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot20.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 90, numerator := 421885320929113277254860800 }, { target := 92, numerator := 19385263922207940511233212416 }, { target := 95, numerator := 19384997107929138273649164288 }, { target := 102, numerator := 422019908662668388248584192 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk3.Parent1
