import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk20Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 85; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot0.Left3.expected,
    Slot0.Left5.expected,
    Slot1.Left0.expected,
    Slot1.Left2.expected,
    Slot2.Left0.expected,
    Slot2.Left3.expected,
    Slot2.Left5.expected,
    Slot3.Left0.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot5.Left0.expected,
    Slot5.Left3.expected,
    Slot5.Left5.expected,
    Slot6.Left0.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot9.Left0.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left2.expected,
    Slot14.Left3.expected,
    Slot14.Left4.expected,
    Slot14.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 8085359279352672445421898956800 }, { target := 1, numerator := 32495926031241232216102010880 }, { target := 2, numerator := 1682824740903563811190996992 }, { target := 3, numerator := 29339967320703094636638380228608 }, { target := 4, numerator := 45262182686371716300999229440 }, { target := 5, numerator := 8085121092632009466256610557952 }, { target := 6, numerator := 45320211125713218501385125888 }, { target := 7, numerator := 45320211125713218501385125888 }, { target := 8, numerator := 32437897591899730015716114432 }, { target := 9, numerator := 1682824740903563811190996992 }, { target := 10, numerator := 23896730108024250227790557741056 }, { target := 11, numerator := 10367744121219500986660290560 }, { target := 12, numerator := 23896730301641912158893377585152 }, { target := 13, numerator := 10367744121219500986660290560 }, { target := 14, numerator := 8170731037599391428043717214208 }, { target := 19, numerator := 32495926031241232216102010880 }, { target := 20, numerator := 1682824740903563811190996992 }, { target := 21, numerator := 23896730280059221592653202194432 }, { target := 22, numerator := 10367751536810618617900040192 }, { target := 23, numerator := 23896730473675611256861289873408 }, { target := 24, numerator := 10367751536810618617900040192 }, { target := 25, numerator := 29644553975609852957081286475776 }, { target := 26, numerator := 45262182686371716300999229440 }, { target := 27, numerator := 8170531654564118188753149755392 }]

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
    Slot14.Left6.expected,
    Slot14.Left7.expected,
    Slot14.Left8.expected,
    Slot14.Left9.expected,
    Slot15.Left0.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected,
    Slot16.Left2.expected,
    Slot16.Left3.expected,
    Slot17.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 113347453970023321917951311872 }, { target := 3, numerator := 407101524347758274771257655296 }, { target := 5, numerator := 113376321796333104059142635520 }, { target := 10, numerator := 9439289423796859107257876480 }, { target := 12, numerator := 9439296175305190084953767936 }, { target := 15, numerator := 10367744121219500986660290560 }, { target := 17, numerator := 10367751536810618617900040192 }, { target := 21, numerator := 9439289423796859107257876480 }, { target := 23, numerator := 9439296175305190084953767936 }, { target := 28, numerator := 10367744121219500986660290560 }, { target := 30, numerator := 10367751536810618617900040192 }, { target := 32, numerator := 45320211125713218501385125888 }, { target := 33, numerator := 45320211125713218501385125888 }, { target := 34, numerator := 32437897591899730015716114432 }, { target := 35, numerator := 1682824740903563811190996992 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20.Parent3
