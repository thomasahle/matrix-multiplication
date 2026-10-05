import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk23Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 96; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk23.Parent2

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
    Slot8.Left1.expected,
    Slot8.Left2.expected,
    Slot8.Left3.expected,
    Slot8.Left4.expected,
    Slot8.Left5.expected,
    Slot8.Left6.expected,
    Slot8.Left7.expected,
    Slot8.Left8.expected,
    Slot8.Left9.expected,
    Slot9.Left0.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left2.expected,
    Slot10.Left3.expected,
    Slot11.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 337763003112683825489623646208 }, { target := 1, numerator := 32495926031241232216102010880 }, { target := 2, numerator := 1682824740903563811190996992 }, { target := 3, numerator := 1259458564697034458985503129600 }, { target := 4, numerator := 45262182686371716300999229440 }, { target := 5, numerator := 337736742032672587392590282752 }, { target := 6, numerator := 45320211125713218501385125888 }, { target := 7, numerator := 45320211125713218501385125888 }, { target := 8, numerator := 32437897591899730015716114432 }, { target := 9, numerator := 1682824740903563811190996992 }, { target := 10, numerator := 411305551526149618340898799616 }, { target := 11, numerator := 51838745324734563704100618240 }, { target := 12, numerator := 411305578052567596335234023424 }, { target := 13, numerator := 51838745324734563704100618240 }, { target := 14, numerator := 323898692358223525760347406336 }, { target := 15, numerator := 51838745324734563704100618240 }, { target := 17, numerator := 51838732965416034318701035520 }, { target := 19, numerator := 32495926031241232216102010880 }, { target := 20, numerator := 1682824740903563811190996992 }, { target := 21, numerator := 411305578052567596335234023424 }, { target := 22, numerator := 51838732965416034318701035520 }, { target := 23, numerator := 411305604578985574329569247232 }, { target := 24, numerator := 51838732965416034318701035520 }, { target := 25, numerator := 1207956105269204307409769594880 }, { target := 26, numerator := 45262182686371716300999229440 }, { target := 27, numerator := 323875349700698701104056107008 }, { target := 28, numerator := 51838745324734563704100618240 }, { target := 30, numerator := 51838732965416034318701035520 }, { target := 32, numerator := 45320211125713218501385125888 }, { target := 33, numerator := 45320211125713218501385125888 }, { target := 34, numerator := 32437897591899730015716114432 }, { target := 35, numerator := 1682824740903563811190996992 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk23.Parent2
