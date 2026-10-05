import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk6Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 28; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk6.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected,
    Slot2.Left7.expected,
    Slot2.Left8.expected,
    Slot2.Left9.expected,
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
    Slot11.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 324085339171092465617773527040 }, { target := 1, numerator := 29072248110092602393334120448 }, { target := 2, numerator := 1508739422879057210033307648 }, { target := 3, numerator := 1208130053638600810791216087040 }, { target := 4, numerator := 46828950548592275711418433536 }, { target := 5, numerator := 324153067351189782069428355072 }, { target := 6, numerator := 46828950548592275711418433536 }, { target := 7, numerator := 48801917486203350524538912768 }, { target := 8, numerator := 29072248110092602393334120448 }, { target := 9, numerator := 1450710983537555009647411200 }, { target := 10, numerator := 431305915116354393170656624640 }, { target := 11, numerator := 51742018911376079030793011200 }, { target := 12, numerator := 431306053895821745706040819712 }, { target := 13, numerator := 51742018911376079030793011200 }, { target := 14, numerator := 337949649925552765347049766912 }, { target := 15, numerator := 51742018911376079030793011200 }, { target := 17, numerator := 51742031247636178324055654400 }, { target := 19, numerator := 29072248110092602393334120448 }, { target := 20, numerator := 1508739422879057210033307648 }, { target := 21, numerator := 431306039728722297097105178624 }, { target := 22, numerator := 51742031247636178324055654400 }, { target := 23, numerator := 431306178508189649632489373696 }, { target := 24, numerator := 51742031247636178324055654400 }, { target := 25, numerator := 1259632513066430962366949621760 }, { target := 26, numerator := 46828950548592275711418433536 }, { target := 27, numerator := 338014459683163668357962530816 }, { target := 28, numerator := 51742018911376079030793011200 }, { target := 30, numerator := 51742031247636178324055654400 }, { target := 32, numerator := 46828950548592275711418433536 }, { target := 33, numerator := 48801917486203350524538912768 }, { target := 34, numerator := 29072248110092602393334120448 }, { target := 35, numerator := 1450710983537555009647411200 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk6.Parent2
