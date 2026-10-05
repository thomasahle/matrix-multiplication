import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk9Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 40; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk9.Parent2

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
    Slot11.Left5.expected,
    Slot12.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1566818915724605714153609363456 }, { target := 1, numerator := 77525994960246939715557654528 }, { target := 2, numerator := 4023305127677485893422153728 }, { target := 3, numerator := 5751383414059124252333054099456 }, { target := 4, numerator := 124877201462912735230449156096 }, { target := 5, numerator := 1567112302187086956601800654848 }, { target := 6, numerator := 124877201462912735230449156096 }, { target := 7, numerator := 130138446629875601398770434048 }, { target := 8, numerator := 77525994960246939715557654528 }, { target := 9, numerator := 3868562622766813359059763200 }, { target := 10, numerator := 3830436146897074632359812268032 }, { target := 12, numerator := 3830437934842554703987464994816 }, { target := 14, numerator := 1524268551991021891616575062016 }, { target := 15, numerator := 51742031247636178324055654400 }, { target := 17, numerator := 51742018911376079030793011200 }, { target := 19, numerator := 77525994960246939715557654528 }, { target := 20, numerator := 4023305127677485893422153728 }, { target := 21, numerator := 3830437941395760536172783206400 }, { target := 23, numerator := 3830439729342395781104856465408 }, { target := 25, numerator := 5598795545524658788035154935808 }, { target := 26, numerator := 124877201462912735230449156096 }, { target := 27, numerator := 1524566046912343230656102268928 }, { target := 28, numerator := 51742031247636178324055654400 }, { target := 30, numerator := 51742018911376079030793011200 }, { target := 32, numerator := 124877201462912735230449156096 }, { target := 33, numerator := 130138446629875601398770434048 }, { target := 34, numerator := 77525994960246939715557654528 }, { target := 35, numerator := 3868562622766813359059763200 }]

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
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 47293183701110450841987317760 }, { target := 11, numerator := 51742031247636178324055654400 }, { target := 12, numerator := 47293183701110450841987317760 }, { target := 13, numerator := 51742031247636178324055654400 }, { target := 14, numerator := 70777719089126768096250429440 }, { target := 21, numerator := 47293172425538135787023892480 }, { target := 22, numerator := 51742018911376079030793011200 }, { target := 23, numerator := 47293172425538135787023892480 }, { target := 24, numerator := 51742018911376079030793011200 }, { target := 25, numerator := 254585350781235737426992824320 }, { target := 27, numerator := 70777742700959182444476497920 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk9.Parent2
