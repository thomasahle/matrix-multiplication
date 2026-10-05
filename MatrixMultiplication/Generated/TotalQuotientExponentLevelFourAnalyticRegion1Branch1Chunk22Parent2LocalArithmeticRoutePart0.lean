import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk22Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 92; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk22.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot0.Left2.expected,
    Slot0.Left5.expected,
    Slot0.Left12.expected,
    Slot1.Left0.expected,
    Slot1.Left3.expected,
    Slot1.Left5.expected,
    Slot2.Left0.expected,
    Slot2.Left2.expected,
    Slot2.Left5.expected,
    Slot2.Left12.expected,
    Slot3.Left0.expected,
    Slot3.Left2.expected,
    Slot4.Left0.expected,
    Slot4.Left3.expected,
    Slot4.Left5.expected,
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot5.Left5.expected,
    Slot5.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 7853183060388892859651063808 }, { target := 17, numerator := 157063661207777857193021276160 }, { target := 18, numerator := 8133653883974210461781458944 }, { target := 19, numerator := 146125299087950470709935865856 }, { target := 20, numerator := 218767242396547729661708206080 }, { target := 21, numerator := 7853183060388892859651063808 }, { target := 22, numerator := 219047713220133047263838601216 }, { target := 23, numerator := 219047713220133047263838601216 }, { target := 24, numerator := 156783190384192539590890881024 }, { target := 25, numerator := 8133653883974210461781458944 }, { target := 26, numerator := 467142622080266581190876594176 }, { target := 27, numerator := 54428251204033598546572738560 }, { target := 28, numerator := 467142622080266581190876594176 }, { target := 29, numerator := 54428251204033598546572738560 }, { target := 44, numerator := 47463140755409254715391737856 }, { target := 50, numerator := 7853181188044369378131574784 }, { target := 51, numerator := 157063623760887387562631495680 }, { target := 52, numerator := 8133651944760239713064845312 }, { target := 53, numerator := 146125264248968444500233945088 }, { target := 54, numerator := 218767190238378861247951011840 }, { target := 55, numerator := 7853181188044369378131574784 }, { target := 56, numerator := 219047660995094731582884282368 }, { target := 57, numerator := 219047660995094731582884282368 }, { target := 58, numerator := 156783153004171517227698225152 }, { target := 59, numerator := 8133651944760239713064845312 }, { target := 60, numerator := 1686134625767355650396586508288 }, { target := 61, numerator := 202187389550661337240672665600 }, { target := 62, numerator := 1686134625767355650396586508288 }, { target := 63, numerator := 202187389550661337240672665600 }, { target := 64, numerator := 1854012773754034296138598711296 }, { target := 71, numerator := 467132330309706465305258098688 }, { target := 72, numerator := 54416794115756858281159557120 }, { target := 73, numerator := 467132330309706465305258098688 }, { target := 74, numerator := 54416794115756858281159557120 }, { target := 75, numerator := 1854012504579144772568821530624 }, { target := 104, numerator := 47463381596099881067297636352 }]

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
    Slot6.Left0.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left2.expected,
    Slot9.Left3.expected,
    Slot9.Left4.expected,
    Slot9.Left5.expected,
    Slot9.Left6.expected,
    Slot9.Left7.expected,
    Slot9.Left8.expected,
    Slot9.Left9.expected,
    Slot9.Left10.expected,
    Slot9.Left11.expected,
    Slot9.Left12.expected,
    Slot9.Left13.expected,
    Slot9.Left14.expected,
    Slot9.Left15.expected,
    Slot10.Left0.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left2.expected,
    Slot12.Left3.expected,
    Slot12.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 43741977357672251592387067904 }, { target := 1, numerator := 18240272766345524987966783488 }, { target := 2, numerator := 1095704589778326475535141568512 }, { target := 3, numerator := 190855536994200737069213417472 }, { target := 4, numerator := 16905618661490974379091165184 }, { target := 5, numerator := 1095704193099541914484943618048 }, { target := 6, numerator := 16905618661490974379091165184 }, { target := 7, numerator := 16460733959872790842799292416 }, { target := 8, numerator := 621948812862220583736038129664 }, { target := 9, numerator := 16460733959872790842799292416 }, { target := 10, numerator := 190855536994200737069213417472 }, { target := 11, numerator := 621948812862220583736038129664 }, { target := 12, numerator := 43742109583933771942453051392 }, { target := 13, numerator := 16460733959872790842799292416 }, { target := 14, numerator := 16460733959872790842799292416 }, { target := 15, numerator := 18240272766345524987966783488 }, { target := 16, numerator := 1237550013376670447285032714240 }, { target := 19, numerator := 4496977858933637388560748249088 }, { target := 21, numerator := 1237549876428075376637596663808 }, { target := 26, numerator := 835093670925811866206036033536 }, { target := 28, numerator := 835093866153865322564463624192 }, { target := 40, numerator := 162479649525287438475539251200 }, { target := 42, numerator := 162479610787124883685480857600 }, { target := 44, numerator := 16015849258254607306507419648 }, { target := 45, numerator := 8414124707559528063911854080 }, { target := 47, numerator := 8414122701476110047998115840 }, { target := 49, numerator := 18240272766345524987966783488 }, { target := 50, numerator := 1237550208870742526432980762624 }, { target := 53, numerator := 4496978572979316086906382450688 }, { target := 55, numerator := 1237550071922081590640994418688 }, { target := 60, numerator := 3171686035327621575108533944320 }, { target := 62, numerator := 3171686719435928558233410600960 }, { target := 64, numerator := 14236310451781873161339928576 }, { target := 65, numerator := 226310940410221789305215385600 }, { target := 67, numerator := 226310886453495373704776908800 }, { target := 69, numerator := 190855536994200737069213417472 }, { target := 70, numerator := 16905618661490974379091165184 }, { target := 71, numerator := 826969409829958219020443320320 }, { target := 73, numerator := 826969606994853375023870115840 }, { target := 75, numerator := 14236310451781873161339928576 }, { target := 76, numerator := 16905618661490974379091165184 }, { target := 91, numerator := 16460733959872790842799292416 }, { target := 96, numerator := 621948812862220583736038129664 }, { target := 97, numerator := 16460733959872790842799292416 }, { target := 102, numerator := 190855536994200737069213417472 }, { target := 103, numerator := 621948812862220583736038129664 }, { target := 104, numerator := 16015849258254607306507419648 }, { target := 109, numerator := 16460733959872790842799292416 }, { target := 110, numerator := 16460733959872790842799292416 }, { target := 111, numerator := 18240272766345524987966783488 }]

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

namespace RouteChunk2

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot12.Left5.expected,
    Slot12.Left6.expected,
    Slot12.Left7.expected,
    Slot12.Left8.expected,
    Slot12.Left9.expected,
    Slot13.Left0.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left2.expected,
    Slot14.Left3.expected,
    Slot15.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 20727203182486200507565080576 }, { target := 2, numerator := 811168375713394306744225628160 }, { target := 5, numerator := 811168503217289344224646397952 }, { target := 12, numerator := 20727330686381237987985850368 }, { target := 16, numerator := 49554079454418649422999060480 }, { target := 19, numerator := 184081056158064799577328844800 }, { target := 21, numerator := 49543648374047288882846760960 }, { target := 30, numerator := 54428251204033598546572738560 }, { target := 33, numerator := 202187389550661337240672665600 }, { target := 35, numerator := 54416794115756858281159557120 }, { target := 50, numerator := 49554079454418649422999060480 }, { target := 53, numerator := 184081056158064799577328844800 }, { target := 55, numerator := 49543648374047288882846760960 }, { target := 71, numerator := 8123982476264371923776962560 }, { target := 73, numerator := 8123980539356244184274042880 }, { target := 77, numerator := 54428251204033598546572738560 }, { target := 80, numerator := 202187389550661337240672665600 }, { target := 82, numerator := 54416794115756858281159557120 }, { target := 87, numerator := 226601082641516945445350277120 }, { target := 89, numerator := 226601028615615239568500981760 }, { target := 92, numerator := 226601082641516945445350277120 }, { target := 94, numerator := 226601028615615239568500981760 }, { target := 98, numerator := 162189507293992282335404359680 }, { target := 100, numerator := 162189468625005017821756784640 }, { target := 105, numerator := 8414124707559528063911854080 }, { target := 107, numerator := 8414122701476110047998115840 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk22.Parent2
