import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk6Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 63; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk6.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected,
    Slot13.Left11.expected,
    Slot13.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 174106675570275844897112064 }, { target := 82, numerator := 6753344446335914800519839744 }, { target := 85, numerator := 6754272679065638580088995840 }, { target := 92, numerator := 174251976646205579968118784 }, { target := 131, numerator := 214564812078064870310805504 }, { target := 134, numerator := 766860344803200766492803072 }, { target := 136, numerator := 214589712769197927888322560 }, { target := 176, numerator := 6310489849093729024991035392 }, { target := 178, numerator := 244244761607906541052427763712 }, { target := 181, numerator := 244277135504048048424993423360 }, { target := 188, numerator := 6314640880075482431532040192 }, { target := 227, numerator := 5744652216559344291132997632 }, { target := 230, numerator := 20536881952761239914011426816 }, { target := 232, numerator := 5745432535972795023366291456 }, { target := 286, numerator := 6311045306237032019880050688 }, { target := 288, numerator := 244271353771551683791760130048 }, { target := 291, numerator := 244303742722118859955560775680 }, { target := 298, numerator := 6315207422868674695636451328 }, { target := 302, numerator := 73411769537333880881273634816 }, { target := 305, numerator := 262166506238282472734167400448 }, { target := 307, numerator := 73415840832214554607399993344 }, { target := 573, numerator := 173020174051723058633244672 }, { target := 575, numerator := 6707335030034686649735053312 }, { target := 578, numerator := 6708248207470672809893560320 }, { target := 585, numerator := 173156432361219995553759232 }, { target := 589, numerator := 5734159475517069802768171008 }, { target := 592, numerator := 20499955488188588717437353984 }, { target := 594, numerator := 5734950806141255988340064256 }, { target := 763, numerator := 212172764416101506309160960 }, { target := 766, numerator := 758438275763259933437460480 }, { target := 768, numerator := 212200092784998596927815680 }]

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
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot18.Left5.expected,
    Slot18.Left12.expected,
    Slot19.Left0.expected,
    Slot19.Left3.expected,
    Slot19.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 214564812078064870310805504 }, { target := 27, numerator := 5744652216559344291132997632 }, { target := 29, numerator := 73411769537333880881273634816 }, { target := 37, numerator := 5734159475517069802768171008 }, { target := 44, numerator := 212172764416101506309160960 }, { target := 80, numerator := 33816707092355134210965504 }, { target := 82, numerator := 1179148807854785499959918592 }, { target := 85, numerator := 1179699866228186700702547968 }, { target := 92, numerator := 33266227106120977499553792 }, { target := 157, numerator := 766860344803200766492803072 }, { target := 158, numerator := 20536881952761239914011426816 }, { target := 160, numerator := 262166506238282472734167400448 }, { target := 168, numerator := 20499955488188588717437353984 }, { target := 175, numerator := 758438275763259933437460480 }, { target := 176, numerator := 1622003405096971275488722944 }, { target := 178, numerator := 56557351259338605151452659712 }, { target := 181, numerator := 56583782530592275186946408448 }, { target := 188, numerator := 1595599875928059749609766912 }, { target := 267, numerator := 214589712769197927888322560 }, { target := 268, numerator := 5745432535972795023366291456 }, { target := 270, numerator := 73415840832214554607399993344 }, { target := 278, numerator := 5734950806141255988340064256 }, { target := 285, numerator := 212200092784998596927815680 }, { target := 286, numerator := 1622927239056793260911493120 }, { target := 288, numerator := 56589564263088639820179701760 }, { target := 291, numerator := 56616010588630055908320215040 }, { target := 298, numerator := 1596508671401014975015157760 }, { target := 573, numerator := 34498029700603498834427904 }, { target := 575, numerator := 1202905725968855531406753792 }, { target := 578, numerator := 1203467886799016860758048768 }, { target := 585, numerator := 33936458910673249335508992 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk6.Parent0
