import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk24Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 99; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk24.Parent1

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
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot1.Left4.expected,
    Slot1.Left5.expected,
    Slot1.Left6.expected,
    Slot1.Left7.expected,
    Slot1.Left8.expected,
    Slot1.Left9.expected,
    Slot1.Left10.expected,
    Slot1.Left11.expected,
    Slot1.Left12.expected,
    Slot1.Left13.expected,
    Slot1.Left14.expected,
    Slot1.Left15.expected,
    Slot2.Left0.expected,
    Slot2.Left3.expected,
    Slot2.Left5.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot6.Left0.expected,
    Slot7.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 3752279070492631215317712896 }, { target := 1, numerator := 735026898325694538221355008 }, { target := 2, numerator := 116269876300847753249511440384 }, { target := 3, numerator := 5783501121036385971794345984 }, { target := 4, numerator := 696341272098026404630757376 }, { target := 5, numerator := 116269847966648856031640158208 }, { target := 6, numerator := 696341272098026404630757376 }, { target := 7, numerator := 696341272098026404630757376 }, { target := 8, numerator := 29826617821532130998350774272 }, { target := 9, numerator := 696341272098026404630757376 }, { target := 10, numerator := 5783501121036385971794345984 }, { target := 11, numerator := 29826617821532130998350774272 }, { target := 12, numerator := 3752307404691528433188995072 }, { target := 13, numerator := 696341272098026404630757376 }, { target := 14, numerator := 696341272098026404630757376 }, { target := 15, numerator := 735026898325694538221355008 }, { target := 16, numerator := 3350135325013437111230005248 }, { target := 19, numerator := 11984887931659007752012824576 }, { target := 21, numerator := 3350134211291263661015826432 }, { target := 26, numerator := 3350135325013437111230005248 }, { target := 27, numerator := 3752429007934305335766941696 }, { target := 28, numerator := 3350135325013437111230005248 }, { target := 29, numerator := 3752429007934305335766941696 }, { target := 30, numerator := 3752429007934305335766941696 }, { target := 33, numerator := 13424067020760917585587863552 }, { target := 35, numerator := 3752427760473237351158513664 }, { target := 44, numerator := 3752279070492631215317712896 }, { target := 49, numerator := 735026898325694538221355008 }, { target := 50, numerator := 3350135325013437111230005248 }, { target := 53, numerator := 11984887931659007752012824576 }, { target := 55, numerator := 3350134211291263661015826432 }, { target := 60, numerator := 11984887931659007752012824576 }, { target := 61, numerator := 13424067020760917585587863552 }, { target := 62, numerator := 11984887931659007752012824576 }, { target := 63, numerator := 13424067020760917585587863552 }, { target := 64, numerator := 116269876300847753249511440384 }, { target := 69, numerator := 5783501121036385971794345984 }, { target := 70, numerator := 696341272098026404630757376 }, { target := 71, numerator := 3350134211291263661015826432 }, { target := 72, numerator := 3752427760473237351158513664 }, { target := 73, numerator := 3350134211291263661015826432 }, { target := 74, numerator := 3752427760473237351158513664 }, { target := 75, numerator := 116269847966648856031640158208 }, { target := 76, numerator := 696341272098026404630757376 }, { target := 77, numerator := 3752429007934305335766941696 }, { target := 80, numerator := 13424067020760917585587863552 }, { target := 82, numerator := 3752427760473237351158513664 }, { target := 91, numerator := 696341272098026404630757376 }, { target := 96, numerator := 29826617821532130998350774272 }, { target := 97, numerator := 696341272098026404630757376 }, { target := 102, numerator := 5783501121036385971794345984 }, { target := 103, numerator := 29826617821532130998350774272 }, { target := 104, numerator := 3752307404691528433188995072 }, { target := 109, numerator := 696341272098026404630757376 }, { target := 110, numerator := 696341272098026404630757376 }, { target := 111, numerator := 735026898325694538221355008 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk24.Parent1
