import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk23Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 97; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk23.Parent3

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
    Slot1.Left3.expected,
    Slot1.Left5.expected,
    Slot2.Left0.expected,
    Slot2.Left2.expected,
    Slot3.Left0.expected,
    Slot3.Left3.expected,
    Slot3.Left5.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot5.Left0.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left2.expected,
    Slot6.Left3.expected,
    Slot6.Left4.expected,
    Slot6.Left5.expected,
    Slot6.Left6.expected,
    Slot6.Left7.expected,
    Slot6.Left8.expected,
    Slot6.Left9.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot8.Left0.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left2.expected,
    Slot9.Left3.expected,
    Slot10.Left0.expected,
    Slot11.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 344332995481976219393178206208 }, { target := 1, numerator := 30987186608362175006068703232 }, { target := 2, numerator := 1740853180245066011576893440 }, { target := 3, numerator := 1243855157482660720752669491200 }, { target := 4, numerator := 47061064305958284512962019328 }, { target := 5, numerator := 344332962425410839305661710336 }, { target := 6, numerator := 47061064305958284512962019328 }, { target := 7, numerator := 47061064305958284512962019328 }, { target := 8, numerator := 30987186608362175006068703232 }, { target := 9, numerator := 1740853180245066011576893440 }, { target := 10, numerator := 411460338377033044073023275008 }, { target := 11, numerator := 41857857558025464421894062080 }, { target := 12, numerator := 411460320557478268869596413952 }, { target := 13, numerator := 41857857558025464421894062080 }, { target := 14, numerator := 358916229865055628170497097728 }, { target := 15, numerator := 41857857558025464421894062080 }, { target := 17, numerator := 41857837598648376668159213568 }, { target := 19, numerator := 30987186608362175006068703232 }, { target := 20, numerator := 1740853180245066011576893440 }, { target := 21, numerator := 411460320557478268869596413952 }, { target := 22, numerator := 41857837598648376668159213568 }, { target := 23, numerator := 411460302737923493666169552896 }, { target := 24, numerator := 41857837598648376668159213568 }, { target := 25, numerator := 1293916851230766240791575658496 }, { target := 26, numerator := 47061064305958284512962019328 }, { target := 27, numerator := 358916196808490248082980601856 }, { target := 28, numerator := 41857857558025464421894062080 }, { target := 30, numerator := 41857837598648376668159213568 }, { target := 32, numerator := 47061064305958284512962019328 }, { target := 33, numerator := 47061064305958284512962019328 }, { target := 34, numerator := 30987186608362175006068703232 }, { target := 35, numerator := 1740853180245066011576893440 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk23.Parent3
