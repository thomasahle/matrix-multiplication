import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk24Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 101; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk24.Parent3

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
    Slot3.Left0.expected,
    Slot3.Left2.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected,
    Slot4.Left4.expected,
    Slot4.Left5.expected,
    Slot4.Left6.expected,
    Slot4.Left7.expected,
    Slot4.Left8.expected,
    Slot4.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 270799383593676935134183424 }, { target := 17, numerator := 5415987671873538702683668480 }, { target := 18, numerator := 280470790150593968531832832 }, { target := 19, numerator := 5038802816153774400175341568 }, { target := 20, numerator := 7543697114395286050166538240 }, { target := 21, numerator := 270799383593676935134183424 }, { target := 22, numerator := 7553368520952203083564187648 }, { target := 23, numerator := 7553368520952203083564187648 }, { target := 24, numerator := 5406316265316621669286019072 }, { target := 25, numerator := 280470790150593968531832832 }, { target := 26, numerator := 3610653528783939479242014720 }, { target := 27, numerator := 3668364388979468695987290112 }, { target := 28, numerator := 3610653528783939479242014720 }, { target := 29, numerator := 3668364388979468695987290112 }, { target := 40, numerator := 5415987671873538702683668480 }, { target := 42, numerator := 5415987671873538702683668480 }, { target := 44, numerator := 2970656582080461887772819456 }, { target := 45, numerator := 280470790150593968531832832 }, { target := 47, numerator := 280470790150593968531832832 }, { target := 50, numerator := 270799383593676935134183424 }, { target := 51, numerator := 5415987671873538702683668480 }, { target := 52, numerator := 280470790150593968531832832 }, { target := 53, numerator := 5038802816153774400175341568 }, { target := 54, numerator := 7543697114395286050166538240 }, { target := 55, numerator := 270799383593676935134183424 }, { target := 56, numerator := 7553368520952203083564187648 }, { target := 57, numerator := 7553368520952203083564187648 }, { target := 58, numerator := 5406316265316621669286019072 }, { target := 59, numerator := 280470790150593968531832832 }, { target := 60, numerator := 17237681250126687000453971968 }, { target := 61, numerator := 13398768116003035151125708800 }, { target := 62, numerator := 17237681250126687000453971968 }, { target := 63, numerator := 13398768116003035151125708800 }, { target := 64, numerator := 115871601356415493111478747136 }, { target := 65, numerator := 7543697114395286050166538240 }, { target := 67, numerator := 7543697114395286050166538240 }, { target := 71, numerator := 3610652403532550982959366144 }, { target := 72, numerator := 3668363153047615757447331840 }, { target := 73, numerator := 3610652403532550982959366144 }, { target := 74, numerator := 3668363153047615757447331840 }, { target := 75, numerator := 115871558855117147284671823872 }, { target := 87, numerator := 7553368520952203083564187648 }, { target := 89, numerator := 7553368520952203083564187648 }, { target := 92, numerator := 7553368520952203083564187648 }, { target := 94, numerator := 7553368520952203083564187648 }, { target := 98, numerator := 5406316265316621669286019072 }, { target := 100, numerator := 5406316265316621669286019072 }, { target := 104, numerator := 2970670749179910496708460544 }, { target := 105, numerator := 280470790150593968531832832 }, { target := 107, numerator := 280470790150593968531832832 }]

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
    Slot5.Left0.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left2.expected,
    Slot6.Left3.expected,
    Slot7.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 3666997854178488292403576832 }, { target := 1, numerator := 793055337667196738607251456 }, { target := 2, numerator := 116490571376058183248928309248 }, { target := 3, numerator := 8298066825834814655183192064 }, { target := 4, numerator := 735026898325694538221355008 }, { target := 5, numerator := 116490528874759837422121385984 }, { target := 6, numerator := 735026898325694538221355008 }, { target := 7, numerator := 715684085211860471426056192 }, { target := 8, numerator := 27041252733140025379827744768 }, { target := 9, numerator := 715684085211860471426056192 }, { target := 10, numerator := 8298066825834814655183192064 }, { target := 11, numerator := 27041252733140025379827744768 }, { target := 12, numerator := 3667012021277936901339217920 }, { target := 13, numerator := 715684085211860471426056192 }, { target := 14, numerator := 715684085211860471426056192 }, { target := 15, numerator := 793055337667196738607251456 }, { target := 16, numerator := 3339854145190262544107831296 }, { target := 19, numerator := 12198878433972912600278630400 }, { target := 21, numerator := 3339853019938874047825182720 }, { target := 30, numerator := 3668364388979468695987290112 }, { target := 33, numerator := 13398768116003035151125708800 }, { target := 35, numerator := 3668363153047615757447331840 }, { target := 50, numerator := 3339854145190262544107831296 }, { target := 53, numerator := 12198878433972912600278630400 }, { target := 55, numerator := 3339853019938874047825182720 }, { target := 77, numerator := 3668364388979468695987290112 }, { target := 80, numerator := 13398768116003035151125708800 }, { target := 82, numerator := 3668363153047615757447331840 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk24.Parent3
