import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk12Parent3LocalData

/-! Line-budgeted sparse route chunks, part 1, for region 1, branch 2,
parent 53; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk19

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot25.Left0.expected,
    Slot25.Left3.expected,
    Slot25.Left5.expected,
    Slot26.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 4, numerator := 1692496147460480844588646400 }, { target := 5, numerator := 33917622795108036125556473856 }, { target := 6, numerator := 56935570400570575611962064896 }, { target := 7, numerator := 54633775640024321663321505792 }, { target := 8, numerator := 1692496147460480844588646400 }, { target := 9, numerator := 54633775640024321663321505792 }, { target := 10, numerator := 36490216939247967009331216384 }, { target := 11, numerator := 1760195993358900078372192256 }, { target := 12, numerator := 33917622795108036125556473856 }, { target := 13, numerator := 1624796301562061610805100544 }, { target := 14, numerator := 6797376021766394138727546880 }, { target := 15, numerator := 6991586765245433971262619648 }, { target := 16, numerator := 6797376021766394138727546880 }, { target := 17, numerator := 6020533047850234808587255808 }, { target := 18, numerator := 281799788788086797008390586368 }, { target := 19, numerator := 76713243674220733851353743360 }, { target := 20, numerator := 6991586765245433971262619648 }, { target := 21, numerator := 281799788788086797008390586368 }, { target := 22, numerator := 6797376021766394138727546880 }, { target := 23, numerator := 6797376021766394138727546880 }, { target := 24, numerator := 5826322304371194976052183040 }, { target := 25, numerator := 6797376021766394138727546880 }, { target := 26, numerator := 76713243674220733851353743360 }, { target := 27, numerator := 5826322304371194976052183040 }, { target := 28, numerator := 6797376021766394138727546880 }, { target := 29, numerator := 6020533047850234808587255808 }, { target := 136, numerator := 24317163919308131670750658560 }, { target := 137, numerator := 25011940031288364004200677376 }, { target := 138, numerator := 24317163919308131670750658560 }, { target := 139, numerator := 21538059471387202336950583296 }, { target := 140, numerator := 1008120138483317115835977302016 }, { target := 141, numerator := 274436564232191771712757432320 }, { target := 142, numerator := 25011940031288364004200677376 }, { target := 143, numerator := 1008120138483317115835977302016 }, { target := 144, numerator := 24317163919308131670750658560 }, { target := 145, numerator := 24317163919308131670750658560 }, { target := 146, numerator := 20843283359406970003500564480 }, { target := 147, numerator := 24317163919308131670750658560 }, { target := 148, numerator := 274436564232191771712757432320 }, { target := 149, numerator := 20843283359406970003500564480 }, { target := 150, numerator := 24317163919308131670750658560 }, { target := 151, numerator := 21538059471387202336950583296 }, { target := 267, numerator := 6797373762040245109307473920 }, { target := 268, numerator := 6991584440955680683859116032 }, { target := 269, numerator := 6797373762040245109307473920 }, { target := 270, numerator := 6020531046378502811100905472 }, { target := 271, numerator := 281799695106297018674432704512 }, { target := 272, numerator := 76713218171597051947898634240 }, { target := 273, numerator := 6991584440955680683859116032 }, { target := 274, numerator := 281799695106297018674432704512 }, { target := 275, numerator := 6797373762040245109307473920 }, { target := 276, numerator := 6797373762040245109307473920 }, { target := 277, numerator := 5826320367463067236549263360 }, { target := 278, numerator := 6797373762040245109307473920 }, { target := 279, numerator := 76713218171597051947898634240 }, { target := 280, numerator := 5826320367463067236549263360 }, { target := 281, numerator := 6797373762040245109307473920 }, { target := 282, numerator := 6020531046378502811100905472 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk19

namespace RouteChunk20

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot26.Left2.expected,
    Slot27.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 20696810031802451470969733120 }, { target := 1, numerator := 18917271225329717325802242048 }, { target := 2, numerator := 20696810031802451470969733120 }, { target := 3, numerator := 18917271225329717325802242048 }, { target := 126, numerator := 1692496147460480844588646400 }, { target := 127, numerator := 33917622795108036125556473856 }, { target := 128, numerator := 56935570400570575611962064896 }, { target := 129, numerator := 54633775640024321663321505792 }, { target := 130, numerator := 1692496147460480844588646400 }, { target := 131, numerator := 54633775640024321663321505792 }, { target := 132, numerator := 36490216939247967009331216384 }, { target := 133, numerator := 1760195993358900078372192256 }, { target := 134, numerator := 33917622795108036125556473856 }, { target := 135, numerator := 1624796301562061610805100544 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk20

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent3
