import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk1Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 32; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk1.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot16.Left5.expected,
    Slot16.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 33366526216946116859002880 }, { target := 27, numerator := 1115182308821086911521095680 }, { target := 29, numerator := 12356934565712633371453030400 }, { target := 37, numerator := 1115169207124972825718292480 }, { target := 44, numerator := 33346436949571185294704640 }, { target := 80, numerator := 46154269981971078499532800 }, { target := 82, numerator := 1881067204561313920375062528 }, { target := 85, numerator := 1881049290507507735833083904 }, { target := 92, numerator := 46162537199274645872705536 }, { target := 131, numerator := 33366526216946116859002880 }, { target := 134, numerator := 113633263317550260268564480 }, { target := 136, numerator := 33399332477606939680833536 }, { target := 157, numerator := 113633263317550260268564480 }, { target := 158, numerator := 3797872278384827304278753280 }, { target := 160, numerator := 42082858436435651517113958400 }, { target := 168, numerator := 3797827659161514740369326080 }, { target := 175, numerator := 113564847175137662274109440 }, { target := 176, numerator := 1881067204561313920375062528 }, { target := 178, numerator := 75420251624856670614610509824 }, { target := 181, numerator := 75419580072120451937150697472 }, { target := 188, numerator := 1881370614058800905988341760 }, { target := 227, numerator := 1115182308821086911521095680 }, { target := 230, numerator := 3797872278384827304278753280 }, { target := 232, numerator := 1116278765829216876883869696 }, { target := 267, numerator := 33399332477606939680833536 }, { target := 268, numerator := 1116278765829216876883869696 }, { target := 270, numerator := 12369084011947932932510842880 }, { target := 278, numerator := 1116265651251400481917894656 }, { target := 285, numerator := 33379223458288467399671808 }, { target := 286, numerator := 1881049290507507735833083904 }, { target := 288, numerator := 75419580072120451937150697472 }, { target := 291, numerator := 75418908523582714012307030016 }, { target := 298, numerator := 1881352698373565756431400960 }, { target := 302, numerator := 12356934565712633371453030400 }, { target := 305, numerator := 42082858436435651517113958400 }, { target := 307, numerator := 12369084011947932932510842880 }, { target := 573, numerator := 46162537199274645872705536 }, { target := 575, numerator := 1881370614058800905988341760 }, { target := 578, numerator := 1881352698373565756431400960 }, { target := 585, numerator := 46170804994164865456144384 }, { target := 589, numerator := 1115169207124972825718292480 }, { target := 592, numerator := 3797827659161514740369326080 }, { target := 594, numerator := 1116265651251400481917894656 }, { target := 763, numerator := 33346436949571185294704640 }, { target := 766, numerator := 113564847175137662274109440 }, { target := 768, numerator := 33379223458288467399671808 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk1.Parent0
