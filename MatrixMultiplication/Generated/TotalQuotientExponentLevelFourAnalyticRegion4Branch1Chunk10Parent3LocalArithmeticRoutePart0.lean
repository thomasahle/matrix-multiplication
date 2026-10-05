import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk10Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 82; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk10.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left3.expected,
    Slot13.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 32957326380867338108928000 }, { target := 27, numerator := 1120101463684109963152588800 }, { target := 29, numerator := 12333323487236047139294412800 }, { target := 37, numerator := 1120118915273403512179916800 }, { target := 44, numerator := 32952963483543950852096000 }, { target := 80, numerator := 23377451556985935161720832 }, { target := 82, numerator := 938950309659142029091799040 }, { target := 85, numerator := 939132826799734943165448192 }, { target := 92, numerator := 23196540475455435165401088 }, { target := 131, numerator := 32957326380867338108928000 }, { target := 134, numerator := 112449203715420916033781760 }, { target := 136, numerator := 32957251961698245578588160 }, { target := 157, numerator := 112449203715420916033781760 }, { target := 158, numerator := 3821745617838581440887914496 }, { target := 160, numerator := 42080852957462911566349336576 }, { target := 168, numerator := 3821805162029058232477024256 }, { target := 175, numerator := 112434317667801718136504320 }, { target := 176, numerator := 938950309659142029091799040 }, { target := 178, numerator := 37712737073153723176111308800 }, { target := 181, numerator := 37720067834817802236319498240 }, { target := 188, numerator := 931684055011591634403983360 }, { target := 227, numerator := 1120101463684109963152588800 }, { target := 230, numerator := 3821745617838581440887914496 }, { target := 232, numerator := 1120098934443137458488999936 }, { target := 267, numerator := 32957251961698245578588160 }, { target := 268, numerator := 1120098934443137458488999936 }, { target := 270, numerator := 12333295638020505118720393216 }, { target := 278, numerator := 1120116385993024510776836096 }, { target := 285, numerator := 32952889074226482506629120 }, { target := 286, numerator := 939132826799734943165448192 }, { target := 288, numerator := 37720067834817802236319498240 }, { target := 291, numerator := 37727400021466402342779748352 }, { target := 298, numerator := 931865159706810764731875328 }, { target := 302, numerator := 12333323487236047139294412800 }, { target := 305, numerator := 42080852957462911566349336576 }, { target := 307, numerator := 12333295638020505118720393216 }, { target := 573, numerator := 23196540475455435165401088 }, { target := 575, numerator := 931684055011591634403983360 }, { target := 578, numerator := 931865159706810764731875328 }, { target := 585, numerator := 23017029410489647279112192 }, { target := 589, numerator := 1120118915273403512179916800 }, { target := 592, numerator := 3821805162029058232477024256 }, { target := 594, numerator := 1120116385993024510776836096 }, { target := 763, numerator := 32952963483543950852096000 }, { target := 766, numerator := 112434317667801718136504320 }, { target := 768, numerator := 32952889074226482506629120 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk10.Parent3
