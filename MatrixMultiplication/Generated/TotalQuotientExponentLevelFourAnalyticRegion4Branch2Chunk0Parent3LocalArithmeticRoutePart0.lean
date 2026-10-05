import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk0Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 21; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk0.Parent3

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
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 33368154976120977720606720 }, { target := 27, numerator := 1034243483229578494193172480 }, { target := 29, numerator := 12139817557963663392815185920 }, { target := 37, numerator := 1034251140964611390355537920 }, { target := 44, numerator := 33372409273361475588587520 }, { target := 80, numerator := 15906484670917757036920832 }, { target := 82, numerator := 777894324501006092699959296 }, { target := 85, numerator := 777894608386534503906017280 }, { target := 92, numerator := 15907525584521931459133440 }, { target := 131, numerator := 33368154976120977720606720 }, { target := 134, numerator := 118430126357116632743018496 }, { target := 136, numerator := 33398765025461265881890816 }, { target := 157, numerator := 118430126357116632743018496 }, { target := 158, numerator := 3670732963526360159238488064 }, { target := 160, numerator := 43086593441286923180945965056 }, { target := 168, numerator := 3670760142329869199952838656 }, { target := 175, numerator := 118445225692399433139879936 }, { target := 176, numerator := 777894324501006092699959296 }, { target := 178, numerator := 38042320010356063227019788288 }, { target := 181, numerator := 38042333893558161475727523840 }, { target := 188, numerator := 777945229575366337961656320 }, { target := 227, numerator := 1034243483229578494193172480 }, { target := 230, numerator := 3670732963526360159238488064 }, { target := 232, numerator := 1035192239433635453881810944 }, { target := 267, numerator := 33398765025461265881890816 }, { target := 268, numerator := 1035192239433635453881810944 }, { target := 270, numerator := 12150953936786444877431832576 }, { target := 278, numerator := 1035199904193439343812018176 }, { target := 285, numerator := 33403023225352315843117056 }, { target := 286, numerator := 777894608386534503906017280 }, { target := 288, numerator := 38042333893558161475727523840 }, { target := 291, numerator := 38042347776765326274016051200 }, { target := 298, numerator := 777945513479472097630617600 }, { target := 302, numerator := 12139817557963663392815185920 }, { target := 305, numerator := 43086593441286923180945965056 }, { target := 307, numerator := 12150953936786444877431832576 }, { target := 573, numerator := 15907525584521931459133440 }, { target := 575, numerator := 777945229575366337961656320 }, { target := 578, numerator := 777945513479472097630617600 }, { target := 585, numerator := 15908566566243050245324800 }, { target := 589, numerator := 1034251140964611390355537920 }, { target := 592, numerator := 3670760142329869199952838656 }, { target := 594, numerator := 1035199904193439343812018176 }, { target := 763, numerator := 33372409273361475588587520 }, { target := 766, numerator := 118445225692399433139879936 }, { target := 768, numerator := 33403023225352315843117056 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk0.Parent3
