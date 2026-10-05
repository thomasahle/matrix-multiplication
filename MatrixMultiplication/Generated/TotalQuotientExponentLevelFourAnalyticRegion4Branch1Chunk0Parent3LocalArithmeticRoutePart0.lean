import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk0Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 21; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk0.Parent3

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
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left6.expected,
    Slot11.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 9211884933842922972905472 }, { target := 30, numerator := 539253203119603411436175360 }, { target := 35, numerator := 539432219401099737890291712 }, { target := 43, numerator := 9032868652346596518789120 }, { target := 71, numerator := 828677356007478125395968 }, { target := 72, numerator := 28064963124656838990102528 }, { target := 74, numerator := 304579026320900213667004416 }, { target := 82, numerator := 28064919927255113159147520 }, { target := 89, numerator := 828482967699711886098432 }, { target := 104, numerator := 323462622764464688129376256 }, { target := 105, numerator := 18935131807214104854428385280 }, { target := 110, numerator := 18941417716813084962142027776 }, { target := 118, numerator := 317176713165484580415733760 }, { target := 146, numerator := 28064963124656838990102528 }, { target := 147, numerator := 950481088300957926359564288 }, { target := 149, numerator := 10315231953994421284829659136 }, { target := 157, numerator := 950479625326885173377105920 }, { target := 164, numerator := 28058379741329450569039872 }, { target := 200, numerator := 9211884933842922972905472 }, { target := 202, numerator := 323462622764464688129376256 }, { target := 205, numerator := 323445371598020931041099776 }, { target := 212, numerator := 9228501574624380949889024 }, { target := 226, numerator := 323445371598020931041099776 }, { target := 227, numerator := 18934121943670524463682682880 }, { target := 232, numerator := 18940407518024363059703709696 }, { target := 240, numerator := 317159797244182335020072960 }, { target := 242, numerator := 304579026320900213667004416 }, { target := 243, numerator := 10315231953994421284829659136 }, { target := 245, numerator := 111947530123835636071993966592 }, { target := 253, numerator := 10315216076859053864900362240 }, { target := 260, numerator := 304507579211746823985168384 }, { target := 296, numerator := 539253203119603411436175360 }, { target := 298, numerator := 18935131807214104854428385280 }, { target := 301, numerator := 18934121943670524463682682880 }, { target := 308, numerator := 540225922256983144131461120 }, { target := 624, numerator := 9228501574624380949889024 }, { target := 625, numerator := 540225922256983144131461120 }, { target := 630, numerator := 540405261452765202537775104 }, { target := 638, numerator := 9049162378842322543575040 }, { target := 640, numerator := 28064919927255113159147520 }, { target := 641, numerator := 950479625326885173377105920 }, { target := 643, numerator := 10315216076859053864900362240 }, { target := 651, numerator := 950478162355064220208332800 }, { target := 658, numerator := 28058336554060823899668480 }, { target := 659, numerator := 539432219401099737890291712 }, { target := 661, numerator := 18941417716813084962142027776 }, { target := 664, numerator := 18940407518024363059703709696 }, { target := 671, numerator := 540405261452765202537775104 }, { target := 1017, numerator := 828482967699711886098432 }, { target := 1018, numerator := 28058379741329450569039872 }, { target := 1020, numerator := 304507579211746823985168384 }, { target := 1028, numerator := 28058336554060823899668480 }, { target := 1035, numerator := 828288624990891873927168 }, { target := 1036, numerator := 9032868652346596518789120 }, { target := 1038, numerator := 317176713165484580415733760 }, { target := 1041, numerator := 317159797244182335020072960 }, { target := 1048, numerator := 9049162378842322543575040 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk0.Parent3
