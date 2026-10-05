import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk0Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 20; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk0.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 1961465773777969175592960 }, { target := 57, numerator := 44894009050245310546182144 }, { target := 59, numerator := 590660143206782791694942208 }, { target := 67, numerator := 44892948467732713536749568 }, { target := 74, numerator := 1961506565413069060571136 }, { target := 110, numerator := 1961465773777969175592960 }, { target := 112, numerator := 111576003321166965610905600 }, { target := 115, numerator := 111576477036515895227187200 }, { target := 122, numerator := 1961046197326060086886400 }, { target := 152, numerator := 111576003321166965610905600 }, { target := 153, numerator := 2553750450227168684109987840 }, { target := 155, numerator := 33599106842014664528630906880 }, { target := 163, numerator := 2553690120060040674520596480 }, { target := 170, numerator := 111578323712210350595112960 }, { target := 206, numerator := 44894009050245310546182144 }, { target := 208, numerator := 2553750450227168684109987840 }, { target := 211, numerator := 2553761292619346205558702080 }, { target := 218, numerator := 44884405788602362977320960 }, { target := 283, numerator := 111576477036515895227187200 }, { target := 284, numerator := 2553761292619346205558702080 }, { target := 286, numerator := 33599249492872802668705218560 }, { target := 294, numerator := 2553700962196075967162613760 }, { target := 301, numerator := 111578797437410904396267520 }, { target := 302, numerator := 590660143206782791694942208 }, { target := 304, numerator := 33599106842014664528630906880 }, { target := 307, numerator := 33599249492872802668705218560 }, { target := 314, numerator := 590533795303860439057694720 }, { target := 660, numerator := 1961046197326060086886400 }, { target := 661, numerator := 44884405788602362977320960 }, { target := 663, numerator := 590533795303860439057694720 }, { target := 671, numerator := 44883345432958597196677120 }, { target := 678, numerator := 1961086980235435693834240 }, { target := 679, numerator := 44892948467732713536749568 }, { target := 681, numerator := 2553690120060040674520596480 }, { target := 684, numerator := 2553700962196075967162613760 }, { target := 691, numerator := 44883345432958597196677120 }, { target := 966, numerator := 1961506565413069060571136 }, { target := 968, numerator := 111578323712210350595112960 }, { target := 971, numerator := 111578797437410904396267520 }, { target := 978, numerator := 1961086980235435693834240 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk0.Parent1
