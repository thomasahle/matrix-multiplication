import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk1Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 22; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk1.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 143024368068849724072919040 }, { target := 37, numerator := 6994496049118681444248453120 }, { target := 40, numerator := 6994498601697025742969241600 }, { target := 47, numerator := 143033727522778819382476800 }, { target := 86, numerator := 143024368068849724072919040 }, { target := 89, numerator := 507621533005409982005379072 }, { target := 91, numerator := 143155570497230436472717312 }, { target := 145, numerator := 507621533005409982005379072 }, { target := 147, numerator := 24824838277521528400449110016 }, { target := 150, numerator := 24824847337122698080687226880 }, { target := 157, numerator := 507654751543032142878474240 }, { target := 161, numerator := 6994496049118681444248453120 }, { target := 164, numerator := 24824838277521528400449110016 }, { target := 166, numerator := 7000912402355088722006900736 }, { target := 216, numerator := 143155570497230436472717312 }, { target := 218, numerator := 7000912402355088722006900736 }, { target := 221, numerator := 7000914957275023351983636480 }, { target := 228, numerator := 143164938536990746387415040 }, { target := 232, numerator := 6994498601697025742969241600 }, { target := 235, numerator := 24824847337122698080687226880 }, { target := 237, numerator := 7000914957275023351983636480 }, { target := 406, numerator := 143033727522778819382476800 }, { target := 409, numerator := 507654751543032142878474240 }, { target := 411, numerator := 143164938536990746387415040 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk1.Parent0
