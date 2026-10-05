import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk2Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 35; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk2.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left0.expected,
    Slot6.Left2.expected,
    Slot6.Left5.expected,
    Slot6.Left12.expected,
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 396901208928292423285604352 }, { target := 21, numerator := 19410146503167813031198457856 }, { target := 24, numerator := 19410153586725981584967598080 }, { target := 31, numerator := 396927181974910453772451840 }, { target := 35, numerator := 5190598292656704558339194880 }, { target := 38, numerator := 18292317531934804799549079552 }, { target := 40, numerator := 5196341669163164030407278592 }, { target := 71, numerator := 396901208928292423285604352 }, { target := 73, numerator := 396900262643197719265411072 }, { target := 90, numerator := 396900262643197719265411072 }, { target := 92, numerator := 19410100225827485535506006016 }, { target := 95, numerator := 19410107309368765590672506880 }, { target := 102, numerator := 396926235627891254875914240 }, { target := 106, numerator := 18292317531934804799549079552 }, { target := 109, numerator := 64461152070278033776412983296 }, { target := 111, numerator := 18312582524209191470472626176 }, { target := 116, numerator := 19410146503167813031198457856 }, { target := 118, numerator := 19410100225827485535506006016 }, { target := 140, numerator := 5196341669163164030407278592 }, { target := 143, numerator := 18312582524209191470472626176 }, { target := 145, numerator := 5202091214979616251477753856 }, { target := 150, numerator := 19410153586725981584967598080 }, { target := 152, numerator := 19410107309368765590672506880 }, { target := 232, numerator := 396927181974910453772451840 }, { target := 234, numerator := 396926235627891254875914240 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk2.Parent2
