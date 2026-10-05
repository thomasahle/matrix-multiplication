import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk4Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 61; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk4.Parent2

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
    Slot10.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 760669299393814960537600 }, { target := 72, numerator := 19253881034143740062597120 }, { target := 74, numerator := 205485215984666494600478720 }, { target := 82, numerator := 19272010672730812039823360 }, { target := 89, numerator := 720444621043644770549760 }, { target := 146, numerator := 19253881034143740062597120 }, { target := 147, numerator := 487349673731257589190098944 }, { target := 149, numerator := 5201193088766676597540388864 }, { target := 157, numerator := 487808566846604402577375232 }, { target := 164, numerator := 18235723508648671457574912 }, { target := 242, numerator := 205485215984666494600478720 }, { target := 243, numerator := 5201193088766676597540388864 }, { target := 245, numerator := 55509239063432570414389264384 }, { target := 253, numerator := 5206090581939803495430356992 }, { target := 260, numerator := 194619026531134741332099072 }, { target := 640, numerator := 19272010672730812039823360 }, { target := 641, numerator := 487808566846604402577375232 }, { target := 643, numerator := 5206090581939803495430356992 }, { target := 651, numerator := 488267892060098939003600896 }, { target := 658, numerator := 18252894440368842196647936 }, { target := 1017, numerator := 720444621043644770549760 }, { target := 1018, numerator := 18235723508648671457574912 }, { target := 1020, numerator := 194619026531134741332099072 }, { target := 1028, numerator := 18252894440368842196647936 }, { target := 1035, numerator := 682347049373951984664576 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk4.Parent2
