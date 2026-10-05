import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk7Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 67; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk7.Parent0

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
  [{ target := 71, numerator := 551220330725100333563904 }, { target := 72, numerator := 16423296669575615531188224 }, { target := 74, numerator := 174943354723098426385367040 }, { target := 82, numerator := 16469172530603354769850368 }, { target := 89, numerator := 591839712427912621719552 }, { target := 146, numerator := 16423296669575615531188224 }, { target := 147, numerator := 489322796098767587475718144 }, { target := 149, numerator := 5212337888932325797123850240 }, { target := 157, numerator := 490689641321329831662583808 }, { target := 164, numerator := 17633528076248294948339712 }, { target := 242, numerator := 174943354723098426385367040 }, { target := 243, numerator := 5212337888932325797123850240 }, { target := 245, numerator := 55522584447334153999246950400 }, { target := 253, numerator := 5226897723868831152791879680 }, { target := 260, numerator := 187834916419526328865259520 }, { target := 640, numerator := 16469172530603354769850368 }, { target := 641, numerator := 490689641321329831662583808 }, { target := 643, numerator := 5226897723868831152791879680 }, { target := 651, numerator := 492060304608117442798944256 }, { target := 658, numerator := 17682784525774248040464384 }, { target := 1017, numerator := 591839712427912621719552 }, { target := 1018, numerator := 17633528076248294948339712 }, { target := 1020, numerator := 187834916419526328865259520 }, { target := 1028, numerator := 17682784525774248040464384 }, { target := 1035, numerator := 635452333091538207768576 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk7.Parent0
