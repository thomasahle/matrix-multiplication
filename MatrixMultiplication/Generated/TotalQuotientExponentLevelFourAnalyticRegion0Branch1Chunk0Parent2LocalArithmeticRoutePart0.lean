import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk0Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 21; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk0.Parent2

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
  [{ target := 71, numerator := 321339980424610802827264 }, { target := 72, numerator := 13700925611442531878305792 }, { target := 74, numerator := 131514701945176669221289984 }, { target := 82, numerator := 13701039737160689074044928 }, { target := 89, numerator := 321311448995071503892480 }, { target := 146, numerator := 13700925611442531878305792 }, { target := 147, numerator := 584164355652973588828389376 }, { target := 149, numerator := 5607373056352809937065213952 }, { target := 157, numerator := 584169221614478777368182784 }, { target := 164, numerator := 13699709121066234743357440 }, { target := 242, numerator := 131514701945176669221289984 }, { target := 243, numerator := 5607373056352809937065213952 }, { target := 245, numerator := 53824976291073365934346338304 }, { target := 253, numerator := 5607419764545758383851962368 }, { target := 260, numerator := 131503024896939557524602880 }, { target := 640, numerator := 13701039737160689074044928 }, { target := 641, numerator := 584169221614478777368182784 }, { target := 643, numerator := 5607419764545758383851962368 }, { target := 651, numerator := 584174087616516362554310656 }, { target := 658, numerator := 13699823236651292777512960 }, { target := 1017, numerator := 321311448995071503892480 }, { target := 1018, numerator := 13699709121066234743357440 }, { target := 1020, numerator := 131503024896939557524602880 }, { target := 1028, numerator := 13699823236651292777512960 }, { target := 1035, numerator := 321282920098806995353600 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk0.Parent2
