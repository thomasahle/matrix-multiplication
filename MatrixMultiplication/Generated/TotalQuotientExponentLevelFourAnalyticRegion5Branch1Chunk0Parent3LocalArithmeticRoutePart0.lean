import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk0Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 31; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk0.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot9.Left0.expected,
    Slot9.Left2.expected,
    Slot9.Left5.expected,
    Slot9.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 35, numerator := 356437663751317738166943744 }, { target := 37, numerator := 14296890324131075673089376256 }, { target := 40, numerator := 14296762803732878833146134528 }, { target := 47, numerator := 356495310456770553370902528 }, { target := 86, numerator := 356437663751317738166943744 }, { target := 89, numerator := 1214179679606043399839285248 }, { target := 91, numerator := 356599307767672552283963392 }, { target := 145, numerator := 1214179679606043399839285248 }, { target := 147, numerator := 48700011888736730115811049472 }, { target := 150, numerator := 48699577562248443850586587136 }, { target := 157, numerator := 1214376013110812492815138816 }, { target := 161, numerator := 14296890324131075673089376256 }, { target := 164, numerator := 48700011888736730115811049472 }, { target := 166, numerator := 14304232544930812900161880064 }, { target := 216, numerator := 356599307767672552283963392 }, { target := 218, numerator := 14304232544930812900161880064 }, { target := 221, numerator := 14304104926310797037128384512 }, { target := 228, numerator := 356657003745320040688254976 }, { target := 232, numerator := 14296762803732878833146134528 }, { target := 235, numerator := 48699577562248443850586587136 }, { target := 237, numerator := 14304104926310797037128384512 }, { target := 406, numerator := 356495310456770553370902528 }, { target := 409, numerator := 1214376013110812492815138816 }, { target := 411, numerator := 356657003745320040688254976 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk0.Parent3
