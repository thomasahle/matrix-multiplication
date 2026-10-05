import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk9Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 80; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk9.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left0.expected,
    Slot7.Left3.expected,
    Slot7.Left5.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 958034642232177196728844288 }, { target := 21, numerator := 38649950624168109109806104576 }, { target := 24, numerator := 38642688779120773188160585728 }, { target := 31, numerator := 957966205703094985534996480 }, { target := 35, numerator := 13241773068071022962040373248 }, { target := 38, numerator := 45933078244699889428284309504 }, { target := 40, numerator := 13252617062413400522040016896 }, { target := 71, numerator := 958034642232177196728844288 }, { target := 73, numerator := 958429180411362311409762304 }, { target := 90, numerator := 958429180411362311409762304 }, { target := 92, numerator := 38669081902600585534616109056 }, { target := 95, numerator := 38661813025980131557939085312 }, { target := 102, numerator := 958360668312441302892412928 }, { target := 106, numerator := 45933078244699889428284309504 }, { target := 109, numerator := 159322606652894504747364515840 }, { target := 111, numerator := 45970783553004167830553231360 }, { target := 116, numerator := 38649950624168109109806104576 }, { target := 118, numerator := 38669081902600585534616109056 }, { target := 140, numerator := 13252617062413400522040016896 }, { target := 143, numerator := 45970783553004167830553231360 }, { target := 145, numerator := 13263475130121244696559747072 }, { target := 150, numerator := 38642688779120773188160585728 }, { target := 152, numerator := 38661813025980131557939085312 }, { target := 232, numerator := 957966205703094985534996480 }, { target := 234, numerator := 958360668312441302892412928 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk9.Parent1
