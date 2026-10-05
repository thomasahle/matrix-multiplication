import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk8Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 75; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk8.Parent2

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
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 2099477701934686037606400 }, { target := 57, numerator := 62552745659208867145318400 }, { target := 59, numerator := 666320982500129703460864000 }, { target := 67, numerator := 62727476781985299221708800 }, { target := 74, numerator := 2254188044420144902963200 }, { target := 110, numerator := 2099477701934686037606400 }, { target := 112, numerator := 102409258798992158229528576 }, { target := 115, numerator := 102371080815269643766726656 }, { target := 122, numerator := 2099066650233921607827456 }, { target := 152, numerator := 102409258798992158229528576 }, { target := 153, numerator := 3051225699086153880652742656 }, { target := 155, numerator := 32502101773775994487580917760 }, { target := 163, numerator := 3059748811647035360298401792 }, { target := 170, numerator := 109955788818279289677938688 }, { target := 206, numerator := 62552745659208867145318400 }, { target := 208, numerator := 3051225699086153880652742656 }, { target := 211, numerator := 3050088207745628961176027136 }, { target := 218, numerator := 62540498607255417767591936 }, { target := 283, numerator := 102371080815269643766726656 }, { target := 284, numerator := 3050088207745628961176027136 }, { target := 286, numerator := 32489985049887754217387458560 }, { target := 294, numerator := 3058608142905790715136049152 }, { target := 301, numerator := 109914797502016176393289728 }, { target := 302, numerator := 666320982500129703460864000 }, { target := 304, numerator := 32502101773775994487580917760 }, { target := 307, numerator := 32489985049887754217387458560 }, { target := 314, numerator := 666190525114057295984066560 }, { target := 660, numerator := 2099066650233921607827456 }, { target := 661, numerator := 62540498607255417767591936 }, { target := 663, numerator := 666190525114057295984066560 }, { target := 671, numerator := 62715195519844655407562752 }, { target := 678, numerator := 2253746702352711709360128 }, { target := 679, numerator := 62727476781985299221708800 }, { target := 681, numerator := 3059748811647035360298401792 }, { target := 684, numerator := 3058608142905790715136049152 }, { target := 691, numerator := 62715195519844655407562752 }, { target := 966, numerator := 2254188044420144902963200 }, { target := 968, numerator := 109955788818279289677938688 }, { target := 971, numerator := 109914797502016176393289728 }, { target := 978, numerator := 2253746702352711709360128 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk8.Parent2
