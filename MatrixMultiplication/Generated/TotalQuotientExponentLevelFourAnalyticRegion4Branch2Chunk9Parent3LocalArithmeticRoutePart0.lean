import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk9Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 78; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk9.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left3.expected,
    Slot13.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 27498324179049580572180480 }, { target := 27, numerator := 960996578020808730701987840 }, { target := 29, numerator := 11594761054263428599439687680 }, { target := 37, numerator := 961019228362850132998225920 }, { target := 44, numerator := 27499133119836773511331840 }, { target := 80, numerator := 17872999624737180182642688 }, { target := 82, numerator := 823569209639170951027359744 }, { target := 85, numerator := 823567905641039144316567552 }, { target := 92, numerator := 17871294396410971406991360 }, { target := 131, numerator := 27498324179049580572180480 }, { target := 134, numerator := 105530114426103505807736832 }, { target := 136, numerator := 27498965247034763369250816 }, { target := 157, numerator := 105530114426103505807736832 }, { target := 158, numerator := 3688009428548929358718304256 }, { target := 160, numerator := 44497128364352531814324109312 }, { target := 168, numerator := 3688096353598319847882620928 }, { target := 175, numerator := 105533218892153166135033856 }, { target := 176, numerator := 823569209639170951027359744 }, { target := 178, numerator := 37949211509350239543410819072 }, { target := 181, numerator := 37949151422474318803816677376 }, { target := 188, numerator := 823490634493736137711943680 }, { target := 227, numerator := 960996578020808730701987840 }, { target := 230, numerator := 3688009428548929358718304256 }, { target := 232, numerator := 961018981718431465448931328 }, { target := 267, numerator := 27498965247034763369250816 }, { target := 268, numerator := 961018981718431465448931328 }, { target := 270, numerator := 11595031362739659150832173056 }, { target := 278, numerator := 961041632588519924054360064 }, { target := 285, numerator := 27499774206680779748016128 }, { target := 286, numerator := 823567905641039144316567552 }, { target := 288, numerator := 37949151422474318803816677376 }, { target := 291, numerator := 37949091335693536606350737408 }, { target := 298, numerator := 823489330620016270707261440 }, { target := 302, numerator := 11594761054263428599439687680 }, { target := 305, numerator := 44497128364352531814324109312 }, { target := 307, numerator := 11595031362739659150832173056 }, { target := 573, numerator := 17871294396410971406991360 }, { target := 575, numerator := 823490634493736137711943680 }, { target := 578, numerator := 823489330620016270707261440 }, { target := 585, numerator := 17869589330777299170099200 }, { target := 589, numerator := 961019228362850132998225920 }, { target := 592, numerator := 3688096353598319847882620928 }, { target := 594, numerator := 961041632588519924054360064 }, { target := 763, numerator := 27499133119836773511331840 }, { target := 766, numerator := 105533218892153166135033856 }, { target := 768, numerator := 27499774206680779748016128 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk9.Parent3
