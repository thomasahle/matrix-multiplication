import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk0Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 30; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk0.Parent3

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
    Slot7.Left6.expected,
    Slot7.Left14.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left3.expected,
    Slot12.Left11.expected,
    Slot12.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 1926107597646417786568704 }, { target := 35, numerator := 93368500601769695580782592 }, { target := 40, numerator := 93381530577496765555015680 }, { target := 48, numerator := 1913850105223132257189888 }, { target := 79, numerator := 50628295863326817216626688 }, { target := 80, numerator := 2454218070972674695048986624 }, { target := 85, numerator := 2454560567657183992306728960 }, { target := 93, numerator := 50306104126111881086631936 }, { target := 121, numerator := 1926107597646417786568704 }, { target := 122, numerator := 50628295863326817216626688 }, { target := 124, numerator := 695812394850695179287920640 }, { target := 132, numerator := 50432912318026774241869824 }, { target := 139, numerator := 1882248907336027094384640 }, { target := 154, numerator := 695812394850695179287920640 }, { target := 155, numerator := 33729662915364375583491358720 }, { target := 160, numerator := 33734370034855819145432268800 }, { target := 168, numerator := 691384337369206423111598080 }, { target := 196, numerator := 93368500601769695580782592 }, { target := 197, numerator := 2454218070972674695048986624 }, { target := 199, numerator := 33729662915364375583491358720 }, { target := 207, numerator := 2444746809507731432487780352 }, { target := 214, numerator := 91242440688168606598430720 }, { target := 492, numerator := 50432912318026774241869824 }, { target := 493, numerator := 2444746809507731432487780352 }, { target := 498, numerator := 2445087984436978542266286080 }, { target := 506, numerator := 50111963975692309158166528 }, { target := 508, numerator := 93381530577496765555015680 }, { target := 509, numerator := 2454560567657183992306728960 }, { target := 511, numerator := 33734370034855819145432268800 }, { target := 519, numerator := 2445087984436978542266286080 }, { target := 526, numerator := 91255173963093050707148800 }, { target := 890, numerator := 1882248907336027094384640 }, { target := 891, numerator := 91242440688168606598430720 }, { target := 896, numerator := 91255173963093050707148800 }, { target := 904, numerator := 1870270525781122828206080 }, { target := 906, numerator := 1913850105223132257189888 }, { target := 907, numerator := 50306104126111881086631936 }, { target := 909, numerator := 691384337369206423111598080 }, { target := 917, numerator := 50111963975692309158166528 }, { target := 924, numerator := 1870270525781122828206080 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk0.Parent3
