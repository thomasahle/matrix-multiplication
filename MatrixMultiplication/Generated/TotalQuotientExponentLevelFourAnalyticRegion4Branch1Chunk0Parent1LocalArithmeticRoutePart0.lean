import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk0Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 19; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk0.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left3.expected,
    Slot11.Left11.expected,
    Slot11.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 33673346586824060625223680 }, { target := 27, numerator := 1140421206627586768403169280 }, { target := 29, numerator := 12376584254449601835339612160 }, { target := 37, numerator := 1140419451298966504944435200 }, { target := 44, numerator := 33665447608032875060920320 }, { target := 80, numerator := 30374446991302187047452672 }, { target := 82, numerator := 1066556775229726325899001856 }, { target := 85, numerator := 1066499892773589801423077376 }, { target := 92, numerator := 30429237219167023266791424 }, { target := 131, numerator := 33673346586824060625223680 }, { target := 134, numerator := 113860866999441397188132864 }, { target := 136, numerator := 33648821261994220100517888 }, { target := 157, numerator := 113860866999441397188132864 }, { target := 158, numerator := 3856146195518757306047135744 }, { target := 160, numerator := 41849378114816528123867168768 }, { target := 168, numerator := 3856140260164572749454376960 }, { target := 175, numerator := 113834157905610892520718336 }, { target := 176, numerator := 1066556775229726325899001856 }, { target := 178, numerator := 37450668817581168669268901888 }, { target := 181, numerator := 37448671468658191060170702848 }, { target := 188, numerator := 1068480658445192114892439552 }, { target := 227, numerator := 1140421206627586768403169280 }, { target := 230, numerator := 3856146195518757306047135744 }, { target := 232, numerator := 1139590603097781262612430848 }, { target := 267, numerator := 33648821261994220100517888 }, { target := 268, numerator := 1139590603097781262612430848 }, { target := 270, numerator := 12367570010844749170481299456 }, { target := 278, numerator := 1139588849047620343373496320 }, { target := 285, numerator := 33640928036270083525312512 }, { target := 286, numerator := 1066499892773589801423077376 }, { target := 288, numerator := 37448671468658191060170702848 }, { target := 291, numerator := 37446674226259418387220267008 }, { target := 298, numerator := 1068423673382982330081083392 }, { target := 302, numerator := 12376584254449601835339612160 }, { target := 305, numerator := 41849378114816528123867168768 }, { target := 307, numerator := 12367570010844749170481299456 }, { target := 573, numerator := 30429237219167023266791424 }, { target := 575, numerator := 1068480658445192114892439552 }, { target := 578, numerator := 1068423673382982330081083392 }, { target := 585, numerator := 30484126279088632085086208 }, { target := 589, numerator := 1140419451298966504944435200 }, { target := 592, numerator := 3856140260164572749454376960 }, { target := 594, numerator := 1139588849047620343373496320 }, { target := 763, numerator := 33665447608032875060920320 }, { target := 766, numerator := 113834157905610892520718336 }, { target := 768, numerator := 33640928036270083525312512 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk0.Parent1
