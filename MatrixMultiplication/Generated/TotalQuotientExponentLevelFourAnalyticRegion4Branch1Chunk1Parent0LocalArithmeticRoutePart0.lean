import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk1Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 22; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk1.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left6.expected,
    Slot9.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 1521552880339375185985536 }, { target := 35, numerator := 89069964543790463770951680 }, { target := 40, numerator := 89099533165271795059654656 }, { target := 48, numerator := 1491984258858043897282560 }, { target := 79, numerator := 51530701508096489376710656 }, { target := 80, numerator := 3016548301113966179154657280 }, { target := 85, numerator := 3017549706866765595647410176 }, { target := 93, numerator := 50529295755297072883957760 }, { target := 121, numerator := 1521552880339375185985536 }, { target := 122, numerator := 51530701508096489376710656 }, { target := 124, numerator := 559244308330474024606892032 }, { target := 132, numerator := 51530622192388701987799040 }, { target := 139, numerator := 1521195959654331935883264 }, { target := 154, numerator := 559244308330474024606892032 }, { target := 155, numerator := 32737521881724965540237148160 }, { target := 160, numerator := 32748389780883964481840873472 }, { target := 168, numerator := 548376409171475083003166720 }, { target := 196, numerator := 89069964543790463770951680 }, { target := 197, numerator := 3016548301113966179154657280 }, { target := 199, numerator := 32737521881724965540237148160 }, { target := 207, numerator := 3016543658063191096898355200 }, { target := 214, numerator := 89049070815302593617592320 }, { target := 492, numerator := 51530622192388701987799040 }, { target := 493, numerator := 3016543658063191096898355200 }, { target := 498, numerator := 3017545062274633540923555840 }, { target := 506, numerator := 50529217980946257962598400 }, { target := 508, numerator := 89099533165271795059654656 }, { target := 509, numerator := 3017549706866765595647410176 }, { target := 511, numerator := 32748389780883964481840873472 }, { target := 519, numerator := 3017545062274633540923555840 }, { target := 526, numerator := 89078632500677548802310144 }, { target := 890, numerator := 1521195959654331935883264 }, { target := 891, numerator := 89049070815302593617592320 }, { target := 896, numerator := 89078632500677548802310144 }, { target := 904, numerator := 1491634274279376751165440 }, { target := 906, numerator := 1491984258858043897282560 }, { target := 907, numerator := 50529295755297072883957760 }, { target := 909, numerator := 548376409171475083003166720 }, { target := 917, numerator := 50529217980946257962598400 }, { target := 924, numerator := 1491634274279376751165440 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk1.Parent0
