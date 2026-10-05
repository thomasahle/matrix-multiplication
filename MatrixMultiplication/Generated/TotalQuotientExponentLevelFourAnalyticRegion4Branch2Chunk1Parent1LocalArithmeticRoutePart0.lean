import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk1Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 30; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk1.Parent1

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
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left6.expected,
    Slot11.Left14.expected,
    Slot12.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 3720603834154983421378560 }, { target := 35, numerator := 171878652737692130659532800 }, { target := 40, numerator := 171841632279278942123196416 }, { target := 48, numerator := 3742617013957979757608960 }, { target := 79, numerator := 62163546597587091896401920 }, { target := 80, numerator := 2808158584294466311195459584 }, { target := 85, numerator := 2807683008699933612325208064 }, { target := 93, numerator := 62163546597587091896401920 }, { target := 121, numerator := 3720603834154983421378560 }, { target := 122, numerator := 119369225624785860931092480 }, { target := 124, numerator := 1430269801108939152451174400 }, { target := 132, numerator := 119369734687762365871554560 }, { target := 139, numerator := 3876018989982125769359360 }, { target := 154, numerator := 729667749120507731697991680 }, { target := 155, numerator := 32961805841610533465160155136 }, { target := 160, numerator := 32956223596185482522636845056 }, { target := 168, numerator := 729667749120507731697991680 }, { target := 196, numerator := 171878652737692130659532800 }, { target := 197, numerator := 5519276446393047628898107392 }, { target := 199, numerator := 66165060652477609386686021632 }, { target := 207, numerator := 5519299550918326376904785920 }, { target := 214, numerator := 179243591967423201405829120 }, { target := 492, numerator := 62164006868283758928199680 }, { target := 493, numerator := 2808179376433568536892276736 }, { target := 498, numerator := 2807703797317783879371718656 }, { target := 506, numerator := 62164006868283758928199680 }, { target := 508, numerator := 171841632279278942123196416 }, { target := 509, numerator := 5518077817680463688267464704 }, { target := 511, numerator := 66150623123681785400562548736 }, { target := 519, numerator := 5518100918067778803650789376 }, { target := 526, numerator := 179204608409635690440032256 }, { target := 890, numerator := 2005859696074924574638080 }, { target := 891, numerator := 90612142207499586729148416 }, { target := 896, numerator := 90596796591463788693159936 }, { target := 904, numerator := 2005859696074924574638080 }, { target := 906, numerator := 3742617013957979757608960 }, { target := 907, numerator := 120103499101583676046049280 }, { target := 909, numerator := 1439262501017642950721536000 }, { target := 917, numerator := 120104008790842004167720960 }, { target := 924, numerator := 3900023745982838352117760 }]

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

namespace RouteChunk1

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot12.Left1.expected,
    Slot12.Left3.expected,
    Slot12.Left11.expected,
    Slot12.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 79, numerator := 57205679027198769034690560 }, { target := 80, numerator := 2711117862098581317702647808 }, { target := 85, numerator := 2710394808980530075942256640 }, { target := 93, numerator := 57939952503996584149647360 }, { target := 154, numerator := 700602051988431420753182720 }, { target := 155, numerator := 33203254810867075921525866496 }, { target := 160, numerator := 33194399527496302877925703680 }, { target := 168, numerator := 709594751897135219023544320 }, { target := 492, numerator := 57205727819478606943354880 }, { target := 493, numerator := 2711120174484757840012509184 }, { target := 498, numerator := 2710397120749994924279070720 }, { target := 506, numerator := 57940001922558245239521280 }, { target := 890, numerator := 1870159293907201194721280 }, { target := 891, numerator := 88631449759923614676680704 }, { target := 896, numerator := 88607811818171901746872320 }, { target := 904, numerator := 1894164049907913777479680 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk1.Parent1
