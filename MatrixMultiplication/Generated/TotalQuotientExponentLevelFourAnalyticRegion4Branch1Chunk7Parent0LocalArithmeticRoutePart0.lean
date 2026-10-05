import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk7Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 63; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk7.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot5.Left5.expected,
    Slot5.Left12.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected,
    Slot18.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 5992757510416462005556740096 }, { target := 21, numerator := 211884691765104608952335728640 }, { target := 24, numerator := 211888554644077347763006734336 }, { target := 31, numerator := 5988904075954886652528164864 }, { target := 35, numerator := 54489279479973415728877404160 }, { target := 38, numerator := 186540489891377946410321182720 }, { target := 40, numerator := 54492548634595783537569300480 }, { target := 71, numerator := 6060061811664214525483155456 }, { target := 73, numerator := 6060052327081147483404894208 }, { target := 90, numerator := 3372107218855542413181583360 }, { target := 92, numerator := 115469900434105919354049658880 }, { target := 95, numerator := 115473657093212629610843340800 }, { target := 102, numerator := 3368360004703600177326325760 }, { target := 106, numerator := 183235255223825275542684303360 }, { target := 109, numerator := 627187310677232958518989946880 }, { target := 111, numerator := 183245818225338437253621350400 }, { target := 116, numerator := 211817559830207866951578943488 }, { target := 118, numerator := 211817281250264905109412511744 }, { target := 140, numerator := 54461880006816922678025256960 }, { target := 143, numerator := 186445525328776630926720368640 }, { target := 145, numerator := 54465142817349381274069893120 }, { target := 150, numerator := 211816638965931772353422819328 }, { target := 152, numerator := 211816360391612680545935294464 }, { target := 232, numerator := 6060921285005457982364844032 }, { target := 234, numerator := 6060911795139668577380990976 }]

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
    Slot18.Left2.expected,
    Slot19.Left0.expected,
    Slot19.Left3.expected,
    Slot19.Left5.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot20.Left5.expected,
    Slot20.Left12.expected,
    Slot23.Left0.expected,
    Slot23.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 548466461078249629827465216 }, { target := 21, numerator := 19258642641849124174501511168 }, { target := 24, numerator := 19257615524567826114415689728 }, { target := 31, numerator := 549455799333109140576796672 }, { target := 35, numerator := 13869179099055927141282611200 }, { target := 38, numerator := 44762438753111819493467750400 }, { target := 40, numerator := 13841714146298196271929753600 }, { target := 71, numerator := 481162159830497109901049856 }, { target := 73, numerator := 481166404415162061391134720 }, { target := 90, numerator := 3169111512640767131614445568 }, { target := 92, numerator := 115673325875734249118067851264 }, { target := 95, numerator := 115672405017082024554590633984 }, { target := 102, numerator := 3169994592455704330104733696 }, { target := 106, numerator := 48067673420664490361104629760 }, { target := 109, numerator := 155137248724658550493591633920 }, { target := 111, numerator := 47972485639884988407380705280 }, { target := 116, numerator := 19325774576745866175258296320 }, { target := 118, numerator := 19325945059575263362704998400 }, { target := 140, numerator := 13872382774077057131473797120 }, { target := 143, numerator := 44772778536446794734281687040 }, { target := 145, numerator := 13844911477123863933207183360 }, { target := 150, numerator := 19329531202713401523999604736 }, { target := 152, numerator := 19329701718681973619498680320 }, { target := 232, numerator := 477438590282537810740117504 }, { target := 234, numerator := 477442802019635930050068480 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk7.Parent0
