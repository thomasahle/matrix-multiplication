import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk0Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 31; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk0.Parent3

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
    Slot8.Left6.expected,
    Slot8.Left14.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left3.expected,
    Slot14.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 1437994711052784112762880 }, { target := 72, numerator := 37237268705725272295473152 }, { target := 74, numerator := 401316560299443787745198080 }, { target := 82, numerator := 37207044713952241587847168 }, { target := 89, numerator := 1427141708113065602449408 }, { target := 146, numerator := 37237268705725272295473152 }, { target := 147, numerator := 952808522001382598510641152 }, { target := 149, numerator := 10316488027760125550453063680 }, { target := 157, numerator := 951945982330008175921594368 }, { target := 164, numerator := 36923859425758772394459136 }, { target := 200, numerator := 11847297380916669366403072 }, { target := 202, numerator := 405425130498078040234393600 }, { target := 205, numerator := 405426324325778062487584768 }, { target := 212, numerator := 11847297380916669366403072 }, { target := 242, numerator := 401316560299443787745198080 }, { target := 243, numerator := 10316488027760125550453063680 }, { target := 245, numerator := 111499501205988980252947251200 }, { target := 253, numerator := 10307525367976984596048773120 }, { target := 260, numerator := 398073861877461858218147840 }, { target := 296, numerator := 550523439548990718021206016 }, { target := 298, numerator := 18839405321328300561059020800 }, { target := 301, numerator := 18839460796438826929832853504 }, { target := 308, numerator := 550523439548990718021206016 }, { target := 640, numerator := 37207044713952241587847168 }, { target := 641, numerator := 951945982330008175921594368 }, { target := 643, numerator := 10307525367976984596048773120 }, { target := 651, numerator := 951083521144553309378445312 }, { target := 658, numerator := 36893637942490734132199424 }, { target := 659, numerator := 550508288695061455296266240 }, { target := 661, numerator := 18838886845533025690714112000 }, { target := 664, numerator := 18838942319116831785809346560 }, { target := 671, numerator := 550508288695061455296266240 }, { target := 1017, numerator := 719303487711062565847040 }, { target := 1018, numerator := 16595884352804571590950912 }, { target := 1020, numerator := 187328228468357752925716480 }, { target := 1028, numerator := 16566612219330783774507008 }, { target := 1035, numerator := 708139601289066670194688 }, { target := 1036, numerator := 11851721966577427507314688 }, { target := 1038, numerator := 405576543783423798830694400 }, { target := 1041, numerator := 405577738056980184193564672 }, { target := 1048, numerator := 11851721966577427507314688 }]

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
    Slot14.Left18.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 11847297380916669366403072 }, { target := 30, numerator := 550523439548990718021206016 }, { target := 35, numerator := 550508288695061455296266240 }, { target := 43, numerator := 11851721966577427507314688 }, { target := 104, numerator := 405425130498078040234393600 }, { target := 105, numerator := 18839405321328300561059020800 }, { target := 110, numerator := 18838886845533025690714112000 }, { target := 118, numerator := 405576543783423798830694400 }, { target := 226, numerator := 405426324325778062487584768 }, { target := 227, numerator := 18839460796438826929832853504 }, { target := 232, numerator := 18838942319116831785809346560 }, { target := 240, numerator := 405577738056980184193564672 }, { target := 624, numerator := 11847297380916669366403072 }, { target := 625, numerator := 550523439548990718021206016 }, { target := 630, numerator := 550508288695061455296266240 }, { target := 638, numerator := 11851721966577427507314688 }, { target := 1017, numerator := 707838220402003036602368 }, { target := 1018, numerator := 20327975072954200803508224 }, { target := 1020, numerator := 210745633409104105292431360 }, { target := 1028, numerator := 20327025723159950357692416 }, { target := 1035, numerator := 708139601289066670194688 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk0.Parent3
