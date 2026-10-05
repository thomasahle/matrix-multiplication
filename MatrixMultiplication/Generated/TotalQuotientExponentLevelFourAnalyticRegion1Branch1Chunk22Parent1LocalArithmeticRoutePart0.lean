import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk22Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 91; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk22.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot0.Left3.expected,
    Slot0.Left5.expected,
    Slot1.Left0.expected,
    Slot1.Left2.expected,
    Slot2.Left0.expected,
    Slot2.Left3.expected,
    Slot2.Left5.expected,
    Slot3.Left0.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot5.Left0.expected,
    Slot5.Left3.expected,
    Slot5.Left5.expected,
    Slot6.Left0.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot8.Left0.expected,
    Slot8.Left3.expected,
    Slot8.Left5.expected,
    Slot9.Left0.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left2.expected,
    Slot11.Left3.expected,
    Slot11.Left4.expected,
    Slot11.Left5.expected,
    Slot11.Left6.expected,
    Slot11.Left7.expected,
    Slot11.Left8.expected,
    Slot11.Left9.expected,
    Slot12.Left0.expected,
    Slot13.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 1536558718546815389549608304640 }, { target := 1, numerator := 86655802749976619242938695680 }, { target := 2, numerator := 4487532642409503496509325312 }, { target := 3, numerator := 5652073756421042412300594577408 }, { target := 4, numerator := 120699153830324576802664611840 }, { target := 5, numerator := 1536523664420413048173187039232 }, { target := 6, numerator := 120853896335235249337027002368 }, { target := 7, numerator := 120853896335235249337027002368 }, { target := 8, numerator := 86501060245065946708576305152 }, { target := 9, numerator := 4487532642409503496509325312 }, { target := 10, numerator := 3837923227197433018083178446848 }, { target := 11, numerator := 51838732965416034318701035520 }, { target := 12, numerator := 3837923606794467827633688150016 }, { target := 13, numerator := 51838732965416034318701035520 }, { target := 14, numerator := 1579181046423231662610054119424 }, { target := 19, numerator := 86655802749976619242938695680 }, { target := 20, numerator := 4487532642409503496509325312 }, { target := 21, numerator := 3790727148422969647134572281856 }, { target := 22, numerator := 51838745324734563704100618240 }, { target := 23, numerator := 3790727516767620050211542401024 }, { target := 24, numerator := 51838745324734563704100618240 }, { target := 25, numerator := 5804492984526038118698267443200 }, { target := 26, numerator := 120699153830324576802664611840 }, { target := 27, numerator := 1579166595981794081495700209664 }, { target := 32, numerator := 120853896335235249337027002368 }, { target := 33, numerator := 120853896335235249337027002368 }, { target := 34, numerator := 86501060245065946708576305152 }, { target := 35, numerator := 4487532642409503496509325312 }]

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
    Slot13.Left1.expected,
    Slot13.Left2.expected,
    Slot13.Left3.expected,
    Slot14.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 70933415512066980298945986560 }, { target := 3, numerator := 254253368417490001368469995520 }, { target := 5, numerator := 70954028641764706300303769600 }, { target := 15, numerator := 51838732965416034318701035520 }, { target := 17, numerator := 51838745324734563704100618240 }, { target := 21, numerator := 47196458371498180499115868160 }, { target := 23, numerator := 47196469624012065461942353920 }, { target := 28, numerator := 51838732965416034318701035520 }, { target := 30, numerator := 51838745324734563704100618240 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk22.Parent1
