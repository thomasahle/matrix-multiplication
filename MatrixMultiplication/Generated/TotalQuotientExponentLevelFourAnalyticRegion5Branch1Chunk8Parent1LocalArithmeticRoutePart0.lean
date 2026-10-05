import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk8Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 80; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk8.Parent1

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
  [{ target := 19, numerator := 1102811394127550757862375424 }, { target := 21, numerator := 38511199027522574642973769728 }, { target := 24, numerator := 38511279307671718633649733632 }, { target := 31, numerator := 1102830283644147732251148288 }, { target := 35, numerator := 10525129969291216177200103424 }, { target := 38, numerator := 36705438049248071921086496768 }, { target := 40, numerator := 10519851441016927664943923200 }, { target := 71, numerator := 1102811394127550757862375424 }, { target := 73, numerator := 1102812372995062866001264640 }, { target := 90, numerator := 1102812372995062866001264640 }, { target := 92, numerator := 38511240549923009064157052928 }, { target := 95, numerator := 38511320830234282641418354688 }, { target := 102, numerator := 1102831262410328848774201344 }, { target := 106, numerator := 36705438049248071921086496768 }, { target := 109, numerator := 128049407204606239177283993600 }, { target := 111, numerator := 36686475952242060162284650496 }, { target := 116, numerator := 38511199027522574642973769728 }, { target := 118, numerator := 38511240549923009064157052928 }, { target := 140, numerator := 10519851441016927664943923200 }, { target := 143, numerator := 36686475952242060162284650496 }, { target := 145, numerator := 10514581998145775523061563392 }, { target := 150, numerator := 38511279307671718633649733632 }, { target := 152, numerator := 38511320830234282641418354688 }, { target := 232, numerator := 1102830283644147732251148288 }, { target := 234, numerator := 1102831262410328848774201344 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk8.Parent1
