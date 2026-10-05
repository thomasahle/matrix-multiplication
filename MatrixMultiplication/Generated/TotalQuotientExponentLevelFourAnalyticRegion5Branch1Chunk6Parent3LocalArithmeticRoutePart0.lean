import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch1Chunk6Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 1,
parent 72; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk6.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected,
    Slot20.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 19, numerator := 2227678780599369501406920704 }, { target := 21, numerator := 77000323173407212507431436288 }, { target := 24, numerator := 77000353868460306912350568448 }, { target := 31, numerator := 2227747254837091392573931520 }, { target := 35, numerator := 15805273707355559011232514048 }, { target := 38, numerator := 55085855837731745633667121152 }, { target := 40, numerator := 15794787735950574325566799872 }, { target := 71, numerator := 2227678780599369501406920704 }, { target := 73, numerator := 2227685101328825971906707456 }, { target := 90, numerator := 1685961772636377941782036480 }, { target := 92, numerator := 57735214420104165568548962304 }, { target := 95, numerator := 57735323034778717750080569344 }, { target := 102, numerator := 1686008996400285830036324352 }, { target := 106, numerator := 55085855837731745633667121152 }, { target := 109, numerator := 191918077002120124412586885120 }, { target := 111, numerator := 55050017752447319405997588480 }, { target := 116, numerator := 77000323173407212507431436288 }, { target := 118, numerator := 77000538803497126943793348608 }, { target := 140, numerator := 15794787735950574325566799872 }, { target := 143, numerator := 55050017752447319405997588480 }, { target := 145, numerator := 15784301723851063406981283840 }, { target := 150, numerator := 77000353868460306912350568448 }, { target := 152, numerator := 77000569499208309844261994496 }, { target := 232, numerator := 2227747254837091392573931520 }, { target := 234, numerator := 2227753575719107300450893824 }]

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
    Slot20.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 90, numerator := 541723328692448030124670976 }, { target := 92, numerator := 19265324383392961375244386304 }, { target := 95, numerator := 19265246464429592094181425152 }, { target := 102, numerator := 541744579318821470414569472 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk6.Parent3
