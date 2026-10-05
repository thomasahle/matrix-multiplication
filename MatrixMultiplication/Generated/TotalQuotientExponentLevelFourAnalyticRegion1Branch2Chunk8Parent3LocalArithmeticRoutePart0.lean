import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk8Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 37; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk8.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot0.Left1.expected,
    Slot0.Left2.expected,
    Slot0.Left3.expected,
    Slot0.Left4.expected,
    Slot0.Left5.expected,
    Slot0.Left6.expected,
    Slot0.Left7.expected,
    Slot0.Left8.expected,
    Slot0.Left9.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot2.Left0.expected,
    Slot3.Left0.expected,
    Slot3.Left3.expected,
    Slot3.Left5.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected,
    Slot5.Left0.expected,
    Slot6.Left0.expected,
    Slot6.Left3.expected,
    Slot6.Left5.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot8.Left0.expected,
    Slot9.Left0.expected,
    Slot9.Left3.expected,
    Slot9.Left5.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot11.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 367688346727906829290811949056 }, { target := 1, numerator := 44101613899541672293281300480 }, { target := 2, numerator := 1798881619586568211962789888 }, { target := 3, numerator := 1285889281557070199414232973312 }, { target := 4, numerator := 36325803027780377441571176448 }, { target := 5, numerator := 367688313671341449203295453184 }, { target := 6, numerator := 36383831467121879641957072896 }, { target := 7, numerator := 32611982909924236616873803776 }, { target := 8, numerator := 44101613899541672293281300480 }, { target := 9, numerator := 1798881619586568211962789888 }, { target := 10, numerator := 416116233899200972435845283840 }, { target := 11, numerator := 49227459374707699994035486720 }, { target := 12, numerator := 416044567265456942700082233344 }, { target := 13, numerator := 49711029702553551663917957120 }, { target := 14, numerator := 367688346727906829290811949056 }, { target := 15, numerator := 49227459374707699994035486720 }, { target := 17, numerator := 49227459374707699994035486720 }, { target := 19, numerator := 44101613899541672293281300480 }, { target := 20, numerator := 1798881619586568211962789888 }, { target := 21, numerator := 416044567265456942700082233344 }, { target := 22, numerator := 49227459374707699994035486720 }, { target := 23, numerator := 415972900631712912964319182848 }, { target := 24, numerator := 49711029702553551663917957120 }, { target := 25, numerator := 1285889281557070199414232973312 }, { target := 26, numerator := 36325803027780377441571176448 }, { target := 27, numerator := 367688313671341449203295453184 }, { target := 28, numerator := 49711029702553551663917957120 }, { target := 30, numerator := 49711029702553551663917957120 }, { target := 32, numerator := 36383831467121879641957072896 }, { target := 33, numerator := 32611982909924236616873803776 }, { target := 34, numerator := 44101613899541672293281300480 }, { target := 35, numerator := 1798881619586568211962789888 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk8.Parent3
