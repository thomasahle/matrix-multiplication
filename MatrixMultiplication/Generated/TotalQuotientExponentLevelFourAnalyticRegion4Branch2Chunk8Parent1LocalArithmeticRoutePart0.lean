import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk8Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 70; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk8.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 4219600473140691384401920 }, { target := 57, numerator := 35602878992124583555891200 }, { target := 58, numerator := 35866604021695876767416320 }, { target := 59, numerator := 4483325502711984595927040 }, { target := 60, numerator := 30592103430270012536913920 }, { target := 61, numerator := 4483325502711984595927040 }, { target := 62, numerator := 35602878992124583555891200 }, { target := 63, numerator := 35602878992124583555891200 }, { target := 64, numerator := 30592103430270012536913920 }, { target := 65, numerator := 646390047479239661448069120 }, { target := 66, numerator := 30592103430270012536913920 }, { target := 67, numerator := 35602878992124583555891200 }, { target := 68, numerator := 35602878992124583555891200 }, { target := 69, numerator := 4483325502711984595927040 }, { target := 70, numerator := 30592103430270012536913920 }, { target := 71, numerator := 4483325502711984595927040 }, { target := 72, numerator := 35602878992124583555891200 }, { target := 73, numerator := 35602878992124583555891200 }, { target := 74, numerator := 4219600473140691384401920 }, { target := 110, numerator := 3409754499577347689152512 }, { target := 112, numerator := 157117936397977001819897856 }, { target := 115, numerator := 157117687625326035361333248 }, { target := 122, numerator := 3409429181495314627952640 }, { target := 152, numerator := 150522941331019990397091840 }, { target := 153, numerator := 1270037317480481168975462400 }, { target := 154, numerator := 1279445001313669918375280640 }, { target := 155, numerator := 159930625164208739796910080 }, { target := 156, numerator := 1091291324649894930378915840 }, { target := 157, numerator := 159930625164208739796910080 }, { target := 158, numerator := 1270037317480481168975462400 }, { target := 159, numerator := 1270037317480481168975462400 }, { target := 160, numerator := 1091291324649894930378915840 }, { target := 161, numerator := 23058233075145624778954506240 }, { target := 162, numerator := 1091291324649894930378915840 }, { target := 163, numerator := 1270037317480481168975462400 }, { target := 164, numerator := 1270037317480481168975462400 }, { target := 165, numerator := 159930625164208739796910080 }, { target := 166, numerator := 1091291324649894930378915840 }, { target := 167, numerator := 159930625164208739796910080 }, { target := 168, numerator := 1270037317480481168975462400 }, { target := 169, numerator := 1270037317480481168975462400 }, { target := 170, numerator := 150522941331019990397091840 }, { target := 206, numerator := 119162258203406647160733696 }, { target := 208, numerator := 5490872761591161147147419648 }, { target := 211, numerator := 5490864067618949339633680384 }, { target := 218, numerator := 119150889162821975796613120 }, { target := 302, numerator := 1437734474976480842263560192 }, { target := 304, numerator := 66249307340025212103552925696 }, { target := 307, numerator := 66249202444198615173161811968 }, { target := 314, numerator := 1437597303510931010213642240 }, { target := 679, numerator := 119165066814767461614747648 }, { target := 681, numerator := 5491002179477759663196340224 }, { target := 684, numerator := 5490993485300634072637243392 }, { target := 691, numerator := 119153697506218612422082560 }, { target := 966, numerator := 3409854807125948205367296 }, { target := 968, numerator := 157122558465355520250216448 }, { target := 971, numerator := 157122309685386204397174784 }, { target := 978, numerator := 3409529479473765936005120 }]

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
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left2.expected,
    Slot11.Left3.expected,
    Slot11.Left4.expected,
    Slot11.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 4219600473140691384401920 }, { target := 112, numerator := 150522941331019990397091840 }, { target := 115, numerator := 150522941331019990397091840 }, { target := 122, numerator := 4219526686164396546195456 }, { target := 206, numerator := 35602878992124583555891200 }, { target := 208, numerator := 1270037317480481168975462400 }, { target := 211, numerator := 1270037317480481168975462400 }, { target := 218, numerator := 35602256414512095858524160 }, { target := 241, numerator := 35866604021695876767416320 }, { target := 243, numerator := 1279445001313669918375280640 }, { target := 246, numerator := 1279445001313669918375280640 }, { target := 253, numerator := 35865976832397370642661376 }, { target := 283, numerator := 150522941331019990397091840 }, { target := 284, numerator := 1270037317480481168975462400 }, { target := 285, numerator := 1279445001313669918375280640 }, { target := 286, numerator := 159930625164208739796910080 }, { target := 287, numerator := 1091291324649894930378915840 }, { target := 288, numerator := 159930625164208739796910080 }, { target := 289, numerator := 1270037317480481168975462400 }, { target := 290, numerator := 1270037317480481168975462400 }, { target := 291, numerator := 1091291324649894930378915840 }, { target := 292, numerator := 23058233075145624778954506240 }, { target := 293, numerator := 1091291324649894930378915840 }, { target := 294, numerator := 1270037317480481168975462400 }, { target := 295, numerator := 1270037317480481168975462400 }, { target := 296, numerator := 159930625164208739796910080 }, { target := 297, numerator := 1091291324649894930378915840 }, { target := 298, numerator := 159930625164208739796910080 }, { target := 299, numerator := 1270037317480481168975462400 }, { target := 300, numerator := 1270037317480481168975462400 }, { target := 301, numerator := 150522941331019990397091840 }, { target := 302, numerator := 4483325502711984595927040 }, { target := 304, numerator := 159930625164208739796910080 }, { target := 307, numerator := 159930625164208739796910080 }, { target := 314, numerator := 4483247104049671330332672 }, { target := 337, numerator := 30592103430270012536913920 }, { target := 339, numerator := 1091291324649894930378915840 }, { target := 342, numerator := 1091291324649894930378915840 }, { target := 349, numerator := 30591568474691874959917056 }, { target := 363, numerator := 4483325502711984595927040 }, { target := 365, numerator := 159930625164208739796910080 }, { target := 368, numerator := 159930625164208739796910080 }, { target := 375, numerator := 4483247104049671330332672 }, { target := 660, numerator := 4219526686164396546195456 }, { target := 661, numerator := 35602256414512095858524160 }, { target := 662, numerator := 35865976832397370642661376 }, { target := 663, numerator := 4483247104049671330332672 }, { target := 664, numerator := 30591568474691874959917056 }, { target := 665, numerator := 4483247104049671330332672 }, { target := 666, numerator := 35602256414512095858524160 }, { target := 667, numerator := 35602256414512095858524160 }, { target := 668, numerator := 30591568474691874959917056 }, { target := 669, numerator := 646378744236808495920316416 }, { target := 670, numerator := 30591568474691874959917056 }, { target := 671, numerator := 35602256414512095858524160 }, { target := 672, numerator := 35602256414512095858524160 }, { target := 673, numerator := 4483247104049671330332672 }, { target := 674, numerator := 30591568474691874959917056 }, { target := 675, numerator := 4483247104049671330332672 }, { target := 676, numerator := 35602256414512095858524160 }, { target := 677, numerator := 35602256414512095858524160 }, { target := 678, numerator := 4219526686164396546195456 }]

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

namespace RouteChunk2

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot11.Left6.expected,
    Slot11.Left7.expected,
    Slot11.Left8.expected,
    Slot11.Left9.expected,
    Slot11.Left10.expected,
    Slot11.Left11.expected,
    Slot11.Left12.expected,
    Slot11.Left13.expected,
    Slot11.Left14.expected,
    Slot11.Left15.expected,
    Slot11.Left16.expected,
    Slot11.Left17.expected,
    Slot11.Left18.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 3409754499577347689152512 }, { target := 57, numerator := 119162258203406647160733696 }, { target := 59, numerator := 1437734474976480842263560192 }, { target := 67, numerator := 119165066814767461614747648 }, { target := 74, numerator := 3409854807125948205367296 }, { target := 152, numerator := 157117936397977001819897856 }, { target := 153, numerator := 5490872761591161147147419648 }, { target := 155, numerator := 66249307340025212103552925696 }, { target := 163, numerator := 5491002179477759663196340224 }, { target := 170, numerator := 157122558465355520250216448 }, { target := 473, numerator := 35602878992124583555891200 }, { target := 475, numerator := 1270037317480481168975462400 }, { target := 478, numerator := 1270037317480481168975462400 }, { target := 485, numerator := 35602256414512095858524160 }, { target := 508, numerator := 35602878992124583555891200 }, { target := 510, numerator := 1270037317480481168975462400 }, { target := 513, numerator := 1270037317480481168975462400 }, { target := 520, numerator := 35602256414512095858524160 }, { target := 569, numerator := 30592103430270012536913920 }, { target := 571, numerator := 1091291324649894930378915840 }, { target := 574, numerator := 1091291324649894930378915840 }, { target := 581, numerator := 30591568474691874959917056 }, { target := 604, numerator := 646390047479239661448069120 }, { target := 606, numerator := 23058233075145624778954506240 }, { target := 609, numerator := 23058233075145624778954506240 }, { target := 616, numerator := 646378744236808495920316416 }, { target := 630, numerator := 30592103430270012536913920 }, { target := 632, numerator := 1091291324649894930378915840 }, { target := 635, numerator := 1091291324649894930378915840 }, { target := 642, numerator := 30591568474691874959917056 }, { target := 679, numerator := 35602878992124583555891200 }, { target := 681, numerator := 1270037317480481168975462400 }, { target := 684, numerator := 1270037317480481168975462400 }, { target := 691, numerator := 35602256414512095858524160 }, { target := 705, numerator := 35602878992124583555891200 }, { target := 707, numerator := 1270037317480481168975462400 }, { target := 710, numerator := 1270037317480481168975462400 }, { target := 717, numerator := 35602256414512095858524160 }, { target := 785, numerator := 4483325502711984595927040 }, { target := 787, numerator := 159930625164208739796910080 }, { target := 790, numerator := 159930625164208739796910080 }, { target := 797, numerator := 4483247104049671330332672 }, { target := 820, numerator := 30592103430270012536913920 }, { target := 822, numerator := 1091291324649894930378915840 }, { target := 825, numerator := 1091291324649894930378915840 }, { target := 832, numerator := 30591568474691874959917056 }, { target := 846, numerator := 4483325502711984595927040 }, { target := 848, numerator := 159930625164208739796910080 }, { target := 851, numerator := 159930625164208739796910080 }, { target := 858, numerator := 4483247104049671330332672 }, { target := 895, numerator := 35602878992124583555891200 }, { target := 897, numerator := 1270037317480481168975462400 }, { target := 900, numerator := 1270037317480481168975462400 }, { target := 907, numerator := 35602256414512095858524160 }, { target := 921, numerator := 35602878992124583555891200 }, { target := 923, numerator := 1270037317480481168975462400 }, { target := 926, numerator := 1270037317480481168975462400 }, { target := 933, numerator := 35602256414512095858524160 }, { target := 966, numerator := 4219600473140691384401920 }, { target := 968, numerator := 150522941331019990397091840 }, { target := 971, numerator := 150522941331019990397091840 }, { target := 978, numerator := 4219526686164396546195456 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk2

namespace RouteChunk3

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot12.Left5.expected,
    Slot12.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 283, numerator := 157117687625326035361333248 }, { target := 284, numerator := 5490864067618949339633680384 }, { target := 286, numerator := 66249202444198615173161811968 }, { target := 294, numerator := 5490993485300634072637243392 }, { target := 301, numerator := 157122309685386204397174784 }, { target := 660, numerator := 3409429181495314627952640 }, { target := 661, numerator := 119150889162821975796613120 }, { target := 663, numerator := 1437597303510931010213642240 }, { target := 671, numerator := 119153697506218612422082560 }, { target := 678, numerator := 3409529479473765936005120 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk8.Parent1
