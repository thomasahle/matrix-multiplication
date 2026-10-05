import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk6Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 62; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk6.Parent3

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
    Slot10.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 4320688630664619727257600 }, { target := 57, numerator := 36455810321232728948736000 }, { target := 58, numerator := 36725853360649267681689600 }, { target := 59, numerator := 4590731670081158460211200 }, { target := 60, numerator := 31324992572318493022617600 }, { target := 61, numerator := 4590731670081158460211200 }, { target := 62, numerator := 36455810321232728948736000 }, { target := 63, numerator := 36455810321232728948736000 }, { target := 64, numerator := 31324992572318493022617600 }, { target := 65, numerator := 661875489609936434469273600 }, { target := 66, numerator := 31324992572318493022617600 }, { target := 67, numerator := 36455810321232728948736000 }, { target := 68, numerator := 36455810321232728948736000 }, { target := 69, numerator := 4590731670081158460211200 }, { target := 70, numerator := 31324992572318493022617600 }, { target := 71, numerator := 4590731670081158460211200 }, { target := 72, numerator := 36455810321232728948736000 }, { target := 73, numerator := 36455810321232728948736000 }, { target := 74, numerator := 4320688630664619727257600 }, { target := 110, numerator := 5288565038639316650164224 }, { target := 112, numerator := 243691569431316460902285312 }, { target := 115, numerator := 243691183582322161191223296 }, { target := 122, numerator := 5288060466877540104929280 }, { target := 206, numerator := 176405820192523540871774208 }, { target := 208, numerator := 8128596484197748220576661504 }, { target := 211, numerator := 8128583613786244798199365632 }, { target := 218, numerator := 176388989654403680839925760 }, { target := 257, numerator := 155281166946236887696670720 }, { target := 260, numerator := 547480435776829129081487360 }, { target := 262, numerator := 155245163549519822098268160 }, { target := 302, numerator := 2160454726021564292237623296 }, { target := 304, numerator := 99551503862181468100727144448 }, { target := 307, numerator := 99551346237329135764487798784 }, { target := 314, numerator := 2160248601214668160232325120 }, { target := 353, numerator := 7014627797254137159660601344 }, { target := 356, numerator := 24731727348382232696504451072 }, { target := 358, numerator := 7013001389928807505154015232 }, { target := 679, numerator := 176405970653846441646096384 }, { target := 681, numerator := 8128603417298815998222139392 }, { target := 684, numerator := 8128590546876335051753127936 }, { target := 691, numerator := 176389140101371357802004480 }, { target := 695, numerator := 7013439835219598829131137024 }, { target := 698, numerator := 24727538907599967340736806912 }, { target := 700, numerator := 7011813703334422384604086272 }, { target := 966, numerator := 5767032045463778994683904 }, { target := 968, numerator := 265738830826849373521969152 }, { target := 971, numerator := 265738410069328462155350016 }, { target := 978, numerator := 5766481824090279515258880 }, { target := 982, numerator := 155281166946236887696670720 }, { target := 985, numerator := 547480435776829129081487360 }, { target := 987, numerator := 155245163549519822098268160 }]

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
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot12.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 10943365393331262377164800 }, { target := 112, numerator := 390375239918927195249049600 }, { target := 115, numerator := 390375239918927195249049600 }, { target := 122, numerator := 10943174029753595870576640 }, { target := 152, numerator := 150421742493031619796926464 }, { target := 153, numerator := 1269183452284954292036567040 }, { target := 154, numerator := 1278584811190768768273874944 }, { target := 155, numerator := 159823101398846096034234368 }, { target := 156, numerator := 1090557633074479243527716864 }, { target := 157, numerator := 159823101398846096034234368 }, { target := 158, numerator := 1269183452284954292036567040 }, { target := 159, numerator := 1269183452284954292036567040 }, { target := 160, numerator := 1090557633074479243527716864 }, { target := 161, numerator := 23042730678151281257641672704 }, { target := 162, numerator := 1090557633074479243527716864 }, { target := 163, numerator := 1269183452284954292036567040 }, { target := 164, numerator := 1269183452284954292036567040 }, { target := 165, numerator := 159823101398846096034234368 }, { target := 166, numerator := 1090557633074479243527716864 }, { target := 167, numerator := 159823101398846096034234368 }, { target := 168, numerator := 1269183452284954292036567040 }, { target := 169, numerator := 1269183452284954292036567040 }, { target := 170, numerator := 150421742493031619796926464 }, { target := 283, numerator := 150421908513728283182891008 }, { target := 284, numerator := 1269184853084582389355642880 }, { target := 285, numerator := 1278586222366690407054573568 }, { target := 286, numerator := 159823277795836300881821696 }, { target := 287, numerator := 1090558836724530053075959808 }, { target := 288, numerator := 159823277795836300881821696 }, { target := 289, numerator := 1269184853084582389355642880 }, { target := 290, numerator := 1269184853084582389355642880 }, { target := 291, numerator := 1090558836724530053075959808 }, { target := 292, numerator := 23042756110446751380079116288 }, { target := 293, numerator := 1090558836724530053075959808 }, { target := 294, numerator := 1269184853084582389355642880 }, { target := 295, numerator := 1269184853084582389355642880 }, { target := 296, numerator := 159823277795836300881821696 }, { target := 297, numerator := 1090558836724530053075959808 }, { target := 298, numerator := 159823277795836300881821696 }, { target := 299, numerator := 1269184853084582389355642880 }, { target := 300, numerator := 1269184853084582389355642880 }, { target := 301, numerator := 150421908513728283182891008 }, { target := 660, numerator := 4320670183920546017705984 }, { target := 661, numerator := 36455654676829607024394240 }, { target := 662, numerator := 36725696563324641150500864 }, { target := 663, numerator := 4590712070415580143812608 }, { target := 664, numerator := 31324858833423958628368384 }, { target := 665, numerator := 4590712070415580143812608 }, { target := 666, numerator := 36455654676829607024394240 }, { target := 667, numerator := 36455654676829607024394240 }, { target := 668, numerator := 31324858833423958628368384 }, { target := 669, numerator := 661872663799328643087335424 }, { target := 670, numerator := 31324858833423958628368384 }, { target := 671, numerator := 36455654676829607024394240 }, { target := 672, numerator := 36455654676829607024394240 }, { target := 673, numerator := 4590712070415580143812608 }, { target := 674, numerator := 31324858833423958628368384 }, { target := 675, numerator := 4590712070415580143812608 }, { target := 676, numerator := 36455654676829607024394240 }, { target := 677, numerator := 36455654676829607024394240 }, { target := 678, numerator := 4320670183920546017705984 }]

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
    Slot12.Left1.expected,
    Slot12.Left3.expected,
    Slot12.Left11.expected,
    Slot12.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left2.expected,
    Slot15.Left3.expected,
    Slot15.Left4.expected,
    Slot15.Left5.expected,
    Slot15.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 10943365393331262377164800 }, { target := 57, numerator := 382442821844213409670758400 }, { target := 59, numerator := 4614306895175931214482636800 }, { target := 67, numerator := 382451835883310084731699200 }, { target := 74, numerator := 10943687323299000772198400 }, { target := 110, numerator := 4320688630664619727257600 }, { target := 112, numerator := 150421742493031619796926464 }, { target := 115, numerator := 150421908513728283182891008 }, { target := 122, numerator := 4320670183920546017705984 }, { target := 152, numerator := 390375239918927195249049600 }, { target := 153, numerator := 13642622992711676557315276800 }, { target := 155, numerator := 164603035402761808824080793600 }, { target := 163, numerator := 13642944544405193750898278400 }, { target := 170, numerator := 390386723907981380734156800 }, { target := 206, numerator := 418898632165446138619494400 }, { target := 208, numerator := 14911806444996630849351843840 }, { target := 211, numerator := 14911807845796258946670919680 }, { target := 218, numerator := 418891788850110857069199360 }, { target := 241, numerator := 36725853360649267681689600 }, { target := 243, numerator := 1278584811190768768273874944 }, { target := 246, numerator := 1278586222366690407054573568 }, { target := 253, numerator := 36725696563324641150500864 }, { target := 283, numerator := 390375239918927195249049600 }, { target := 284, numerator := 13642622992711676557315276800 }, { target := 286, numerator := 164603035402761808824080793600 }, { target := 294, numerator := 13642944544405193750898278400 }, { target := 301, numerator := 390386723907981380734156800 }, { target := 302, numerator := 4618897626846012372942848000 }, { target := 304, numerator := 164762858504160654920115027968 }, { target := 307, numerator := 164762858680557645124962615296 }, { target := 314, numerator := 4618816918148964540479438848 }, { target := 337, numerator := 31324992572318493022617600 }, { target := 339, numerator := 1090557633074479243527716864 }, { target := 342, numerator := 1090558836724530053075959808 }, { target := 349, numerator := 31324858833423958628368384 }, { target := 363, numerator := 4590731670081158460211200 }, { target := 365, numerator := 159823101398846096034234368 }, { target := 368, numerator := 159823277795836300881821696 }, { target := 375, numerator := 4590712070415580143812608 }, { target := 473, numerator := 36455810321232728948736000 }, { target := 475, numerator := 1269183452284954292036567040 }, { target := 478, numerator := 1269184853084582389355642880 }, { target := 485, numerator := 36455654676829607024394240 }, { target := 660, numerator := 10943174029753595870576640 }, { target := 661, numerator := 382436134173281250044805120 }, { target := 663, numerator := 4614226206078548960335626240 }, { target := 671, numerator := 382445148054751938147778560 }, { target := 678, numerator := 10943495954091834731397120 }, { target := 679, numerator := 382451835883310084731699200 }, { target := 681, numerator := 13642944544405193750898278400 }, { target := 684, numerator := 13642944544405193750898278400 }, { target := 691, numerator := 382445148054751938147778560 }, { target := 966, numerator := 10943687323299000772198400 }, { target := 968, numerator := 390386723907981380734156800 }, { target := 971, numerator := 390386723907981380734156800 }, { target := 978, numerator := 10943495954091834731397120 }]

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
    Slot15.Left7.expected,
    Slot15.Left8.expected,
    Slot15.Left9.expected,
    Slot15.Left10.expected,
    Slot15.Left11.expected,
    Slot15.Left12.expected,
    Slot15.Left13.expected,
    Slot15.Left14.expected,
    Slot15.Left15.expected,
    Slot15.Left16.expected,
    Slot15.Left17.expected,
    Slot15.Left18.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot16.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 5288565038639316650164224 }, { target := 57, numerator := 176405820192523540871774208 }, { target := 59, numerator := 2160454726021564292237623296 }, { target := 67, numerator := 176405970653846441646096384 }, { target := 74, numerator := 5767032045463778994683904 }, { target := 152, numerator := 243691569431316460902285312 }, { target := 153, numerator := 8128596484197748220576661504 }, { target := 155, numerator := 99551503862181468100727144448 }, { target := 163, numerator := 8128603417298815998222139392 }, { target := 170, numerator := 265738830826849373521969152 }, { target := 283, numerator := 243691183582322161191223296 }, { target := 284, numerator := 8128583613786244798199365632 }, { target := 286, numerator := 99551346237329135764487798784 }, { target := 294, numerator := 8128590546876335051753127936 }, { target := 301, numerator := 265738410069328462155350016 }, { target := 508, numerator := 36455810321232728948736000 }, { target := 510, numerator := 1269183452284954292036567040 }, { target := 513, numerator := 1269184853084582389355642880 }, { target := 520, numerator := 36455654676829607024394240 }, { target := 569, numerator := 31324992572318493022617600 }, { target := 571, numerator := 1090557633074479243527716864 }, { target := 574, numerator := 1090558836724530053075959808 }, { target := 581, numerator := 31324858833423958628368384 }, { target := 604, numerator := 661875489609936434469273600 }, { target := 606, numerator := 23042730678151281257641672704 }, { target := 609, numerator := 23042756110446751380079116288 }, { target := 616, numerator := 661872663799328643087335424 }, { target := 630, numerator := 31324992572318493022617600 }, { target := 632, numerator := 1090557633074479243527716864 }, { target := 635, numerator := 1090558836724530053075959808 }, { target := 642, numerator := 31324858833423958628368384 }, { target := 679, numerator := 36455810321232728948736000 }, { target := 681, numerator := 1269183452284954292036567040 }, { target := 684, numerator := 1269184853084582389355642880 }, { target := 691, numerator := 36455654676829607024394240 }, { target := 705, numerator := 36455810321232728948736000 }, { target := 707, numerator := 1269183452284954292036567040 }, { target := 710, numerator := 1269184853084582389355642880 }, { target := 717, numerator := 36455654676829607024394240 }, { target := 785, numerator := 4590731670081158460211200 }, { target := 787, numerator := 159823101398846096034234368 }, { target := 790, numerator := 159823277795836300881821696 }, { target := 797, numerator := 4590712070415580143812608 }, { target := 820, numerator := 31324992572318493022617600 }, { target := 822, numerator := 1090557633074479243527716864 }, { target := 825, numerator := 1090558836724530053075959808 }, { target := 832, numerator := 31324858833423958628368384 }, { target := 846, numerator := 4590731670081158460211200 }, { target := 848, numerator := 159823101398846096034234368 }, { target := 851, numerator := 159823277795836300881821696 }, { target := 858, numerator := 4590712070415580143812608 }, { target := 895, numerator := 36455810321232728948736000 }, { target := 897, numerator := 1269183452284954292036567040 }, { target := 900, numerator := 1269184853084582389355642880 }, { target := 907, numerator := 36455654676829607024394240 }, { target := 921, numerator := 36455810321232728948736000 }, { target := 923, numerator := 1269183452284954292036567040 }, { target := 926, numerator := 1269184853084582389355642880 }, { target := 933, numerator := 36455654676829607024394240 }, { target := 966, numerator := 4320688630664619727257600 }, { target := 968, numerator := 150421742493031619796926464 }, { target := 971, numerator := 150421908513728283182891008 }, { target := 978, numerator := 4320670183920546017705984 }]

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

namespace RouteChunk4

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot16.Left12.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 155281166946236887696670720 }, { target := 15, numerator := 7014627797254137159660601344 }, { target := 20, numerator := 7013439835219598829131137024 }, { target := 28, numerator := 155281166946236887696670720 }, { target := 136, numerator := 547480435776829129081487360 }, { target := 137, numerator := 24731727348382232696504451072 }, { target := 142, numerator := 24727538907599967340736806912 }, { target := 150, numerator := 547480435776829129081487360 }, { target := 267, numerator := 155245163549519822098268160 }, { target := 268, numerator := 7013001389928807505154015232 }, { target := 273, numerator := 7011813703334422384604086272 }, { target := 281, numerator := 155245163549519822098268160 }, { target := 660, numerator := 5288060466877540104929280 }, { target := 661, numerator := 176388989654403680839925760 }, { target := 663, numerator := 2160248601214668160232325120 }, { target := 671, numerator := 176389140101371357802004480 }, { target := 678, numerator := 5766481824090279515258880 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk4

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk6.Parent3
