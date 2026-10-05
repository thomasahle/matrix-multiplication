import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk1Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 32; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk1.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot3.Left4.expected,
    Slot3.Left5.expected,
    Slot3.Left6.expected,
    Slot3.Left7.expected,
    Slot3.Left8.expected,
    Slot3.Left9.expected,
    Slot3.Left10.expected,
    Slot3.Left11.expected,
    Slot3.Left12.expected,
    Slot3.Left13.expected,
    Slot3.Left14.expected,
    Slot3.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 4747050532283277807452160 }, { target := 112, numerator := 169338308997397489196728320 }, { target := 115, numerator := 169338308997397489196728320 }, { target := 122, numerator := 4746967521934946114469888 }, { target := 206, numerator := 36130329051267169978941440 }, { target := 208, numerator := 1288852685146858667775098880 }, { target := 211, numerator := 1288852685146858667775098880 }, { target := 218, numerator := 36129697250282645426798592 }, { target := 241, numerator := 36130329051267169978941440 }, { target := 243, numerator := 1288852685146858667775098880 }, { target := 246, numerator := 1288852685146858667775098880 }, { target := 253, numerator := 36129697250282645426798592 }, { target := 302, numerator := 5010775561854571018977280 }, { target := 304, numerator := 178745992830586238596546560 }, { target := 307, numerator := 178745992830586238596546560 }, { target := 314, numerator := 5010687939820220898607104 }, { target := 337, numerator := 32174453607697771806064640 }, { target := 339, numerator := 1147737427649027426777825280 }, { target := 342, numerator := 1147737427649027426777825280 }, { target := 349, numerator := 32173890982003523664740352 }, { target := 363, numerator := 5010775561854571018977280 }, { target := 365, numerator := 178745992830586238596546560 }, { target := 368, numerator := 178745992830586238596546560 }, { target := 375, numerator := 5010687939820220898607104 }, { target := 473, numerator := 35866604021695876767416320 }, { target := 475, numerator := 1279445001313669918375280640 }, { target := 478, numerator := 1279445001313669918375280640 }, { target := 485, numerator := 35865976832397370642661376 }, { target := 508, numerator := 35866604021695876767416320 }, { target := 510, numerator := 1279445001313669918375280640 }, { target := 513, numerator := 1279445001313669918375280640 }, { target := 520, numerator := 35865976832397370642661376 }, { target := 569, numerator := 32174453607697771806064640 }, { target := 571, numerator := 1147737427649027426777825280 }, { target := 574, numerator := 1147737427649027426777825280 }, { target := 581, numerator := 32173890982003523664740352 }, { target := 604, numerator := 634258696118960173717913600 }, { target := 606, numerator := 22625479618818942306562867200 }, { target := 609, numerator := 22625479618818942306562867200 }, { target := 616, numerator := 634247605014085855850004480 }, { target := 630, numerator := 32174453607697771806064640 }, { target := 632, numerator := 1147737427649027426777825280 }, { target := 635, numerator := 1147737427649027426777825280 }, { target := 642, numerator := 32173890982003523664740352 }, { target := 679, numerator := 36130329051267169978941440 }, { target := 681, numerator := 1288852685146858667775098880 }, { target := 684, numerator := 1288852685146858667775098880 }, { target := 691, numerator := 36129697250282645426798592 }, { target := 705, numerator := 35866604021695876767416320 }, { target := 707, numerator := 1279445001313669918375280640 }, { target := 710, numerator := 1279445001313669918375280640 }, { target := 717, numerator := 35865976832397370642661376 }, { target := 785, numerator := 5010775561854571018977280 }, { target := 787, numerator := 178745992830586238596546560 }, { target := 790, numerator := 178745992830586238596546560 }, { target := 797, numerator := 5010687939820220898607104 }, { target := 820, numerator := 32174453607697771806064640 }, { target := 822, numerator := 1147737427649027426777825280 }, { target := 825, numerator := 1147737427649027426777825280 }, { target := 832, numerator := 32173890982003523664740352 }, { target := 846, numerator := 5010775561854571018977280 }, { target := 848, numerator := 178745992830586238596546560 }, { target := 851, numerator := 178745992830586238596546560 }, { target := 858, numerator := 5010687939820220898607104 }]

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
    Slot3.Left16.expected,
    Slot3.Left17.expected,
    Slot3.Left18.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left6.expected,
    Slot8.Left14.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 4989146219062740866039808 }, { target := 57, numerator := 166418380865867776090177536 }, { target := 59, numerator := 2038137840611671370505388032 }, { target := 67, numerator := 166418522808631981693206528 }, { target := 74, numerator := 5440524209236558498234368 }, { target := 110, numerator := 12927585298826171252736000 }, { target := 112, numerator := 450064809825837786375127040 }, { target := 115, numerator := 450065306563025061155962880 }, { target := 122, numerator := 12927530105805362943754240 }, { target := 152, numerator := 243990335275671914098458624 }, { target := 153, numerator := 8138562142828013578258219008 }, { target := 155, numerator := 99673553997841260145746640896 }, { target := 163, numerator := 8138569084429062702612086784 }, { target := 170, numerator := 266064626611887359397986304 }, { target := 206, numerator := 400689545429573355700224000 }, { target := 208, numerator := 13949725327230052089578127360 }, { target := 211, numerator := 13949740723562249191340113920 }, { target := 218, numerator := 400687834725995899948892160 }, { target := 257, numerator := 148826651092107549086842880 }, { target := 260, numerator := 520752488698904136353054720 }, { target := 262, numerator := 149019478182026964128235520 }, { target := 283, numerator := 243990424317747521724088320 }, { target := 284, numerator := 8138565112922975906499133440 }, { target := 286, numerator := 99673590372807182992571105280 }, { target := 294, numerator := 8138572054526558305643397120 }, { target := 301, numerator := 266064723709776800482590720 }, { target := 302, numerator := 4703242570800564793245696000 }, { target := 304, numerator := 163740089449213955547793981440 }, { target := 307, numerator := 163740270169389586693415239680 }, { target := 314, numerator := 4703222490781050221510000640 }, { target := 353, numerator := 7053261127103938239957827584 }, { target := 356, numerator := 24679741554551428714747396096 }, { target := 358, numerator := 7062399677273554408529985536 }, { target := 660, numerator := 4989472706673302160015360 }, { target := 661, numerator := 166429271214062979640197120 }, { target := 663, numerator := 2038271215486721808861757440 }, { target := 671, numerator := 166429413166115859474677760 }, { target := 678, numerator := 5440880234831175808450560 }, { target := 679, numerator := 400692512211012258103296000 }, { target := 681, numerator := 13949828613643812258384445440 }, { target := 684, numerator := 13949844010090006725714247680 }, { target := 691, numerator := 400690801494768428399984640 }, { target := 695, numerator := 7051380027605580585338142720 }, { target := 698, numerator := 24673159485828712172806471680 }, { target := 700, numerator := 7060516140530661212427386880 }, { target := 895, numerator := 36130329051267169978941440 }, { target := 897, numerator := 1288852685146858667775098880 }, { target := 900, numerator := 1288852685146858667775098880 }, { target := 907, numerator := 36129697250282645426798592 }, { target := 921, numerator := 35866604021695876767416320 }, { target := 923, numerator := 1279445001313669918375280640 }, { target := 926, numerator := 1279445001313669918375280640 }, { target := 933, numerator := 35865976832397370642661376 }, { target := 966, numerator := 17412559013448657183703040 }, { target := 968, numerator := 610052816331024397731102720 }, { target := 971, numerator := 610053313131543542271836160 }, { target := 978, numerator := 17412425414728661191360512 }, { target := 982, numerator := 150736941545711283239649280 }, { target := 985, numerator := 527436698150316416507576320 }, { target := 987, numerator := 150932243701395910421381120 }]

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
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left3.expected,
    Slot15.Left11.expected,
    Slot15.Left18.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot16.Left5.expected,
    Slot16.Left12.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 148826651092107549086842880 }, { target := 15, numerator := 7053261127103938239957827584 }, { target := 20, numerator := 7051380027605580585338142720 }, { target := 28, numerator := 150736941545711283239649280 }, { target := 56, numerator := 12927585298826171252736000 }, { target := 57, numerator := 400689545429573355700224000 }, { target := 59, numerator := 4703242570800564793245696000 }, { target := 67, numerator := 400692512211012258103296000 }, { target := 74, numerator := 12929233510736672587776000 }, { target := 110, numerator := 4989146219062740866039808 }, { target := 112, numerator := 243990335275671914098458624 }, { target := 115, numerator := 243990424317747521724088320 }, { target := 122, numerator := 4989472706673302160015360 }, { target := 136, numerator := 520752488698904136353054720 }, { target := 137, numerator := 24679741554551428714747396096 }, { target := 142, numerator := 24673159485828712172806471680 }, { target := 150, numerator := 527436698150316416507576320 }, { target := 152, numerator := 450064809825837786375127040 }, { target := 153, numerator := 13949725327230052089578127360 }, { target := 155, numerator := 163740089449213955547793981440 }, { target := 163, numerator := 13949828613643812258384445440 }, { target := 170, numerator := 450122191166815657934192640 }, { target := 206, numerator := 166418380865867776090177536 }, { target := 208, numerator := 8138562142828013578258219008 }, { target := 211, numerator := 8138565112922975906499133440 }, { target := 218, numerator := 166429271214062979640197120 }, { target := 267, numerator := 149019478182026964128235520 }, { target := 268, numerator := 7062399677273554408529985536 }, { target := 273, numerator := 7060516140530661212427386880 }, { target := 281, numerator := 150932243701395910421381120 }, { target := 283, numerator := 450065306563025061155962880 }, { target := 284, numerator := 13949740723562249191340113920 }, { target := 286, numerator := 163740270169389586693415239680 }, { target := 294, numerator := 13949844010090006725714247680 }, { target := 301, numerator := 450122687967334802474926080 }, { target := 302, numerator := 2038137840611671370505388032 }, { target := 304, numerator := 99673553997841260145746640896 }, { target := 307, numerator := 99673590372807182992571105280 }, { target := 314, numerator := 2038271215486721808861757440 }, { target := 660, numerator := 12927530105805362943754240 }, { target := 661, numerator := 400687834725995899948892160 }, { target := 663, numerator := 4703222490781050221510000640 }, { target := 671, numerator := 400690801494768428399984640 }, { target := 678, numerator := 12929178310678989861027840 }, { target := 679, numerator := 166418522808631981693206528 }, { target := 681, numerator := 8138569084429062702612086784 }, { target := 684, numerator := 8138572054526558305643397120 }, { target := 691, numerator := 166429413166115859474677760 }, { target := 966, numerator := 5440524209236558498234368 }, { target := 968, numerator := 266064626611887359397986304 }, { target := 971, numerator := 266064723709776800482590720 }, { target := 978, numerator := 5440880234831175808450560 }]

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
    Slot22.Left0.expected,
    Slot22.Left2.expected,
    Slot22.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 4747050532283277807452160 }, { target := 57, numerator := 36130329051267169978941440 }, { target := 58, numerator := 36130329051267169978941440 }, { target := 59, numerator := 5010775561854571018977280 }, { target := 60, numerator := 32174453607697771806064640 }, { target := 61, numerator := 5010775561854571018977280 }, { target := 62, numerator := 35866604021695876767416320 }, { target := 63, numerator := 35866604021695876767416320 }, { target := 64, numerator := 32174453607697771806064640 }, { target := 65, numerator := 634258696118960173717913600 }, { target := 66, numerator := 32174453607697771806064640 }, { target := 67, numerator := 36130329051267169978941440 }, { target := 68, numerator := 35866604021695876767416320 }, { target := 69, numerator := 5010775561854571018977280 }, { target := 70, numerator := 32174453607697771806064640 }, { target := 71, numerator := 5010775561854571018977280 }, { target := 72, numerator := 36130329051267169978941440 }, { target := 73, numerator := 35866604021695876767416320 }, { target := 74, numerator := 4483325502711984595927040 }, { target := 152, numerator := 169338308997397489196728320 }, { target := 153, numerator := 1288852685146858667775098880 }, { target := 154, numerator := 1288852685146858667775098880 }, { target := 155, numerator := 178745992830586238596546560 }, { target := 156, numerator := 1147737427649027426777825280 }, { target := 157, numerator := 178745992830586238596546560 }, { target := 158, numerator := 1279445001313669918375280640 }, { target := 159, numerator := 1279445001313669918375280640 }, { target := 160, numerator := 1147737427649027426777825280 }, { target := 161, numerator := 22625479618818942306562867200 }, { target := 162, numerator := 1147737427649027426777825280 }, { target := 163, numerator := 1288852685146858667775098880 }, { target := 164, numerator := 1279445001313669918375280640 }, { target := 165, numerator := 178745992830586238596546560 }, { target := 166, numerator := 1147737427649027426777825280 }, { target := 167, numerator := 178745992830586238596546560 }, { target := 168, numerator := 1288852685146858667775098880 }, { target := 169, numerator := 1279445001313669918375280640 }, { target := 170, numerator := 159930625164208739796910080 }, { target := 283, numerator := 169338308997397489196728320 }, { target := 284, numerator := 1288852685146858667775098880 }, { target := 285, numerator := 1288852685146858667775098880 }, { target := 286, numerator := 178745992830586238596546560 }, { target := 287, numerator := 1147737427649027426777825280 }, { target := 288, numerator := 178745992830586238596546560 }, { target := 289, numerator := 1279445001313669918375280640 }, { target := 290, numerator := 1279445001313669918375280640 }, { target := 291, numerator := 1147737427649027426777825280 }, { target := 292, numerator := 22625479618818942306562867200 }, { target := 293, numerator := 1147737427649027426777825280 }, { target := 294, numerator := 1288852685146858667775098880 }, { target := 295, numerator := 1279445001313669918375280640 }, { target := 296, numerator := 178745992830586238596546560 }, { target := 297, numerator := 1147737427649027426777825280 }, { target := 298, numerator := 178745992830586238596546560 }, { target := 299, numerator := 1288852685146858667775098880 }, { target := 300, numerator := 1279445001313669918375280640 }, { target := 301, numerator := 159930625164208739796910080 }]

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
    Slot22.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 660, numerator := 4746967521934946114469888 }, { target := 661, numerator := 36129697250282645426798592 }, { target := 662, numerator := 36129697250282645426798592 }, { target := 663, numerator := 5010687939820220898607104 }, { target := 664, numerator := 32173890982003523664740352 }, { target := 665, numerator := 5010687939820220898607104 }, { target := 666, numerator := 35865976832397370642661376 }, { target := 667, numerator := 35865976832397370642661376 }, { target := 668, numerator := 32173890982003523664740352 }, { target := 669, numerator := 634247605014085855850004480 }, { target := 670, numerator := 32173890982003523664740352 }, { target := 671, numerator := 36129697250282645426798592 }, { target := 672, numerator := 35865976832397370642661376 }, { target := 673, numerator := 5010687939820220898607104 }, { target := 674, numerator := 32173890982003523664740352 }, { target := 675, numerator := 5010687939820220898607104 }, { target := 676, numerator := 36129697250282645426798592 }, { target := 677, numerator := 35865976832397370642661376 }, { target := 678, numerator := 4483247104049671330332672 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk1.Parent3
