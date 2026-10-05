import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk7Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 66; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk7.Parent3

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
    Slot7.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 4606597022906053281447936 }, { target := 57, numerator := 34293555614967285539667968 }, { target := 58, numerator := 34805399728623513682051072 }, { target := 59, numerator := 5118441136562281423831040 }, { target := 60, numerator := 30710646819373688542986240 }, { target := 61, numerator := 5118441136562281423831040 }, { target := 62, numerator := 34037633558139171468476416 }, { target := 63, numerator := 34805399728623513682051072 }, { target := 64, numerator := 30710646819373688542986240 }, { target := 65, numerator := 620099143694520394497130496 }, { target := 66, numerator := 30710646819373688542986240 }, { target := 67, numerator := 34037633558139171468476416 }, { target := 68, numerator := 34037633558139171468476416 }, { target := 69, numerator := 5118441136562281423831040 }, { target := 70, numerator := 30710646819373688542986240 }, { target := 71, numerator := 5118441136562281423831040 }, { target := 72, numerator := 34805399728623513682051072 }, { target := 73, numerator := 34805399728623513682051072 }, { target := 74, numerator := 4606597022906053281447936 }, { target := 152, numerator := 169478721001600547876241408 }, { target := 153, numerator := 1261674923011915189745352704 }, { target := 154, numerator := 1280505892012093028398268416 }, { target := 155, numerator := 188309690001778386529157120 }, { target := 156, numerator := 1129858140010670319174942720 }, { target := 157, numerator := 188309690001778386529157120 }, { target := 158, numerator := 1252259438511826270418894848 }, { target := 159, numerator := 1280505892012093028398268416 }, { target := 160, numerator := 1129858140010670319174942720 }, { target := 161, numerator := 22813718943715451528007385088 }, { target := 162, numerator := 1129858140010670319174942720 }, { target := 163, numerator := 1252259438511826270418894848 }, { target := 164, numerator := 1252259438511826270418894848 }, { target := 165, numerator := 188309690001778386529157120 }, { target := 166, numerator := 1129858140010670319174942720 }, { target := 167, numerator := 188309690001778386529157120 }, { target := 168, numerator := 1280505892012093028398268416 }, { target := 169, numerator := 1280505892012093028398268416 }, { target := 170, numerator := 169478721001600547876241408 }, { target := 283, numerator := 169478907774884294185451520 }, { target := 284, numerator := 1261676313435249745602805760 }, { target := 285, numerator := 1280507303188014667178967040 }, { target := 286, numerator := 188309897527649215761612800 }, { target := 287, numerator := 1129859385165895294569676800 }, { target := 288, numerator := 188309897527649215761612800 }, { target := 289, numerator := 1252260818558867284814725120 }, { target := 290, numerator := 1280507303188014667178967040 }, { target := 291, numerator := 1129859385165895294569676800 }, { target := 292, numerator := 22813744085474702489519390720 }, { target := 293, numerator := 1129859385165895294569676800 }, { target := 294, numerator := 1252260818558867284814725120 }, { target := 295, numerator := 1252260818558867284814725120 }, { target := 296, numerator := 188309897527649215761612800 }, { target := 297, numerator := 1129859385165895294569676800 }, { target := 298, numerator := 188309897527649215761612800 }, { target := 299, numerator := 1280507303188014667178967040 }, { target := 300, numerator := 1280507303188014667178967040 }, { target := 301, numerator := 169478907774884294185451520 }]

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
    Slot7.Left12.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left6.expected,
    Slot9.Left14.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 13016603709425129934028800 }, { target := 57, numerator := 442387731900096062139924480 }, { target := 59, numerator := 4871086398158002872783994880 }, { target := 67, numerator := 442394624462293268986593280 }, { target := 74, numerator := 13014880568875828222361600 }, { target := 110, numerator := 4451823643255135134547968 }, { target := 112, numerator := 178806538351404179741736960 }, { target := 115, numerator := 178841295524135783375044608 }, { target := 122, numerator := 4417372316166675719258112 }, { target := 152, numerator := 432892904592090471176601600 }, { target := 153, numerator := 14712479114615170740372111360 }, { target := 155, numerator := 161997613700937472417107804160 }, { target := 163, numerator := 14712708340405264513457192960 }, { target := 170, numerator := 432835598144567027905331200 }, { target := 206, numerator := 218687426174550425481510912 }, { target := 208, numerator := 8783533398609211916172656640 }, { target := 211, numerator := 8785240779057063824480796672 }, { target := 218, numerator := 216995069816120218440695808 }, { target := 257, numerator := 138297570860224178752061440 }, { target := 260, numerator := 479310449703037267829850112 }, { target := 262, numerator := 138329516548579880645689344 }, { target := 302, numerator := 2440707537256879767089577984 }, { target := 304, numerator := 98030492857974269707529748480 }, { target := 307, numerator := 98049548440642799627931746304 }, { target := 314, numerator := 2421819634134144578859565056 }, { target := 353, numerator := 7109001934958136343312465920 }, { target := 356, numerator := 24638313552364465860447830016 }, { target := 358, numerator := 7110644060404893349620744192 }, { target := 660, numerator := 4606410249622306972237824 }, { target := 661, numerator := 34292165191632729682214912 }, { target := 662, numerator := 34803988552701874901352448 }, { target := 663, numerator := 5118233610691452191375360 }, { target := 664, numerator := 30709401664148713148252160 }, { target := 665, numerator := 5118233610691452191375360 }, { target := 666, numerator := 34036253511098157072646144 }, { target := 667, numerator := 34803988552701874901352448 }, { target := 668, numerator := 30709401664148713148252160 }, { target := 669, numerator := 620074001935269432985124864 }, { target := 670, numerator := 30709401664148713148252160 }, { target := 671, numerator := 34036253511098157072646144 }, { target := 672, numerator := 34036253511098157072646144 }, { target := 673, numerator := 5118233610691452191375360 }, { target := 674, numerator := 30709401664148713148252160 }, { target := 675, numerator := 5118233610691452191375360 }, { target := 676, numerator := 34803988552701874901352448 }, { target := 677, numerator := 34803988552701874901352448 }, { target := 678, numerator := 4606410249622306972237824 }, { target := 679, numerator := 218687770330063799926652928 }, { target := 681, numerator := 8783547221541325201641308160 }, { target := 684, numerator := 8785254604676137237629370368 }, { target := 691, numerator := 216995411308317363249610752 }, { target := 695, numerator := 7110654670240474787888496640 }, { target := 698, numerator := 24644041587112222615322755072 }, { target := 700, numerator := 7112297177456527781463588864 }, { target := 966, numerator := 4451135332228386244263936 }, { target := 968, numerator := 178778892487177608804433920 }, { target := 971, numerator := 178813644285988957077897216 }, { target := 978, numerator := 4416689331772386101428224 }, { target := 982, numerator := 136712223634353271382999040 }, { target := 985, numerator := 473815967861880108814958592 }, { target := 987, numerator := 136743803119542148062511104 }]

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
    Slot12.Left5.expected,
    Slot12.Left12.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected,
    Slot13.Left11.expected,
    Slot13.Left18.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 138297570860224178752061440 }, { target := 15, numerator := 7109001934958136343312465920 }, { target := 20, numerator := 7110654670240474787888496640 }, { target := 28, numerator := 136712223634353271382999040 }, { target := 56, numerator := 4451823643255135134547968 }, { target := 57, numerator := 218687426174550425481510912 }, { target := 59, numerator := 2440707537256879767089577984 }, { target := 67, numerator := 218687770330063799926652928 }, { target := 74, numerator := 4451135332228386244263936 }, { target := 110, numerator := 13016603709425129934028800 }, { target := 112, numerator := 432892904592090471176601600 }, { target := 115, numerator := 432892904592090471176601600 }, { target := 122, numerator := 13016497396326426319257600 }, { target := 136, numerator := 479310449703037267829850112 }, { target := 137, numerator := 24638313552364465860447830016 }, { target := 142, numerator := 24644041587112222615322755072 }, { target := 150, numerator := 473815967861880108814958592 }, { target := 152, numerator := 178806538351404179741736960 }, { target := 153, numerator := 8783533398609211916172656640 }, { target := 155, numerator := 98030492857974269707529748480 }, { target := 163, numerator := 8783547221541325201641308160 }, { target := 170, numerator := 178778892487177608804433920 }, { target := 206, numerator := 442387731900096062139924480 }, { target := 208, numerator := 14712479114615170740372111360 }, { target := 211, numerator := 14712479114615170740372111360 }, { target := 218, numerator := 442384118698706769763368960 }, { target := 267, numerator := 138329516548579880645689344 }, { target := 268, numerator := 7110644060404893349620744192 }, { target := 273, numerator := 7112297177456527781463588864 }, { target := 281, numerator := 136743803119542148062511104 }, { target := 283, numerator := 611734200116226254551646208 }, { target := 284, numerator := 23497719893672234564852908032 }, { target := 286, numerator := 260047162141580272045039550464 }, { target := 294, numerator := 23497962945081401751086563328 }, { target := 301, numerator := 611649242430555984983228416 }, { target := 302, numerator := 4871086398158002872783994880 }, { target := 304, numerator := 161997613700937472417107804160 }, { target := 307, numerator := 161997613700937472417107804160 }, { target := 314, numerator := 4871046613564371414821109760 }, { target := 660, numerator := 17433869712493102038515712 }, { target := 661, numerator := 659379188514826988204064768 }, { target := 663, numerator := 7292866247698515993680674816 }, { target := 671, numerator := 659386422512926344517517312 }, { target := 678, numerator := 17431463601623259544551424 }, { target := 679, numerator := 442394624462293268986593280 }, { target := 681, numerator := 14712708340405264513457192960 }, { target := 684, numerator := 14712708340405264513457192960 }, { target := 691, numerator := 442391011204608981267906560 }, { target := 966, numerator := 13014880568875828222361600 }, { target := 968, numerator := 432835598144567027905331200 }, { target := 971, numerator := 432835598144567027905331200 }, { target := 978, numerator := 13014774269850873443123200 }]

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
    Slot18.Left0.expected,
    Slot18.Left1.expected,
    Slot18.Left2.expected,
    Slot18.Left3.expected,
    Slot18.Left4.expected,
    Slot18.Left5.expected,
    Slot18.Left6.expected,
    Slot18.Left7.expected,
    Slot18.Left8.expected,
    Slot18.Left9.expected,
    Slot18.Left10.expected,
    Slot18.Left11.expected,
    Slot18.Left12.expected,
    Slot18.Left13.expected,
    Slot18.Left14.expected,
    Slot18.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 4606597022906053281447936 }, { target := 112, numerator := 169478721001600547876241408 }, { target := 115, numerator := 169478907774884294185451520 }, { target := 122, numerator := 4606410249622306972237824 }, { target := 206, numerator := 34293555614967285539667968 }, { target := 208, numerator := 1261674923011915189745352704 }, { target := 211, numerator := 1261676313435249745602805760 }, { target := 218, numerator := 34292165191632729682214912 }, { target := 241, numerator := 34805399728623513682051072 }, { target := 243, numerator := 1280505892012093028398268416 }, { target := 246, numerator := 1280507303188014667178967040 }, { target := 253, numerator := 34803988552701874901352448 }, { target := 302, numerator := 5118441136562281423831040 }, { target := 304, numerator := 188309690001778386529157120 }, { target := 307, numerator := 188309897527649215761612800 }, { target := 314, numerator := 5118233610691452191375360 }, { target := 337, numerator := 30710646819373688542986240 }, { target := 339, numerator := 1129858140010670319174942720 }, { target := 342, numerator := 1129859385165895294569676800 }, { target := 349, numerator := 30709401664148713148252160 }, { target := 363, numerator := 5118441136562281423831040 }, { target := 365, numerator := 188309690001778386529157120 }, { target := 368, numerator := 188309897527649215761612800 }, { target := 375, numerator := 5118233610691452191375360 }, { target := 473, numerator := 34037633558139171468476416 }, { target := 475, numerator := 1252259438511826270418894848 }, { target := 478, numerator := 1252260818558867284814725120 }, { target := 485, numerator := 34036253511098157072646144 }, { target := 508, numerator := 34805399728623513682051072 }, { target := 510, numerator := 1280505892012093028398268416 }, { target := 513, numerator := 1280507303188014667178967040 }, { target := 520, numerator := 34803988552701874901352448 }, { target := 569, numerator := 30710646819373688542986240 }, { target := 571, numerator := 1129858140010670319174942720 }, { target := 574, numerator := 1129859385165895294569676800 }, { target := 581, numerator := 30709401664148713148252160 }, { target := 604, numerator := 620099143694520394497130496 }, { target := 606, numerator := 22813718943715451528007385088 }, { target := 609, numerator := 22813744085474702489519390720 }, { target := 616, numerator := 620074001935269432985124864 }, { target := 630, numerator := 30710646819373688542986240 }, { target := 632, numerator := 1129858140010670319174942720 }, { target := 635, numerator := 1129859385165895294569676800 }, { target := 642, numerator := 30709401664148713148252160 }, { target := 679, numerator := 34037633558139171468476416 }, { target := 681, numerator := 1252259438511826270418894848 }, { target := 684, numerator := 1252260818558867284814725120 }, { target := 691, numerator := 34036253511098157072646144 }, { target := 705, numerator := 34037633558139171468476416 }, { target := 707, numerator := 1252259438511826270418894848 }, { target := 710, numerator := 1252260818558867284814725120 }, { target := 717, numerator := 34036253511098157072646144 }, { target := 785, numerator := 5118441136562281423831040 }, { target := 787, numerator := 188309690001778386529157120 }, { target := 790, numerator := 188309897527649215761612800 }, { target := 797, numerator := 5118233610691452191375360 }, { target := 820, numerator := 30710646819373688542986240 }, { target := 822, numerator := 1129858140010670319174942720 }, { target := 825, numerator := 1129859385165895294569676800 }, { target := 832, numerator := 30709401664148713148252160 }, { target := 846, numerator := 5118441136562281423831040 }, { target := 848, numerator := 188309690001778386529157120 }, { target := 851, numerator := 188309897527649215761612800 }, { target := 858, numerator := 5118233610691452191375360 }]

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
    Slot18.Left16.expected,
    Slot18.Left17.expected,
    Slot18.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 895, numerator := 34805399728623513682051072 }, { target := 897, numerator := 1280505892012093028398268416 }, { target := 900, numerator := 1280507303188014667178967040 }, { target := 907, numerator := 34803988552701874901352448 }, { target := 921, numerator := 34805399728623513682051072 }, { target := 923, numerator := 1280505892012093028398268416 }, { target := 926, numerator := 1280507303188014667178967040 }, { target := 933, numerator := 34803988552701874901352448 }, { target := 966, numerator := 4606597022906053281447936 }, { target := 968, numerator := 169478721001600547876241408 }, { target := 971, numerator := 169478907774884294185451520 }, { target := 978, numerator := 4606410249622306972237824 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk7.Parent3
