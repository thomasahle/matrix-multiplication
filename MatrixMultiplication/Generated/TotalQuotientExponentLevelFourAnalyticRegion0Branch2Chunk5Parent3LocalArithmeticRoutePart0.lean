import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk5Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 62; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk5.Parent3

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
  [{ target := 56, numerator := 4583754189135277822312448 }, { target := 57, numerator := 39096726907330310837370880 }, { target := 58, numerator := 39905624705413006923661312 }, { target := 59, numerator := 4853386788496176517742592 }, { target := 60, numerator := 28581055532255261715595264 }, { target := 61, numerator := 4853386788496176517742592 }, { target := 62, numerator := 39096726907330310837370880 }, { target := 63, numerator := 39905624705413006923661312 }, { target := 64, numerator := 28581055532255261715595264 }, { target := 65, numerator := 645770075469352375555194880 }, { target := 66, numerator := 28581055532255261715595264 }, { target := 67, numerator := 39096726907330310837370880 }, { target := 68, numerator := 39096726907330310837370880 }, { target := 69, numerator := 4853386788496176517742592 }, { target := 70, numerator := 28581055532255261715595264 }, { target := 71, numerator := 4853386788496176517742592 }, { target := 72, numerator := 39905624705413006923661312 }, { target := 73, numerator := 39905624705413006923661312 }, { target := 74, numerator := 4314121589774379126882304 }, { target := 110, numerator := 3890521279121675985616896 }, { target := 112, numerator := 186607133128114923903123456 }, { target := 115, numerator := 186713417742676795462778880 }, { target := 122, numerator := 3968905614358627007594496 }, { target := 206, numerator := 102263478230721071532736512 }, { target := 208, numerator := 4905022521982567972268408832 }, { target := 211, numerator := 4907816243848539188609679360 }, { target := 218, numerator := 104323833176766538907123712 }, { target := 257, numerator := 139961946373309831317553152 }, { target := 260, numerator := 492584384575808121839026176 }, { target := 262, numerator := 139815596790144000124256256 }, { target := 302, numerator := 1405462982312678667960975360 }, { target := 304, numerator := 67412410582231643233147944960 }, { target := 307, numerator := 67450806231718954449816780800 }, { target := 314, numerator := 1433779568616916311720591360 }, { target := 353, numerator := 7039260784826202704131915776 }, { target := 356, numerator := 24774090611128138720176242688 }, { target := 358, numerator := 7031900263567751913802825728 }, { target := 679, numerator := 101868825387074694231883776 }, { target := 681, numerator := 4886093172815678245108187136 }, { target := 684, numerator := 4888876113215012123998945280 }, { target := 691, numerator := 103921229059093052969189376 }, { target := 695, numerator := 7036418826672285576150908928 }, { target := 698, numerator := 24764088576685836735677988864 }, { target := 700, numerator := 7029061277074360934527401984 }, { target := 966, numerator := 3801931644702765204111360 }, { target := 968, numerator := 182357970479269867904040960 }, { target := 971, numerator := 182461834925820085062860800 }, { target := 978, numerator := 3878531118964896285327360 }, { target := 982, numerator := 141523696939675010048458752 }, { target := 985, numerator := 498080835300650374687358976 }, { target := 987, numerator := 141375714330173671060013056 }]

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
  [{ target := 110, numerator := 8306699922118091665833984 }, { target := 112, numerator := 303831490519789253186027520 }, { target := 115, numerator := 303831750975059128020369408 }, { target := 122, numerator := 8274961587089058281029632 }, { target := 152, numerator := 159830118079123133304930304 }, { target := 153, numerator := 1363256889498403195836170240 }, { target := 154, numerator := 1391462204453542572301746176 }, { target := 155, numerator := 169231889730836258793455616 }, { target := 156, numerator := 996587795081591301783683072 }, { target := 157, numerator := 169231889730836258793455616 }, { target := 158, numerator := 1363256889498403195836170240 }, { target := 159, numerator := 1391462204453542572301746176 }, { target := 160, numerator := 996587795081591301783683072 }, { target := 161, numerator := 22517243105852935545018122240 }, { target := 162, numerator := 996587795081591301783683072 }, { target := 163, numerator := 1363256889498403195836170240 }, { target := 164, numerator := 1363256889498403195836170240 }, { target := 165, numerator := 169231889730836258793455616 }, { target := 166, numerator := 996587795081591301783683072 }, { target := 167, numerator := 169231889730836258793455616 }, { target := 168, numerator := 1391462204453542572301746176 }, { target := 169, numerator := 1391462204453542572301746176 }, { target := 170, numerator := 150428346427410007816404992 }, { target := 283, numerator := 159904812404642097099964416 }, { target := 284, numerator := 1363893988157241416440872960 }, { target := 285, numerator := 1392112484463942962987925504 }, { target := 286, numerator := 169310977840209279282315264 }, { target := 287, numerator := 997053536170121311329189888 }, { target := 288, numerator := 169310977840209279282315264 }, { target := 289, numerator := 1363893988157241416440872960 }, { target := 290, numerator := 1392112484463942962987925504 }, { target := 291, numerator := 997053536170121311329189888 }, { target := 292, numerator := 22527766218183401326730280960 }, { target := 293, numerator := 997053536170121311329189888 }, { target := 294, numerator := 1363893988157241416440872960 }, { target := 295, numerator := 1363893988157241416440872960 }, { target := 296, numerator := 169310977840209279282315264 }, { target := 297, numerator := 997053536170121311329189888 }, { target := 298, numerator := 169310977840209279282315264 }, { target := 299, numerator := 1392112484463942962987925504 }, { target := 300, numerator := 1392112484463942962987925504 }, { target := 301, numerator := 150498646969074914917613568 }, { target := 660, numerator := 4509138262278627292872704 }, { target := 661, numerator := 38460296942964762203914240 }, { target := 662, numerator := 39256027224543343490891776 }, { target := 663, numerator := 4774381689471487721865216 }, { target := 664, numerator := 28115803282443205473206272 }, { target := 665, numerator := 4774381689471487721865216 }, { target := 666, numerator := 38460296942964762203914240 }, { target := 667, numerator := 39256027224543343490891776 }, { target := 668, numerator := 28115803282443205473206272 }, { target := 669, numerator := 635258008126900727437066240 }, { target := 670, numerator := 28115803282443205473206272 }, { target := 671, numerator := 38460296942964762203914240 }, { target := 672, numerator := 38460296942964762203914240 }, { target := 673, numerator := 4774381689471487721865216 }, { target := 674, numerator := 28115803282443205473206272 }, { target := 675, numerator := 4774381689471487721865216 }, { target := 676, numerator := 39256027224543343490891776 }, { target := 677, numerator := 39256027224543343490891776 }, { target := 678, numerator := 4243894835085766863880192 }]

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
  [{ target := 56, numerator := 8306699922118091665833984 }, { target := 57, numerator := 226186633537355776083886080 }, { target := 59, numerator := 2693833583194706216661024768 }, { target := 67, numerator := 226187953168326314327801856 }, { target := 74, numerator := 8304249178887092069990400 }, { target := 110, numerator := 4583754189135277822312448 }, { target := 112, numerator := 159830118079123133304930304 }, { target := 115, numerator := 159904812404642097099964416 }, { target := 122, numerator := 4509138262278627292872704 }, { target := 152, numerator := 303831490519789253186027520 }, { target := 153, numerator := 8273155723408491111933542400 }, { target := 155, numerator := 98531484279934549587174359040 }, { target := 163, numerator := 8273203991125932923085127680 }, { target := 170, numerator := 303741850473111603904512000 }, { target := 206, numerator := 265283360444686086921256960 }, { target := 208, numerator := 9636412612906894307769712640 }, { target := 211, numerator := 9637056803612060479830097920 }, { target := 218, numerator := 263782713977785882331054080 }, { target := 241, numerator := 39905624705413006923661312 }, { target := 243, numerator := 1391462204453542572301746176 }, { target := 246, numerator := 1392112484463942962987925504 }, { target := 253, numerator := 39256027224543343490891776 }, { target := 283, numerator := 303831750975059128020369408 }, { target := 284, numerator := 8273162815454819063389224960 }, { target := 286, numerator := 98531568744662960044209340416 }, { target := 294, numerator := 8273211083213637696117276672 }, { target := 301, numerator := 303742110851538810096844800 }, { target := 302, numerator := 2698686969983202393178767360 }, { target := 304, numerator := 98700716169665385845967814656 }, { target := 307, numerator := 98700879722503169323491655680 }, { target := 314, numerator := 2688315334407874868548730880 }, { target := 337, numerator := 28581055532255261715595264 }, { target := 339, numerator := 996587795081591301783683072 }, { target := 342, numerator := 997053536170121311329189888 }, { target := 349, numerator := 28115803282443205473206272 }, { target := 363, numerator := 4853386788496176517742592 }, { target := 365, numerator := 169231889730836258793455616 }, { target := 368, numerator := 169310977840209279282315264 }, { target := 375, numerator := 4774381689471487721865216 }, { target := 473, numerator := 39096726907330310837370880 }, { target := 475, numerator := 1363256889498403195836170240 }, { target := 478, numerator := 1363893988157241416440872960 }, { target := 485, numerator := 38460296942964762203914240 }, { target := 660, numerator := 8274961587089058281029632 }, { target := 661, numerator := 225322417034821120127139840 }, { target := 663, numerator := 2683540952718403380826865664 }, { target := 671, numerator := 225323731623730400553074688 }, { target := 678, numerator := 8272520207686108918579200 }, { target := 679, numerator := 226187953168326314327801856 }, { target := 681, numerator := 8273203991125932923085127680 }, { target := 684, numerator := 8273211083213637696117276672 }, { target := 691, numerator := 225323731623730400553074688 }, { target := 966, numerator := 8304249178887092069990400 }, { target := 968, numerator := 303741850473111603904512000 }, { target := 971, numerator := 303742110851538810096844800 }, { target := 978, numerator := 8272520207686108918579200 }]

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
  [{ target := 56, numerator := 3890521279121675985616896 }, { target := 57, numerator := 102263478230721071532736512 }, { target := 59, numerator := 1405462982312678667960975360 }, { target := 67, numerator := 101868825387074694231883776 }, { target := 74, numerator := 3801931644702765204111360 }, { target := 152, numerator := 186607133128114923903123456 }, { target := 153, numerator := 4905022521982567972268408832 }, { target := 155, numerator := 67412410582231643233147944960 }, { target := 163, numerator := 4886093172815678245108187136 }, { target := 170, numerator := 182357970479269867904040960 }, { target := 283, numerator := 186713417742676795462778880 }, { target := 284, numerator := 4907816243848539188609679360 }, { target := 286, numerator := 67450806231718954449816780800 }, { target := 294, numerator := 4888876113215012123998945280 }, { target := 301, numerator := 182461834925820085062860800 }, { target := 508, numerator := 39905624705413006923661312 }, { target := 510, numerator := 1391462204453542572301746176 }, { target := 513, numerator := 1392112484463942962987925504 }, { target := 520, numerator := 39256027224543343490891776 }, { target := 569, numerator := 28581055532255261715595264 }, { target := 571, numerator := 996587795081591301783683072 }, { target := 574, numerator := 997053536170121311329189888 }, { target := 581, numerator := 28115803282443205473206272 }, { target := 604, numerator := 645770075469352375555194880 }, { target := 606, numerator := 22517243105852935545018122240 }, { target := 609, numerator := 22527766218183401326730280960 }, { target := 616, numerator := 635258008126900727437066240 }, { target := 630, numerator := 28581055532255261715595264 }, { target := 632, numerator := 996587795081591301783683072 }, { target := 635, numerator := 997053536170121311329189888 }, { target := 642, numerator := 28115803282443205473206272 }, { target := 679, numerator := 39096726907330310837370880 }, { target := 681, numerator := 1363256889498403195836170240 }, { target := 684, numerator := 1363893988157241416440872960 }, { target := 691, numerator := 38460296942964762203914240 }, { target := 705, numerator := 39096726907330310837370880 }, { target := 707, numerator := 1363256889498403195836170240 }, { target := 710, numerator := 1363893988157241416440872960 }, { target := 717, numerator := 38460296942964762203914240 }, { target := 785, numerator := 4853386788496176517742592 }, { target := 787, numerator := 169231889730836258793455616 }, { target := 790, numerator := 169310977840209279282315264 }, { target := 797, numerator := 4774381689471487721865216 }, { target := 820, numerator := 28581055532255261715595264 }, { target := 822, numerator := 996587795081591301783683072 }, { target := 825, numerator := 997053536170121311329189888 }, { target := 832, numerator := 28115803282443205473206272 }, { target := 846, numerator := 4853386788496176517742592 }, { target := 848, numerator := 169231889730836258793455616 }, { target := 851, numerator := 169310977840209279282315264 }, { target := 858, numerator := 4774381689471487721865216 }, { target := 895, numerator := 39905624705413006923661312 }, { target := 897, numerator := 1391462204453542572301746176 }, { target := 900, numerator := 1392112484463942962987925504 }, { target := 907, numerator := 39256027224543343490891776 }, { target := 921, numerator := 39905624705413006923661312 }, { target := 923, numerator := 1391462204453542572301746176 }, { target := 926, numerator := 1392112484463942962987925504 }, { target := 933, numerator := 39256027224543343490891776 }, { target := 966, numerator := 4314121589774379126882304 }, { target := 968, numerator := 150428346427410007816404992 }, { target := 971, numerator := 150498646969074914917613568 }, { target := 978, numerator := 4243894835085766863880192 }]

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
  [{ target := 14, numerator := 139961946373309831317553152 }, { target := 15, numerator := 7039260784826202704131915776 }, { target := 20, numerator := 7036418826672285576150908928 }, { target := 28, numerator := 141523696939675010048458752 }, { target := 136, numerator := 492584384575808121839026176 }, { target := 137, numerator := 24774090611128138720176242688 }, { target := 142, numerator := 24764088576685836735677988864 }, { target := 150, numerator := 498080835300650374687358976 }, { target := 267, numerator := 139815596790144000124256256 }, { target := 268, numerator := 7031900263567751913802825728 }, { target := 273, numerator := 7029061277074360934527401984 }, { target := 281, numerator := 141375714330173671060013056 }, { target := 660, numerator := 3968905614358627007594496 }, { target := 661, numerator := 104323833176766538907123712 }, { target := 663, numerator := 1433779568616916311720591360 }, { target := 671, numerator := 103921229059093052969189376 }, { target := 678, numerator := 3878531118964896285327360 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk5.Parent3
