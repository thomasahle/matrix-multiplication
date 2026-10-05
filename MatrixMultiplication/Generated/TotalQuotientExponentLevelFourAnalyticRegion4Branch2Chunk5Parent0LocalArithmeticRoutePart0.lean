import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk5Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 53; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk5.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left6.expected,
    Slot6.Left14.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left6.expected,
    Slot10.Left14.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left3.expected,
    Slot11.Left11.expected,
    Slot11.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 110, numerator := 24301690718332769059995648 }, { target := 112, numerator := 907834932661375390663573504 }, { target := 115, numerator := 907834645657667187456868352 }, { target := 122, numerator := 24300959237488842056400896 }, { target := 206, numerator := 801321006093061741495713792 }, { target := 208, numerator := 29853826246254282117539168256 }, { target := 211, numerator := 29853817350595679347632242688 }, { target := 218, numerator := 801297492928885729422999552 }, { target := 257, numerator := 301734242064485743455109120 }, { target := 260, numerator := 1073170994175716296438579200 }, { target := 262, numerator := 301700148005422448550871040 }, { target := 302, numerator := 9751750794879765265973772288 }, { target := 304, numerator := 362761137511326453785809649664 }, { target := 307, numerator := 362761033095224978012784033792 }, { target := 314, numerator := 9751468750883374790873186304 }, { target := 353, numerator := 13959162407556862937189580800 }, { target := 356, numerator := 49638050448060254430930403328 }, { target := 358, numerator := 13957546038876981356434292736 }, { target := 679, numerator := 801322488334941075252707328 }, { target := 681, numerator := 29853888516040986317285228544 }, { target := 684, numerator := 29853879620316518402828009472 }, { target := 691, numerator := 801298975074500621144948736 }, { target := 695, numerator := 13956114885104489150527045632 }, { target := 698, numerator := 49627234266381078415858991104 }, { target := 700, numerator := 13954498948633374958657994752 }, { target := 966, numerator := 26144919391410344813395968 }, { target := 968, numerator := 973592396344425699568779264 }, { target := 971, numerator := 973592109304125749389688832 }, { target := 978, numerator := 26144155639460337933090816 }, { target := 982, numerator := 303635835968692783331409920 }, { target := 985, numerator := 1079875512694090696858009600 }, { target := 987, numerator := 303601301007225968855613440 }]

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
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left3.expected,
    Slot15.Left11.expected,
    Slot15.Left18.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot16.Left5.expected,
    Slot16.Left12.expected,
    Slot17.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 153585120570207394081013760 }, { target := 15, numerator := 6938011074900113491966820352 }, { target := 20, numerator := 6936836088287792570189217792 }, { target := 28, numerator := 153585120570207394081013760 }, { target := 56, numerator := 31573463079600701067755520 }, { target := 57, numerator := 1070999303179045565198499840 }, { target := 59, numerator := 13045442538611216257992622080 }, { target := 67, numerator := 1071009112639686301785784320 }, { target := 74, numerator := 33416519857317374507089920 }, { target := 110, numerator := 11205533494734376402944000 }, { target := 112, numerator := 390112784772157581463388160 }, { target := 115, numerator := 390113215340207331103211520 }, { target := 122, numerator := 11205485653839959776296960 }, { target := 152, numerator := 1116684101050175690322739200 }, { target := 153, numerator := 37869024781806751179562024960 }, { target := 155, numerator := 461307181615732550569526558720 }, { target := 163, numerator := 37869366788496524794165985280 }, { target := 170, numerator := 1182429930664528981388165120 }, { target := 206, numerator := 391604931021272097226752000 }, { target := 208, numerator := 13633450852028219630320353280 }, { target := 211, numerator := 13633465899287816989478748160 }, { target := 218, numerator := 391603259103539057320263680 }, { target := 283, numerator := 1116684531618225439962562560 }, { target := 284, numerator := 37869039829066348538720419840 }, { target := 286, numerator := 461307363166201660641357332480 }, { target := 294, numerator := 37869381836110780623979806720 }, { target := 301, numerator := 1182430361245245104979968000 }, { target := 302, numerator := 4724850958589619395887104000 }, { target := 304, numerator := 164492370305702047261455810560 }, { target := 307, numerator := 164492551856171157333286584320 }, { target := 314, numerator := 4724830786315273832350351360 }, { target := 660, numerator := 31573059070403853938589696 }, { target := 661, numerator := 1070985750881463212328353792 }, { target := 663, numerator := 13045276866473179307158011904 }, { target := 671, numerator := 1070995560292564353014562816 }, { target := 678, numerator := 33416083623457818658471936 }, { target := 679, numerator := 391614161007970904702976000 }, { target := 681, numerator := 13633772187537695711051120640 }, { target := 684, numerator := 13633787235151951540864942080 }, { target := 691, numerator := 391612489050831368056995840 }, { target := 966, numerator := 11205863137116476669952000 }, { target := 968, numerator := 390124261040353155775201280 }, { target := 971, numerator := 390124691621069279367004160 }, { target := 978, numerator := 11205815294814685159751680 }]

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
    Slot17.Left3.expected,
    Slot17.Left5.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot20.Left5.expected,
    Slot20.Left12.expected,
    Slot21.Left0.expected,
    Slot21.Left3.expected,
    Slot21.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 148149121494278349374095360 }, { target := 15, numerator := 7021151332656749445222760448 }, { target := 20, numerator := 7019278796816696580337827840 }, { target := 28, numerator := 150050715398485389250396160 }, { target := 56, numerator := 3933761133466444395184128 }, { target := 57, numerator := 121926633935288273523965952 }, { target := 59, numerator := 1431159214858168403868254208 }, { target := 67, numerator := 121927536703225678169899008 }, { target := 74, numerator := 3934262671209446976258048 }, { target := 136, numerator := 1073170994175716296438579200 }, { target := 137, numerator := 49638050448060254430930403328 }, { target := 142, numerator := 49627234266381078415858991104 }, { target := 150, numerator := 1079875512694090696858009600 }, { target := 152, numerator := 181263616383357281804222464 }, { target := 153, numerator := 5618252316475750568297496576 }, { target := 155, numerator := 65946326201295950477738901504 }, { target := 163, numerator := 5618293915082157234170363904 }, { target := 170, numerator := 181286726720249873955815424 }, { target := 267, numerator := 301700148005422448550871040 }, { target := 268, numerator := 13957546038876981356434292736 }, { target := 273, numerator := 13954498948633374958657994752 }, { target := 281, numerator := 303601301007225968855613440 }, { target := 283, numerator := 181263329379649078597517312 }, { target := 284, numerator := 5618243420817147798390571008 }, { target := 286, numerator := 65946221785194474704713285632 }, { target := 294, numerator := 5618285019357689319713144832 }, { target := 301, numerator := 181286439679949923776724992 }, { target := 660, numerator := 3933385820924947894108160 }, { target := 661, numerator := 121915001150961574414909440 }, { target := 663, numerator := 1431022670725469316065525760 }, { target := 671, numerator := 121915903832767636187381760 }, { target := 678, numerator := 3933887310817204434370560 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk5.Parent0
