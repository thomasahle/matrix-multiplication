import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch2Chunk4Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 2,
parent 52; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk4.Parent0

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
    Slot9.Left6.expected,
    Slot9.Left14.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left3.expected,
    Slot13.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 2002231283214940800811008 }, { target := 72, numerator := 53574414274854386839584768 }, { target := 74, numerator := 686314440425504127160680448 }, { target := 82, numerator := 53473020565547189964636160 }, { target := 89, numerator := 1979139884521731695575040 }, { target := 146, numerator := 53574414274854386839584768 }, { target := 147, numerator := 1433063459602789687225221120 }, { target := 149, numerator := 18381424917879816902699646976 }, { target := 157, numerator := 1430302417398197543577321472 }, { target := 164, numerator := 52945927706594298665369600 }, { target := 200, numerator := 10277663035971997400039424 }, { target := 202, numerator := 375922774213237194589470720 }, { target := 205, numerator := 375923096467745581131890688 }, { target := 212, numerator := 10238394022307180159434752 }, { target := 242, numerator := 686314440425504127160680448 }, { target := 243, numerator := 18381424917879816902699646976 }, { target := 245, numerator := 234567640809468121043236290560 }, { target := 253, numerator := 18348549172002813263434743808 }, { target := 260, numerator := 678815065444350145362657280 }, { target := 296, numerator := 516905860795972756137050112 }, { target := 298, numerator := 18906699365156431158690447360 }, { target := 301, numerator := 18906715572658415793963270144 }, { target := 308, numerator := 514930860911273629320216576 }, { target := 640, numerator := 53473020565547189964636160 }, { target := 641, numerator := 1430302417398197543577321472 }, { target := 643, numerator := 18348549172002813263434743808 }, { target := 651, numerator := 1427541342927565869633503232 }, { target := 658, numerator := 52844560337152472420188160 }, { target := 659, numerator := 516697170583917636706369536 }, { target := 661, numerator := 18899066170412419023718318080 }, { target := 664, numerator := 18899082371370954875398520832 }, { target := 671, numerator := 514722968065191710533091328 }, { target := 1017, numerator := 978319604177472994672640 }, { target := 1018, numerator := 26639076873752896392396800 }, { target := 1020, numerator := 317265608429373853301473280 }, { target := 1028, numerator := 26639232292976036948213760 }, { target := 1035, numerator := 978030968477354819584000 }, { target := 1036, numerator := 10392345251268773359386624 }, { target := 1038, numerator := 380117468705204116096286720 }, { target := 1041, numerator := 380117794555555330117337088 }, { target := 1048, numerator := 10352638058470836222820352 }]

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
    Slot13.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 10277663035971997400039424 }, { target := 30, numerator := 516905860795972756137050112 }, { target := 35, numerator := 516697170583917636706369536 }, { target := 43, numerator := 10392345251268773359386624 }, { target := 104, numerator := 375922774213237194589470720 }, { target := 105, numerator := 18906699365156431158690447360 }, { target := 110, numerator := 18899066170412419023718318080 }, { target := 118, numerator := 380117468705204116096286720 }, { target := 226, numerator := 375923096467745581131890688 }, { target := 227, numerator := 18906715572658415793963270144 }, { target := 232, numerator := 18899082371370954875398520832 }, { target := 240, numerator := 380117794555555330117337088 }, { target := 624, numerator := 10238394022307180159434752 }, { target := 625, numerator := 514930860911273629320216576 }, { target := 630, numerator := 514722968065191710533091328 }, { target := 638, numerator := 10352638058470836222820352 }, { target := 1017, numerator := 1000820280344258700902400 }, { target := 1018, numerator := 26306850832841402272972800 }, { target := 1020, numerator := 361549457014976292061184000 }, { target := 1028, numerator := 26205328044176435471974400 }, { target := 1035, numerator := 978030968477354819584000 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk4.Parent0
