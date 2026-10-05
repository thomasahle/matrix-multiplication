import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk3Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 43; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk3.Parent1

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
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot13.Left0.expected,
    Slot13.Left3.expected,
    Slot13.Left5.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 61085902203712763850653696 }, { target := 17, numerator := 3000729543435476708217585664 }, { target := 19, numerator := 33490280360639577397131214848 }, { target := 27, numerator := 3000734265781130429586210816 }, { target := 34, numerator := 61076457512405321113403392 }, { target := 35, numerator := 2020354806433884565864972288 }, { target := 37, numerator := 73570339688933658758526009344 }, { target := 40, numerator := 73570412889970812927554355200 }, { target := 47, numerator := 2020279850068110133377892352 }, { target := 86, numerator := 2819429426747359775170756608 }, { target := 89, numerator := 9283676381515146807943888896 }, { target := 91, numerator := 2815855775183553881381535744 }, { target := 122, numerator := 181183618013182976631767040 }, { target := 124, numerator := 181182451683336379195981824 }, { target := 126, numerator := 61086441074607827472875520 }, { target := 127, numerator := 3000756014450172086640967680 }, { target := 129, numerator := 33490575796029787163338997760 }, { target := 137, numerator := 3000760736837484104562769920 }, { target := 144, numerator := 61076996299983791629271040 }, { target := 145, numerator := 6553712954008208338816335872 }, { target := 147, numerator := 238546189224166787423225774080 }, { target := 150, numerator := 238546425478736641582465810432 }, { target := 157, numerator := 6553470764084169622983540736 }, { target := 161, numerator := 102027764378815972738989031424 }, { target := 164, numerator := 335754315099671918657654489088 }, { target := 166, numerator := 101896285432575726079476498432 }, { target := 197, numerator := 6136177755394107502325923840 }, { target := 199, numerator := 6136138255094143171799547904 }, { target := 216, numerator := 2016622990229242848137445376 }, { target := 218, numerator := 73433597629916388902794428416 }, { target := 221, numerator := 73433670685994493015788355584 }, { target := 228, numerator := 2016548180100977815904583680 }, { target := 232, numerator := 35602992219781346432563281920 }, { target := 235, numerator := 121369631321099807844382801920 }, { target := 237, numerator := 35603049611804299670291742720 }, { target := 242, numerator := 66593746721438339298733588480 }, { target := 244, numerator := 66593318038783418960642572288 }, { target := 406, numerator := 1015819976456271904720814080 }, { target := 409, numerator := 3462902647901743803877294080 }, { target := 411, numerator := 1015821613958059542215393280 }, { target := 416, numerator := 6136168310630742465550745600 }, { target := 418, numerator := 6136128810391576729993871360 }, { target := 498, numerator := 181141116578040311143464960 }, { target := 500, numerator := 181139950521787391070437376 }]

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
    Slot14.Left5.expected,
    Slot14.Left12.expected,
    Slot15.Left0.expected,
    Slot15.Left1.expected,
    Slot15.Left3.expected,
    Slot15.Left11.expected,
    Slot15.Left18.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot19.Left0.expected,
    Slot19.Left3.expected,
    Slot19.Left5.expected,
    Slot20.Left0.expected,
    Slot20.Left2.expected,
    Slot20.Left5.expected,
    Slot20.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 16, numerator := 181183618013182976631767040 }, { target := 17, numerator := 6136177755394107502325923840 }, { target := 19, numerator := 66593746721438339298733588480 }, { target := 27, numerator := 6136168310630742465550745600 }, { target := 34, numerator := 181141116578040311143464960 }, { target := 35, numerator := 1013990912928362174600970240 }, { target := 37, numerator := 35604891128217243169083883520 }, { target := 40, numerator := 35602992219781346432563281920 }, { target := 47, numerator := 1015819976456271904720814080 }, { target := 86, numerator := 214916292614886965295185920 }, { target := 89, numerator := 726703992617463269310857216 }, { target := 91, numerator := 214759762527388397807337472 }, { target := 122, numerator := 61085902203712763850653696 }, { target := 124, numerator := 61086441074607827472875520 }, { target := 126, numerator := 181182451683336379195981824 }, { target := 127, numerator := 6136138255094143171799547904 }, { target := 129, numerator := 66593318038783418960642572288 }, { target := 137, numerator := 6136128810391576729993871360 }, { target := 144, numerator := 181139950521787391070437376 }, { target := 145, numerator := 3456667420124401738438410240 }, { target := 147, numerator := 121376104648267215477953003520 }, { target := 150, numerator := 121369631321099807844382801920 }, { target := 157, numerator := 3462902647901743803877294080 }, { target := 161, numerator := 7147466438334929188620861440 }, { target := 164, numerator := 24167978772762084243524288512 }, { target := 166, numerator := 7142260720641899601858658304 }, { target := 197, numerator := 3000729543435476708217585664 }, { target := 199, numerator := 3000756014450172086640967680 }, { target := 216, numerator := 1013992547481699431051427840 }, { target := 218, numerator := 35604948523301236778540728320 }, { target := 221, numerator := 35603049611804299670291742720 }, { target := 228, numerator := 1015821613958059542215393280 }, { target := 232, numerator := 73570412889970812927554355200 }, { target := 235, numerator := 238546425478736641582465810432 }, { target := 237, numerator := 73433670685994493015788355584 }, { target := 242, numerator := 33490280360639577397131214848 }, { target := 244, numerator := 33490575796029787163338997760 }, { target := 406, numerator := 2020279850068110133377892352 }, { target := 409, numerator := 6553470764084169622983540736 }, { target := 411, numerator := 2016548180100977815904583680 }, { target := 416, numerator := 3000734265781130429586210816 }, { target := 418, numerator := 3000760736837484104562769920 }, { target := 498, numerator := 61076457512405321113403392 }, { target := 500, numerator := 61076996299983791629271040 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk3.Parent1
