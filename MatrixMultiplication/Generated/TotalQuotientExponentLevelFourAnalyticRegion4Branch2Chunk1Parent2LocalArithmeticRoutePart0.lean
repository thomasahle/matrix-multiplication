import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk1Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 31; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk1.Parent2

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
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot13.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 8596526942838671445852160 }, { target := 30, numerator := 388337092249947364531372032 }, { target := 35, numerator := 388271325435865435127939072 }, { target := 43, numerator := 8596526942838671445852160 }, { target := 71, numerator := 1163987693034751439929344 }, { target := 72, numerator := 38826071379208874647093248 }, { target := 74, numerator := 475505679532094638339915776 }, { target := 82, numerator := 38826104495021359632482304 }, { target := 89, numerator := 1269295976737004977127424 }, { target := 104, numerator := 420406498205134618078740480 }, { target := 105, numerator := 18991325003868895140586192896 }, { target := 110, numerator := 18988108728716134189960790016 }, { target := 118, numerator := 420406498205134618078740480 }, { target := 146, numerator := 36077712026395322137706496 }, { target := 147, numerator := 1203411196456307340745900032 }, { target := 149, numerator := 14738263192755384949181251584 }, { target := 157, numerator := 1203412222878453814196699136 }, { target := 164, numerator := 39341734452180895678857216 }, { target := 200, numerator := 20024898687872828346204160 }, { target := 202, numerator := 818277240277500434327797760 }, { target := 205, numerator := 818277832831584531183042560 }, { target := 212, numerator := 20025412448666694587514880 }, { target := 226, numerator := 420406651628700173756006400 }, { target := 227, numerator := 18991331934581929215818465280 }, { target := 232, numerator := 18988115658255417612309626880 }, { target := 240, numerator := 420406651628700173756006400 }, { target := 242, numerator := 423475563550609162773725184 }, { target := 243, numerator := 14125486511716730277910806528 }, { target := 245, numerator := 172995845932330903857461723136 }, { target := 253, numerator := 14125498559728439020952223744 }, { target := 260, numerator := 461788240784412034480472064 }, { target := 296, numerator := 541618652195938027280793600 }, { target := 298, numerator := 18856073277723816565097365504 }, { target := 301, numerator := 18856094089199405265886117888 }, { target := 308, numerator := 541616339809761504970932224 }, { target := 624, numerator := 8597089495912375595827200 }, { target := 625, numerator := 388362504864405640383037440 }, { target := 630, numerator := 388296733746571317073674240 }, { target := 638, numerator := 8597089495912375595827200 }, { target := 640, numerator := 36077979152622145014595584 }, { target := 641, numerator := 1203420106741194325468643328 }, { target := 643, numerator := 14738372317653153489654644736 }, { target := 651, numerator := 1203421133170940623290630144 }, { target := 658, numerator := 39342025745849218932670464 }, { target := 659, numerator := 541474202904101690277888000 }, { target := 661, numerator := 18851044377000515901660856320 }, { target := 664, numerator := 18851065182925699536692183040 }, { target := 671, numerator := 541471891134636841941073920 }, { target := 1017, numerator := 1164136096494097482645504 }, { target := 1018, numerator := 38831021537479421715283968 }, { target := 1020, numerator := 475566304475299383047356416 }, { target := 1028, numerator := 38831054657514031351332864 }, { target := 1035, numerator := 1269457806552740118134784 }, { target := 1036, numerator := 11575062605068775718912000 }, { target := 1038, numerator := 402977681419396385005895680 }, { target := 1041, numerator := 402978126186451334814760960 }, { target := 1048, numerator := 11575013186507114629038080 }]

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
    Slot13.Left1.expected,
    Slot13.Left6.expected,
    Slot13.Left14.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left3.expected,
    Slot14.Left11.expected,
    Slot14.Left18.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 11428371745034156900352000 }, { target := 30, numerator := 541618652195938027280793600 }, { target := 35, numerator := 541474202904101690277888000 }, { target := 43, numerator := 11575062605068775718912000 }, { target := 71, numerator := 1163987693034751439929344 }, { target := 72, numerator := 36077712026395322137706496 }, { target := 74, numerator := 423475563550609162773725184 }, { target := 82, numerator := 36077979152622145014595584 }, { target := 89, numerator := 1164136096494097482645504 }, { target := 104, numerator := 397870742072365816249057280 }, { target := 105, numerator := 18856073277723816565097365504 }, { target := 110, numerator := 18851044377000515901660856320 }, { target := 118, numerator := 402977681419396385005895680 }, { target := 146, numerator := 38826071379208874647093248 }, { target := 147, numerator := 1203411196456307340745900032 }, { target := 149, numerator := 14125486511716730277910806528 }, { target := 157, numerator := 1203420106741194325468643328 }, { target := 164, numerator := 38831021537479421715283968 }, { target := 226, numerator := 397871181202884357427036160 }, { target := 227, numerator := 18856094089199405265886117888 }, { target := 232, numerator := 18851065182925699536692183040 }, { target := 240, numerator := 402978126186451334814760960 }, { target := 242, numerator := 475505679532094638339915776 }, { target := 243, numerator := 14738263192755384949181251584 }, { target := 245, numerator := 172995845932330903857461723136 }, { target := 253, numerator := 14738372317653153489654644736 }, { target := 260, numerator := 475566304475299383047356416 }, { target := 296, numerator := 388337092249947364531372032 }, { target := 298, numerator := 18991325003868895140586192896 }, { target := 301, numerator := 18991331934581929215818465280 }, { target := 308, numerator := 388362504864405640383037440 }, { target := 624, numerator := 11428322952754318991687680 }, { target := 625, numerator := 541616339809761504970932224 }, { target := 630, numerator := 541471891134636841941073920 }, { target := 638, numerator := 11575013186507114629038080 }, { target := 640, numerator := 38826104495021359632482304 }, { target := 641, numerator := 1203412222878453814196699136 }, { target := 643, numerator := 14125498559728439020952223744 }, { target := 651, numerator := 1203421133170940623290630144 }, { target := 658, numerator := 38831054657514031351332864 }, { target := 659, numerator := 388271325435865435127939072 }, { target := 661, numerator := 18988108728716134189960790016 }, { target := 664, numerator := 18988115658255417612309626880 }, { target := 671, numerator := 388296733746571317073674240 }, { target := 1017, numerator := 1269295976737004977127424 }, { target := 1018, numerator := 39341734452180895678857216 }, { target := 1020, numerator := 461788240784412034480472064 }, { target := 1028, numerator := 39342025745849218932670464 }, { target := 1035, numerator := 1269457806552740118134784 }, { target := 1036, numerator := 8596526942838671445852160 }, { target := 1038, numerator := 420406498205134618078740480 }, { target := 1041, numerator := 420406651628700173756006400 }, { target := 1048, numerator := 8597089495912375595827200 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk1.Parent2
