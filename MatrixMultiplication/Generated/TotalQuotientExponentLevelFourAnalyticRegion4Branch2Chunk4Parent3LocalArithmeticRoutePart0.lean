import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk4Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 52; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk4.Parent3

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
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left6.expected,
    Slot9.Left14.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot13.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 2017871517420012020170752 }, { target := 72, numerator := 68913887857313101696204800 }, { target := 74, numerator := 837585901455105019997061120 }, { target := 82, numerator := 68914747621222089511403520 }, { target := 89, numerator := 2109181624658804871266304 }, { target := 146, numerator := 33654146018141297801428992 }, { target := 147, numerator := 1176126914100706010292289536 }, { target := 149, numerator := 14190384076675256451304783872 }, { target := 157, numerator := 1176154634987021073874157568 }, { target := 164, numerator := 33655136049795407215067136 }, { target := 200, numerator := 20392197173756040356823040 }, { target := 202, numerator := 817911329115630809613598720 }, { target := 205, numerator := 817910694815992916800962560 }, { target := 212, numerator := 20391163140244721673175040 }, { target := 242, numerator := 412164738871777368005935104 }, { target := 243, numerator := 14404110630799473070709932032 }, { target := 245, numerator := 173790651062733747920950001664 }, { target := 253, numerator := 14404450130481419641071599616 }, { target := 260, numerator := 412176863860418316947423232 }, { target := 296, numerator := 940480911364944551101857792 }, { target := 298, numerator := 37836937842150108695978049536 }, { target := 301, numerator := 37836907781129813905949851648 }, { target := 308, numerator := 940432359849231571524517888 }, { target := 640, numerator := 33654174722677947777417216 }, { target := 641, numerator := 1176127917251345834236182528 }, { target := 643, numerator := 14190396180039863789426835456 }, { target := 651, numerator := 1176155638161304795861745664 }, { target := 658, numerator := 33655164755176482121187328 }, { target := 659, numerator := 940281527914421411769221120 }, { target := 661, numerator := 37828681818379878190704230400 }, { target := 664, numerator := 37828651765376835162325647360 }, { target := 671, numerator := 940232988447807760244932608 }, { target := 1017, numerator := 1100216185256929652637696 }, { target := 1018, numerator := 38449760873811945474490368 }, { target := 1020, numerator := 463909862034662880115163136 }, { target := 1028, numerator := 38450667120780062264131584 }, { target := 1035, numerator := 1100248551220076680839168 }, { target := 1036, numerator := 20503789321574114645770240 }, { target := 1038, numerator := 823053379074232563343032320 }, { target := 1041, numerator := 823052736632930969174671360 }, { target := 1048, numerator := 20502744641271801881559040 }]

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
    Slot13.Left3.expected,
    Slot13.Left11.expected,
    Slot13.Left18.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
    Slot14.Left5.expected,
    Slot14.Left12.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 20392197173756040356823040 }, { target := 30, numerator := 940480911364944551101857792 }, { target := 35, numerator := 940281527914421411769221120 }, { target := 43, numerator := 20503789321574114645770240 }, { target := 104, numerator := 817911329115630809613598720 }, { target := 105, numerator := 37836937842150108695978049536 }, { target := 110, numerator := 37828681818379878190704230400 }, { target := 118, numerator := 823053379074232563343032320 }, { target := 146, numerator := 35259741839171803894775808 }, { target := 147, numerator := 1176126914100706010292289536 }, { target := 149, numerator := 14404110630799473070709932032 }, { target := 157, numerator := 1176127917251345834236182528 }, { target := 164, numerator := 38449760873811945474490368 }, { target := 226, numerator := 817910694815992916800962560 }, { target := 227, numerator := 37836907781129813905949851648 }, { target := 232, numerator := 37828651765376835162325647360 }, { target := 240, numerator := 823052736632930969174671360 }, { target := 242, numerator := 425421162583327651991126016 }, { target := 243, numerator := 14190384076675256451304783872 }, { target := 245, numerator := 173790651062733747920950001664 }, { target := 253, numerator := 14190396180039863789426835456 }, { target := 260, numerator := 463909862034662880115163136 }, { target := 624, numerator := 20391163140244721673175040 }, { target := 625, numerator := 940432359849231571524517888 }, { target := 630, numerator := 940232988447807760244932608 }, { target := 638, numerator := 20502744641271801881559040 }, { target := 640, numerator := 35260572898544141733986304 }, { target := 641, numerator := 1176154634987021073874157568 }, { target := 643, numerator := 14404450130481419641071599616 }, { target := 651, numerator := 1176155638161304795861745664 }, { target := 658, numerator := 38450667120780062264131584 }, { target := 1017, numerator := 1008965439401875218628608 }, { target := 1018, numerator := 33655136049795407215067136 }, { target := 1020, numerator := 412176863860418316947423232 }, { target := 1028, numerator := 33655164755176482121187328 }, { target := 1035, numerator := 1100248551220076680839168 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk4.Parent3
