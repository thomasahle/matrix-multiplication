import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk4Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 62; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk4.Parent3

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
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left3.expected,
    Slot12.Left11.expected,
    Slot12.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 6692368057092484093706240 }, { target := 57, numerator := 169395634227183178416652288 }, { target := 59, numerator := 1807858811649726010127024128 }, { target := 67, numerator := 169555138777009812787953664 }, { target := 74, numerator := 6338471360180928091521024 }, { target := 110, numerator := 9352595515442277247877120 }, { target := 112, numerator := 364541050329523501337149440 }, { target := 115, numerator := 364540783851533549824901120 }, { target := 122, numerator := 9352302865908991178833920 }, { target := 152, numerator := 238799765760026036519567360 }, { target := 153, numerator := 6044443077417458491595948032 }, { target := 155, numerator := 64508744448331163859568033792 }, { target := 163, numerator := 6050134582847422370777399296 }, { target := 170, numerator := 226171881638177203694862336 }, { target := 206, numerator := 230772824808334058850353152 }, { target := 208, numerator := 8945565973024372195124576256 }, { target := 211, numerator := 8945560873472413333945581568 }, { target := 218, numerator := 230765417332702956132237312 }, { target := 283, numerator := 238800233999279294230036480 }, { target := 284, numerator := 6044454929378468255944933376 }, { target := 286, numerator := 64508870937258960518754861056 }, { target := 294, numerator := 6050146445968352011750473728 }, { target := 301, numerator := 226172325116639710122344448 }, { target := 302, numerator := 2500661926898522725116018688 }, { target := 304, numerator := 97255550888398623472984522752 }, { target := 307, numerator := 97255486034893153876087668736 }, { target := 314, numerator := 2500582871318649813124251648 }, { target := 660, numerator := 6692075407559198024663040 }, { target := 661, numerator := 169388226751552075698536448 }, { target := 663, numerator := 1807779756069853098135257088 }, { target := 671, numerator := 169547724326428787179782144 }, { target := 678, numerator := 6338194186141861574344704 }, { target := 679, numerator := 230824071113119720580055040 }, { target := 681, numerator := 8946140423236382821462310912 }, { target := 684, numerator := 8946135364743741763020128256 }, { target := 691, numerator := 230816656662538694971883520 }, { target := 966, numerator := 8957410992586491282063360 }, { target := 968, numerator := 349961609676290779944845312 }, { target := 971, numerator := 349961329840624333651705856 }, { target := 978, numerator := 8957133818547424764887040 }]

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
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot16.Left5.expected,
    Slot16.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 2660227458349793154170880 }, { target := 57, numerator := 61377190581150880433700864 }, { target := 59, numerator := 692803115248796714988994560 }, { target := 67, numerator := 61268932336109907792101376 }, { target := 74, numerator := 2618939632405563190542336 }, { target := 152, numerator := 125741284569497464817582080 }, { target := 153, numerator := 2901122895606913703528628224 }, { target := 155, numerator := 32746806440067459613416488960 }, { target := 163, numerator := 2896005840388960450684911616 }, { target := 170, numerator := 123789728038113576249982976 }, { target := 283, numerator := 125740549852254255594864640 }, { target := 284, numerator := 2901105944093945078000648192 }, { target := 286, numerator := 32746615097634193357332807680 }, { target := 294, numerator := 2895988918775389751269654528 }, { target := 301, numerator := 123789004723984623529361408 }, { target := 660, numerator := 2660227458349793154170880 }, { target := 661, numerator := 61377190581150880433700864 }, { target := 663, numerator := 692803115248796714988994560 }, { target := 671, numerator := 61268932336109907792101376 }, { target := 678, numerator := 2618939632405563190542336 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk4.Parent3
