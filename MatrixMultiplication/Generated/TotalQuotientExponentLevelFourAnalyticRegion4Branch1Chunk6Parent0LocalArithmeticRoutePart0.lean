import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk6Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 57; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk6.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left6.expected,
    Slot5.Left14.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left6.expected,
    Slot10.Left14.expected,
    Slot13.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 11033337862800831873548288 }, { target := 30, numerator := 567153997917811573662941184 }, { target := 35, numerator := 567285852632644140639715328 }, { target := 43, numerator := 10906859346482086237175808 }, { target := 71, numerator := 825127852968365323714560 }, { target := 72, numerator := 28043139942714922160357376 }, { target := 74, numerator := 308780166551834687340281856 }, { target := 82, numerator := 28043576865062271043239936 }, { target := 89, numerator := 825018622381528102993920 }, { target := 146, numerator := 40532846961261204775895040 }, { target := 147, numerator := 1377566271120500051656310784 }, { target := 149, numerator := 15168242340254757763210543104 }, { target := 157, numerator := 1377587734105388196323917824 }, { target := 164, numerator := 40527481215039168608993280 }, { target := 200, numerator := 19114854987111781772558336 }, { target := 202, numerator := 691527871456696459461656576 }, { target := 205, numerator := 691590967102241327340847104 }, { target := 212, numerator := 19052224436744681745809408 }, { target := 242, numerator := 452375460333359581133537280 }, { target := 243, numerator := 15374621393691890215381106688 }, { target := 245, numerator := 169288395105301385446768508928 }, { target := 253, numerator := 15374860935900168404198227968 }, { target := 260, numerator := 452315574781290033929256960 }, { target := 296, numerator := 1040236762916330209410023424 }, { target := 298, numerator := 37863095514515188255018713088 }, { target := 301, numerator := 37866789061406766189907017728 }, { target := 308, numerator := 1036571085150426772723990528 }, { target := 640, numerator := 40532910749120426944757760 }, { target := 641, numerator := 1377568439041333627082244096 }, { target := 643, numerator := 15168266211010936637988274176 }, { target := 651, numerator := 1377589902059998768955129856 }, { target := 658, numerator := 40527544994454141476536320 }, { target := 659, numerator := 1040525667263765981519937536 }, { target := 661, numerator := 37873788468567378069664301056 }, { target := 664, numerator := 37877483241608427602490425344 }, { target := 671, numerator := 1036858773060966493273980928 }, { target := 1017, numerator := 825000277249920985989120 }, { target := 1018, numerator := 28038804101047771308490752 }, { target := 1020, numerator := 308732425039476937784819712 }, { target := 1028, numerator := 28039240955841125780815872 }, { target := 1035, numerator := 824891063551582367907840 }, { target := 1036, numerator := 18831326838189831003045888 }, { target := 1038, numerator := 681013713520779787822432256 }, { target := 1041, numerator := 681075583016853057763803136 }, { target := 1048, numerator := 18769912680808686169358336 }]

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
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left3.expected,
    Slot14.Left11.expected,
    Slot14.Left18.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot18.Left5.expected,
    Slot18.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 8081517124310949899010048 }, { target := 30, numerator := 473082764998518635747082240 }, { target := 35, numerator := 473239814631121840880222208 }, { target := 43, numerator := 7924467491707744765870080 }, { target := 71, numerator := 825127852968365323714560 }, { target := 72, numerator := 40532846961261204775895040 }, { target := 74, numerator := 452375460333359581133537280 }, { target := 82, numerator := 40532910749120426944757760 }, { target := 89, numerator := 825000277249920985989120 }, { target := 104, numerator := 691527871456696459461656576 }, { target := 105, numerator := 37863095514515188255018713088 }, { target := 110, numerator := 37873788468567378069664301056 }, { target := 118, numerator := 681013713520779787822432256 }, { target := 146, numerator := 28043139942714922160357376 }, { target := 147, numerator := 1377566271120500051656310784 }, { target := 149, numerator := 15374621393691890215381106688 }, { target := 157, numerator := 1377568439041333627082244096 }, { target := 164, numerator := 28038804101047771308490752 }, { target := 226, numerator := 691590967102241327340847104 }, { target := 227, numerator := 37866789061406766189907017728 }, { target := 232, numerator := 37877483241608427602490425344 }, { target := 240, numerator := 681075583016853057763803136 }, { target := 242, numerator := 308780166551834687340281856 }, { target := 243, numerator := 15168242340254757763210543104 }, { target := 245, numerator := 169288395105301385446768508928 }, { target := 253, numerator := 15168266211010936637988274176 }, { target := 260, numerator := 308732425039476937784819712 }, { target := 624, numerator := 19052224436744681745809408 }, { target := 625, numerator := 1036571085150426772723990528 }, { target := 630, numerator := 1036858773060966493273980928 }, { target := 638, numerator := 18769912680808686169358336 }, { target := 640, numerator := 28043576865062271043239936 }, { target := 641, numerator := 1377587734105388196323917824 }, { target := 643, numerator := 15374860935900168404198227968 }, { target := 651, numerator := 1377589902059998768955129856 }, { target := 658, numerator := 28039240955841125780815872 }, { target := 1017, numerator := 825018622381528102993920 }, { target := 1018, numerator := 40527481215039168608993280 }, { target := 1020, numerator := 452315574781290033929256960 }, { target := 1028, numerator := 40527544994454141476536320 }, { target := 1035, numerator := 824891063551582367907840 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk6.Parent0
