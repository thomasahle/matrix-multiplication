import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk0Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 20; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk0.Parent2

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
  [{ target := 110, numerator := 4350674966077939210256384 }, { target := 112, numerator := 160063236501511628549783552 }, { target := 115, numerator := 160063412898501833397370880 }, { target := 122, numerator := 4350498569087734362669056 }, { target := 206, numerator := 34805399728623513682051072 }, { target := 208, numerator := 1280505892012093028398268416 }, { target := 211, numerator := 1280507303188014667178967040 }, { target := 218, numerator := 34803988552701874901352448 }, { target := 241, numerator := 35061321785451627753242624 }, { target := 243, numerator := 1289921376512181947724726272 }, { target := 246, numerator := 1289922798064397127967047680 }, { target := 253, numerator := 35059900233236447510921216 }, { target := 302, numerator := 4862519079734167352639488 }, { target := 304, numerator := 178894205501689467202699264 }, { target := 307, numerator := 178894402651266754973532160 }, { target := 314, numerator := 4862321930156879581806592 }, { target := 337, numerator := 31222490933029916685369344 }, { target := 339, numerator := 1148689109010848157827858432 }, { target := 342, numerator := 1148690374918660216145838080 }, { target := 349, numerator := 31221225025217858367389696 }, { target := 363, numerator := 4862519079734167352639488 }, { target := 365, numerator := 178894205501689467202699264 }, { target := 368, numerator := 178894402651266754973532160 }, { target := 375, numerator := 4862321930156879581806592 }, { target := 473, numerator := 34805399728623513682051072 }, { target := 475, numerator := 1280505892012093028398268416 }, { target := 478, numerator := 1280507303188014667178967040 }, { target := 485, numerator := 34803988552701874901352448 }, { target := 508, numerator := 35061321785451627753242624 }, { target := 510, numerator := 1289921376512181947724726272 }, { target := 513, numerator := 1289922798064397127967047680 }, { target := 520, numerator := 35059900233236447510921216 }, { target := 569, numerator := 31222490933029916685369344 }, { target := 571, numerator := 1148689109010848157827858432 }, { target := 574, numerator := 1148690374918660216145838080 }, { target := 581, numerator := 31221225025217858367389696 }, { target := 604, numerator := 615492546671614341215682560 }, { target := 606, numerator := 22644240222713850980131143680 }, { target := 609, numerator := 22644265177699818195333939200 }, { target := 616, numerator := 615467591685647126012887040 }, { target := 630, numerator := 31222490933029916685369344 }, { target := 632, numerator := 1148689109010848157827858432 }, { target := 635, numerator := 1148690374918660216145838080 }, { target := 642, numerator := 31221225025217858367389696 }, { target := 679, numerator := 34805399728623513682051072 }, { target := 681, numerator := 1280505892012093028398268416 }, { target := 684, numerator := 1280507303188014667178967040 }, { target := 691, numerator := 34803988552701874901352448 }, { target := 705, numerator := 34805399728623513682051072 }, { target := 707, numerator := 1280505892012093028398268416 }, { target := 710, numerator := 1280507303188014667178967040 }, { target := 717, numerator := 34803988552701874901352448 }, { target := 785, numerator := 4862519079734167352639488 }, { target := 787, numerator := 178894205501689467202699264 }, { target := 790, numerator := 178894402651266754973532160 }, { target := 797, numerator := 4862321930156879581806592 }, { target := 820, numerator := 31222490933029916685369344 }, { target := 822, numerator := 1148689109010848157827858432 }, { target := 825, numerator := 1148690374918660216145838080 }, { target := 832, numerator := 31221225025217858367389696 }, { target := 846, numerator := 4862519079734167352639488 }, { target := 848, numerator := 178894205501689467202699264 }, { target := 851, numerator := 178894402651266754973532160 }, { target := 858, numerator := 4862321930156879581806592 }]

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
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left3.expected,
    Slot11.Left11.expected,
    Slot11.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 5017032631241458776539136 }, { target := 57, numerator := 169912734757676888679776256 }, { target := 59, numerator := 1844002255842885428400095232 }, { target := 67, numerator := 169912473229142927647703040 }, { target := 74, numerator := 5015855752838634132209664 }, { target := 110, numerator := 5017032631241458776539136 }, { target := 112, numerator := 176166175006625122461155328 }, { target := 115, numerator := 176156779571749754228441088 }, { target := 122, numerator := 5026082486903020361613312 }, { target := 152, numerator := 176166175006625122461155328 }, { target := 153, numerator := 5966251122382739460312793088 }, { target := 155, numerator := 64749593632809463381005172736 }, { target := 163, numerator := 5966241939169300482799697920 }, { target := 170, numerator := 176124850546149723652227072 }, { target := 206, numerator := 169912734757676888679776256 }, { target := 208, numerator := 5966251122382739460312793088 }, { target := 211, numerator := 5965932925521915686628098048 }, { target := 218, numerator := 170219227825918638504804352 }, { target := 283, numerator := 176156779571749754228441088 }, { target := 284, numerator := 5965932925521915686628098048 }, { target := 286, numerator := 64746140355867049546383097856 }, { target := 294, numerator := 5965923742798243168591544320 }, { target := 301, numerator := 176115457315223423063949312 }, { target := 302, numerator := 1844002255842885428400095232 }, { target := 304, numerator := 64749593632809463381005172736 }, { target := 307, numerator := 64746140355867049546383097856 }, { target := 314, numerator := 1847328515702359903587794944 }, { target := 660, numerator := 5026082486903020361613312 }, { target := 661, numerator := 170219227825918638504804352 }, { target := 663, numerator := 1847328515702359903587794944 }, { target := 671, numerator := 170218965825632616505671680 }, { target := 678, numerator := 5024903485615921365516288 }, { target := 679, numerator := 169912473229142927647703040 }, { target := 681, numerator := 5966241939169300482799697920 }, { target := 684, numerator := 5965923742798243168591544320 }, { target := 691, numerator := 170218965825632616505671680 }, { target := 895, numerator := 35061321785451627753242624 }, { target := 897, numerator := 1289921376512181947724726272 }, { target := 900, numerator := 1289922798064397127967047680 }, { target := 907, numerator := 35059900233236447510921216 }, { target := 921, numerator := 35061321785451627753242624 }, { target := 923, numerator := 1289921376512181947724726272 }, { target := 926, numerator := 1289922798064397127967047680 }, { target := 933, numerator := 35059900233236447510921216 }, { target := 966, numerator := 9622452775744687413657600 }, { target := 968, numerator := 345603571547750271528468480 }, { target := 971, numerator := 345594365090107717249400832 }, { target := 978, numerator := 9631313735238228337754112 }]

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
    Slot18.Left0.expected,
    Slot18.Left2.expected,
    Slot18.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 4350674966077939210256384 }, { target := 57, numerator := 34805399728623513682051072 }, { target := 58, numerator := 35061321785451627753242624 }, { target := 59, numerator := 4862519079734167352639488 }, { target := 60, numerator := 31222490933029916685369344 }, { target := 61, numerator := 4862519079734167352639488 }, { target := 62, numerator := 34805399728623513682051072 }, { target := 63, numerator := 35061321785451627753242624 }, { target := 64, numerator := 31222490933029916685369344 }, { target := 65, numerator := 615492546671614341215682560 }, { target := 66, numerator := 31222490933029916685369344 }, { target := 67, numerator := 34805399728623513682051072 }, { target := 68, numerator := 34805399728623513682051072 }, { target := 69, numerator := 4862519079734167352639488 }, { target := 70, numerator := 31222490933029916685369344 }, { target := 71, numerator := 4862519079734167352639488 }, { target := 72, numerator := 35061321785451627753242624 }, { target := 73, numerator := 35061321785451627753242624 }, { target := 74, numerator := 4606597022906053281447936 }, { target := 152, numerator := 160063236501511628549783552 }, { target := 153, numerator := 1280505892012093028398268416 }, { target := 154, numerator := 1289921376512181947724726272 }, { target := 155, numerator := 178894205501689467202699264 }, { target := 156, numerator := 1148689109010848157827858432 }, { target := 157, numerator := 178894205501689467202699264 }, { target := 158, numerator := 1280505892012093028398268416 }, { target := 159, numerator := 1289921376512181947724726272 }, { target := 160, numerator := 1148689109010848157827858432 }, { target := 161, numerator := 22644240222713850980131143680 }, { target := 162, numerator := 1148689109010848157827858432 }, { target := 163, numerator := 1280505892012093028398268416 }, { target := 164, numerator := 1280505892012093028398268416 }, { target := 165, numerator := 178894205501689467202699264 }, { target := 166, numerator := 1148689109010848157827858432 }, { target := 167, numerator := 178894205501689467202699264 }, { target := 168, numerator := 1289921376512181947724726272 }, { target := 169, numerator := 1289921376512181947724726272 }, { target := 170, numerator := 169478721001600547876241408 }, { target := 283, numerator := 160063412898501833397370880 }, { target := 284, numerator := 1280507303188014667178967040 }, { target := 285, numerator := 1289922798064397127967047680 }, { target := 286, numerator := 178894402651266754973532160 }, { target := 287, numerator := 1148690374918660216145838080 }, { target := 288, numerator := 178894402651266754973532160 }, { target := 289, numerator := 1280507303188014667178967040 }, { target := 290, numerator := 1289922798064397127967047680 }, { target := 291, numerator := 1148690374918660216145838080 }, { target := 292, numerator := 22644265177699818195333939200 }, { target := 293, numerator := 1148690374918660216145838080 }, { target := 294, numerator := 1280507303188014667178967040 }, { target := 295, numerator := 1280507303188014667178967040 }, { target := 296, numerator := 178894402651266754973532160 }, { target := 297, numerator := 1148690374918660216145838080 }, { target := 298, numerator := 178894402651266754973532160 }, { target := 299, numerator := 1289922798064397127967047680 }, { target := 300, numerator := 1289922798064397127967047680 }, { target := 301, numerator := 169478907774884294185451520 }]

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
    Slot18.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 660, numerator := 4350498569087734362669056 }, { target := 661, numerator := 34803988552701874901352448 }, { target := 662, numerator := 35059900233236447510921216 }, { target := 663, numerator := 4862321930156879581806592 }, { target := 664, numerator := 31221225025217858367389696 }, { target := 665, numerator := 4862321930156879581806592 }, { target := 666, numerator := 34803988552701874901352448 }, { target := 667, numerator := 35059900233236447510921216 }, { target := 668, numerator := 31221225025217858367389696 }, { target := 669, numerator := 615467591685647126012887040 }, { target := 670, numerator := 31221225025217858367389696 }, { target := 671, numerator := 34803988552701874901352448 }, { target := 672, numerator := 34803988552701874901352448 }, { target := 673, numerator := 4862321930156879581806592 }, { target := 674, numerator := 31221225025217858367389696 }, { target := 675, numerator := 4862321930156879581806592 }, { target := 676, numerator := 35059900233236447510921216 }, { target := 677, numerator := 35059900233236447510921216 }, { target := 678, numerator := 4606410249622306972237824 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk0.Parent2
