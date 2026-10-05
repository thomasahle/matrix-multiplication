import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion0Branch1Chunk1Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 0, branch 1,
parent 33; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk1.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left5.expected,
    Slot8.Left12.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left6.expected,
    Slot10.Left14.expected,
    Slot15.Left0.expected,
    Slot15.Left3.expected,
    Slot15.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 14, numerator := 143217272664592826253705216 }, { target := 15, numerator := 7424291362408476043980570624 }, { target := 20, numerator := 7425664392019927014536380416 }, { target := 28, numerator := 141921825541042501865963520 }, { target := 56, numerator := 3345021255980400280338432 }, { target := 57, numerator := 168611086114389280335855616 }, { target := 59, numerator := 1851968525019284561266212864 }, { target := 67, numerator := 168612264077033715269632000 }, { target := 74, numerator := 3344628601765588635746304 }, { target := 110, numerator := 6402909291491309748486144 }, { target := 112, numerator := 232827506703911016525201408 }, { target := 115, numerator := 232935954667589891776315392 }, { target := 122, numerator := 6511585506606499391078400 }, { target := 136, numerator := 463186665161148582735118336 }, { target := 137, numerator := 24011299009947385021861986304 }, { target := 142, numerator := 24015739598677104012910657536 }, { target := 150, numerator := 458996990117865750181969920 }, { target := 152, numerator := 117344355073599526561382400 }, { target := 153, numerator := 5914927781991975885157171200 }, { target := 155, numerator := 64967614718878385234037964800 }, { target := 163, numerator := 5914969105277011781222400000 }, { target := 170, numerator := 117330580645254227872972800 }, { target := 206, numerator := 272999904287097836569362432 }, { target := 208, numerator := 9927032252360248169777332224 }, { target := 211, numerator := 9931656132280553579716018176 }, { target := 218, numerator := 277633516130413623587635200 }, { target := 257, numerator := 143217272664592826253705216 }, { target := 260, numerator := 463186665161148582735118336 }, { target := 262, numerator := 143300075528711986556698624 }, { target := 267, numerator := 143300075528711986556698624 }, { target := 268, numerator := 7428583809663090940639707136 }, { target := 273, numerator := 7429957633108848579050471424 }, { target := 281, numerator := 142003879426144332970721280 }, { target := 283, numerator := 117343966616176617672671232 }, { target := 284, numerator := 5914908201181280358698582016 }, { target := 286, numerator := 64967399649715745036345278464 }, { target := 294, numerator := 5914949524329519416082432000 }, { target := 301, numerator := 117330192233430265211387904 }, { target := 302, numerator := 2620516457179658523733131264 }, { target := 304, numerator := 95289232632499207193386549248 }, { target := 307, numerator := 95333617092848468752494231552 }, { target := 314, numerator := 2664994333914816976414310400 }, { target := 353, numerator := 7424291362408476043980570624 }, { target := 356, numerator := 24011299009947385021861986304 }, { target := 358, numerator := 7428583809663090940639707136 }, { target := 660, numerator := 3345697459642500938465280 }, { target := 661, numerator := 168645171229303715282288640 }, { target := 663, numerator := 1852342904672769349842370560 }, { target := 671, numerator := 168646349430075980513280000 }, { target := 678, numerator := 3345304726051745861468160 }, { target := 679, numerator := 273002178316679282518130688 }, { target := 681, numerator := 9927114942370916067616751616 }, { target := 684, numerator := 9931738860807131390734761984 }, { target := 691, numerator := 277635828756969776008396800 }, { target := 695, numerator := 7425664392019927014536380416 }, { target := 698, numerator := 24015739598677104012910657536 }, { target := 700, numerator := 7429957633108848579050471424 }, { target := 966, numerator := 6402340784095948261294080 }, { target := 968, numerator := 232806834201244042065346560 }, { target := 971, numerator := 232915272535945439021629440 }, { target := 978, numerator := 6511007349967461285888000 }, { target := 982, numerator := 141921825541042501865963520 }, { target := 985, numerator := 458996990117865750181969920 }, { target := 987, numerator := 142003879426144332970721280 }]

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
    Slot16.Left12.expected,
    Slot17.Left0.expected,
    Slot17.Left1.expected,
    Slot17.Left3.expected,
    Slot17.Left11.expected,
    Slot17.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 56, numerator := 6402909291491309748486144 }, { target := 57, numerator := 272999904287097836569362432 }, { target := 59, numerator := 2620516457179658523733131264 }, { target := 67, numerator := 273002178316679282518130688 }, { target := 74, numerator := 6402340784095948261294080 }, { target := 110, numerator := 3345021255980400280338432 }, { target := 112, numerator := 117344355073599526561382400 }, { target := 115, numerator := 117343966616176617672671232 }, { target := 122, numerator := 3345697459642500938465280 }, { target := 152, numerator := 232827506703911016525201408 }, { target := 153, numerator := 9927032252360248169777332224 }, { target := 155, numerator := 95289232632499207193386549248 }, { target := 163, numerator := 9927114942370916067616751616 }, { target := 170, numerator := 232806834201244042065346560 }, { target := 206, numerator := 168611086114389280335855616 }, { target := 208, numerator := 5914927781991975885157171200 }, { target := 211, numerator := 5914908201181280358698582016 }, { target := 218, numerator := 168645171229303715282288640 }, { target := 283, numerator := 232935954667589891776315392 }, { target := 284, numerator := 9931656132280553579716018176 }, { target := 286, numerator := 95333617092848468752494231552 }, { target := 294, numerator := 9931738860807131390734761984 }, { target := 301, numerator := 232915272535945439021629440 }, { target := 302, numerator := 1851968525019284561266212864 }, { target := 304, numerator := 64967614718878385234037964800 }, { target := 307, numerator := 64967399649715745036345278464 }, { target := 314, numerator := 1852342904672769349842370560 }, { target := 660, numerator := 6511585506606499391078400 }, { target := 661, numerator := 277633516130413623587635200 }, { target := 663, numerator := 2664994333914816976414310400 }, { target := 671, numerator := 277635828756969776008396800 }, { target := 678, numerator := 6511007349967461285888000 }, { target := 679, numerator := 168612264077033715269632000 }, { target := 681, numerator := 5914969105277011781222400000 }, { target := 684, numerator := 5914949524329519416082432000 }, { target := 691, numerator := 168646349430075980513280000 }, { target := 966, numerator := 3344628601765588635746304 }, { target := 968, numerator := 117330580645254227872972800 }, { target := 971, numerator := 117330192233430265211387904 }, { target := 978, numerator := 3345304726051745861468160 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk1.Parent2
