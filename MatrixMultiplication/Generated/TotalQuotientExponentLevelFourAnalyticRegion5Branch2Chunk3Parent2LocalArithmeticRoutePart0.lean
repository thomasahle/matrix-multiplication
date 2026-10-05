import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk3Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 54; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk3.Parent2

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
    Slot6.Left3.expected,
    Slot6.Left11.expected,
    Slot6.Left18.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left3.expected,
    Slot11.Left11.expected,
    Slot11.Left18.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 100283553729072259349348352 }, { target := 82, numerator := 3674506977203287517453877248 }, { target := 85, numerator := 3674511120722110281169240064 }, { target := 92, numerator := 100279531378471570130337792 }, { target := 131, numerator := 178331518007358389240201216 }, { target := 134, numerator := 635701715413926521893552128 }, { target := 136, numerator := 178197355393904853651554304 }, { target := 176, numerator := 3549837384279733638254297088 }, { target := 178, numerator := 131324536064567313784276779008 }, { target := 181, numerator := 131324645257317158735644196864 }, { target := 188, numerator := 3549699735838510221348569088 }, { target := 227, numerator := 4343089492359973069884751872 }, { target := 230, numerator := 15461986732201464294637830144 }, { target := 232, numerator := 4340293877387884089846005760 }, { target := 286, numerator := 3549843815994210475812323328 }, { target := 288, numerator := 131324732694098189983942705152 }, { target := 291, numerator := 131324841888280179616813940736 }, { target := 298, numerator := 3549706167147663092443250688 }, { target := 302, numerator := 47953083853298214427615559680 }, { target := 305, numerator := 170807752184660639470489436160 }, { target := 307, numerator := 47920124522342634948762009600 }, { target := 573, numerator := 100284923467373726694113280 }, { target := 575, numerator := 3674571720784897409491664896 }, { target := 578, numerator := 3674575863925417804507906048 }, { target := 585, numerator := 100280901116773037475102720 }, { target := 589, numerator := 4337425575331119266160181248 }, { target := 592, numerator := 15441657716697354029494173696 }, { target := 594, numerator := 4334637509752655796492042240 }, { target := 763, numerator := 176209345261215349580234752 }, { target := 766, numerator := 628080547324427797065105408 }, { target := 768, numerator := 176078111624578069363163136 }]

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
    Slot13.Left0.expected,
    Slot13.Left3.expected,
    Slot13.Left5.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected,
    Slot16.Left3.expected,
    Slot16.Left11.expected,
    Slot16.Left18.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected,
    Slot18.Left0.expected,
    Slot18.Left3.expected,
    Slot18.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 182138312102447483495383040 }, { target := 27, numerator := 4301523591638173766517784576 }, { target := 29, numerator := 47864257082483250349496860672 }, { target := 37, numerator := 4296969653185283173616975872 }, { target := 44, numerator := 177656641760418750290460672 }, { target := 80, numerator := 91983918006681198177288192 }, { target := 82, numerator := 3147772083585342483569049600 }, { target := 85, numerator := 3147781352614872360626946048 }, { target := 92, numerator := 91983918006681198177288192 }, { target := 131, numerator := 44293326281539750681640960 }, { target := 134, numerator := 156845722219342003951370240 }, { target := 136, numerator := 44353173111096751800975360 }, { target := 157, numerator := 651749879650243409126359040 }, { target := 158, numerator := 15388549101301783020571721728 }, { target := 160, numerator := 171257797652880816763492630528 }, { target := 168, numerator := 15372147152213762473222733824 }, { target := 175, numerator := 635774661308088051547766784 }, { target := 176, numerator := 3282207118062777405630578688 }, { target := 178, numerator := 112320068145310774763873894400 }, { target := 181, numerator := 112320398886546414311332380672 }, { target := 188, numerator := 3282207118062777405630578688 }, { target := 227, numerator := 1121142177699163474443108352 }, { target := 230, numerator := 3970041749722443546087129088 }, { target := 232, numerator := 1122657006465723980297797632 }, { target := 267, numerator := 182010897874641533974609920 }, { target := 268, numerator := 4298717903536855840928563200 }, { target := 270, numerator := 47831655545888523832484954112 }, { target := 278, numerator := 4294173012070270897024401408 }, { target := 285, numerator := 177528969162791028384595968 }, { target := 286, numerator := 3282213553823738508380995584 }, { target := 288, numerator := 112320288382816732230923059200 }, { target := 291, numerator := 112320619124700890124722896896 }, { target := 298, numerator := 3282213553823738508380995584 }, { target := 302, numerator := 11965283369388874107518451712 }, { target := 305, numerator := 42369893371793093025939324928 }, { target := 307, numerator := 11981450235472884609834811392 }, { target := 573, numerator := 91979895656080508958277632 }, { target := 575, numerator := 3147634435144119066663321600 }, { target := 578, numerator := 3147643703768324977257873408 }, { target := 585, numerator := 91979895656080508958277632 }, { target := 589, numerator := 1122197855899852668462432256 }, { target := 592, numerator := 3973779979016081417451864064 }, { target := 594, numerator := 1123714111043672405333508096 }, { target := 763, numerator := 41951066900026760884125696 }, { target := 766, numerator := 148551620259527227210727424 }, { target := 768, numerator := 42007748991015863646683136 }]

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
    Slot22.Left0.expected,
    Slot22.Left2.expected,
    Slot22.Left5.expected,
    Slot22.Left12.expected,
    Slot23.Left0.expected,
    Slot23.Left3.expected,
    Slot23.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 40486532186450656426459136 }, { target := 27, numerator := 1162708078420962777810075648 }, { target := 29, numerator := 12054110140203838185637150720 }, { target := 37, numerator := 1162653778045688761005637632 }, { target := 44, numerator := 40503770400823360173899776 }, { target := 80, numerator := 8299635722391061172060160 }, { target := 82, numerator := 402065300694391154685247488 }, { target := 85, numerator := 402062463379338115185377280 }, { target := 92, numerator := 8301005460692528516825088 }, { target := 157, numerator := 140797557983025116718563328 }, { target := 158, numerator := 4043479380622124820153237504 }, { target := 160, numerator := 41919847903572915732936130560 }, { target := 168, numerator := 4043290543499672973723303936 }, { target := 175, numerator := 140857506275866972728066048 }, { target := 176, numerator := 392299859140510111823298560 }, { target := 178, numerator := 19004467919256539020402884608 }, { target := 181, numerator := 19004333807551775672610324480 }, { target := 188, numerator := 392364602722120003861086208 }, { target := 267, numerator := 40539630630360071477919744 }, { target := 268, numerator := 1164232980316752229215240192 }, { target := 270, numerator := 12069919211926995726111866880 }, { target := 278, numerator := 1164178608726057304801148928 }, { target := 285, numerator := 40556891452802904625250304 }, { target := 286, numerator := 392297566898371772788244480 }, { target := 288, numerator := 19004356874500426504721137664 }, { target := 291, numerator := 19004222763579289492091043840 }, { target := 298, numerator := 392362310101679296126910464 }, { target := 573, numerator := 8299635722391061172060160 }, { target := 575, numerator := 402065300694391154685247488 }, { target := 578, numerator := 402062463379338115185377280 }, { target := 585, numerator := 8301005460692528516825088 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk3.Parent2
