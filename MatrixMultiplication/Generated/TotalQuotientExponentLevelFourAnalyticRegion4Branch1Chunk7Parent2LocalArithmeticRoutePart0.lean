import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk7Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 65; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk7.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left3.expected,
    Slot4.Left11.expected,
    Slot4.Left18.expected,
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
    Slot13.Left0.expected,
    Slot13.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 164877635916826984788787200 }, { target := 27, numerator := 5603600218809784090094469120 }, { target := 29, numerator := 61700673048328763712701726720 }, { target := 37, numerator := 5603687524944767848095416320 }, { target := 44, numerator := 164855809383081045288550400 }, { target := 80, numerator := 63662173660266007741071360 }, { target := 82, numerator := 2556977501425640395715379200 }, { target := 85, numerator := 2557474537549192067452764160 }, { target := 92, numerator := 63169511204677707093770240 }, { target := 131, numerator := 145234436377155102310400000 }, { target := 134, numerator := 501550139252316253617913856 }, { target := 136, numerator := 145260175610391278603206656 }, { target := 157, numerator := 562063372673531769991987200 }, { target := 158, numerator := 19102520609206102901517189120 }, { target := 160, numerator := 210335914855455713051510046720 }, { target := 168, numerator := 19102818233443684861681336320 }, { target := 175, numerator := 561988966614136279950950400 }, { target := 176, numerator := 2342159236953881920489390080 }, { target := 178, numerator := 94072321589377183449192857600 }, { target := 181, numerator := 94090607765939245791292948480 }, { target := 188, numerator := 2324033969550756644881694720 }, { target := 227, numerator := 6623625267571529252182425600 }, { target := 230, numerator := 22895069715043463577265504256 }, { target := 232, numerator := 6624890812057376481907572736 }, { target := 263, numerator := 377967912465541596849373184 }, { target := 265, numerator := 377969624646299730378227712 }, { target := 286, numerator := 2342161818120232228827955200 }, { target := 288, numerator := 94072425261368033090207744000 }, { target := 291, numerator := 94090711458082296389907251200 }, { target := 298, numerator := 2324036530742235230948556800 }, { target := 302, numerator := 73575084984495076468273971200 }, { target := 305, numerator := 254333518027315338991089221632 }, { target := 307, numerator := 73589210151647286472675950592 }, { target := 338, numerator := 19428935767681112539568013312 }, { target := 340, numerator := 19429023780046383013813026816 }, { target := 573, numerator := 63659592493915699402506240 }, { target := 575, numerator := 2556873829434790754700492800 }, { target := 578, numerator := 2557370845406141468838461440 }, { target := 585, numerator := 63166950013199121026908160 }, { target := 589, numerator := 6623632161907018812306227200 }, { target := 592, numerator := 22895093703304749179627110400 }, { target := 594, numerator := 6624897708392464276583874560 }, { target := 599, numerator := 19433452700991206376712699904 }, { target := 601, numerator := 19433540733818018807962140672 }, { target := 763, numerator := 145209304173135175195033600 }, { target := 766, numerator := 501463459005935134361780224 }, { target := 768, numerator := 145235039432789105263509504 }, { target := 773, numerator := 373635151031133760382828544 }, { target := 775, numerator := 373636843584641767877640192 }]

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
    Slot13.Left5.expected,
    Slot14.Left0.expected,
    Slot14.Left2.expected,
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
    Slot20.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 377967912465541596849373184 }, { target := 11, numerator := 19428935767681112539568013312 }, { target := 16, numerator := 19433452700991206376712699904 }, { target := 24, numerator := 373635151031133760382828544 }, { target := 26, numerator := 111756180055875325735731200 }, { target := 27, numerator := 5489811217600013140806860800 }, { target := 29, numerator := 61270205842648584888621465600 }, { target := 37, numerator := 5489819857094432055833395200 }, { target := 44, numerator := 111738901067037495682662400 }, { target := 80, numerator := 316832531097760832390430720 }, { target := 82, numerator := 10761840271598756419967385600 }, { target := 85, numerator := 10761842852765106728305950720 }, { target := 92, numerator := 316827882162751361997864960 }, { target := 131, numerator := 164877635916826984788787200 }, { target := 134, numerator := 562063372673531769991987200 }, { target := 136, numerator := 164877901699573743825715200 }, { target := 141, numerator := 377969624646299730378227712 }, { target := 142, numerator := 19429023780046383013813026816 }, { target := 147, numerator := 19433540733818018807962140672 }, { target := 155, numerator := 373636843584641767877640192 }, { target := 157, numerator := 387323541451163108649205760 }, { target := 158, numerator := 19026537249537743145234595840 }, { target := 160, numerator := 212349716145910550035829882880 }, { target := 168, numerator := 19026567192218076426755112960 }, { target := 175, numerator := 387263656090496545608171520 }, { target := 176, numerator := 8419681034644874499477995520 }, { target := 178, numerator := 280013147837265487321513328640 }, { target := 181, numerator := 280013147837265487321513328640 }, { target := 188, numerator := 8419612266907846367552471040 }, { target := 227, numerator := 5603600218809784090094469120 }, { target := 230, numerator := 19102520609206102901517189120 }, { target := 232, numerator := 5603609251813257321035857920 }, { target := 267, numerator := 276659896584138266058424320 }, { target := 268, numerator := 11094688574103745009287168000 }, { target := 270, numerator := 122985131304600530235508654080 }, { target := 278, numerator := 11094784521869542755548528640 }, { target := 285, numerator := 276620787035054954659184640 }, { target := 286, numerator := 8419681034644874499477995520 }, { target := 288, numerator := 280013147837265487321513328640 }, { target := 291, numerator := 280013147837265487321513328640 }, { target := 298, numerator := 8419612266907846367552471040 }, { target := 302, numerator := 61700673048328763712701726720 }, { target := 305, numerator := 210335914855455713051510046720 }, { target := 307, numerator := 61700772509812842357608939520 }, { target := 573, numerator := 253168289668835662595358720 }, { target := 575, numerator := 8419612266907846367552471040 }, { target := 578, numerator := 8419612266907846367552471040 }, { target := 585, numerator := 253166221917064999143997440 }, { target := 589, numerator := 5603687524944767848095416320 }, { target := 592, numerator := 19102818233443684861681336320 }, { target := 594, numerator := 5603696558088978567392133120 }, { target := 763, numerator := 164855809383081045288550400 }, { target := 766, numerator := 561988966614136279950950400 }, { target := 768, numerator := 164856075130643432236646400 }]

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
    Slot20.Left2.expected,
    Slot20.Left5.expected,
    Slot20.Left12.expected,
    Slot24.Left0.expected,
    Slot24.Left3.expected,
    Slot24.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 33478256321279776574668800 }, { target := 27, numerator := 1133814049971516111375564800 }, { target := 29, numerator := 12304879141846491579652505600 }, { target := 37, numerator := 1133812304812586756472832000 }, { target := 44, numerator := 33470403106097679512371200 }, { target := 157, numerator := 114226597801153144968708096 }, { target := 158, numerator := 3868532465505720432030908416 }, { target := 160, numerator := 41983801881404788955259338752 }, { target := 168, numerator := 3868526511086672752871997440 }, { target := 175, numerator := 114199802915438588753608704 }, { target := 176, numerator := 2556977501425640395715379200 }, { target := 178, numerator := 94072321589377183449192857600 }, { target := 181, numerator := 94072425261368033090207744000 }, { target := 188, numerator := 2556873829434790754700492800 }, { target := 267, numerator := 33478180725826756370497536 }, { target := 268, numerator := 1133811489766888793656262656 }, { target := 270, numerator := 12304851356859598594776236032 }, { target := 278, numerator := 1133809744611900088427479040 }, { target := 285, numerator := 33470327528377582840971264 }, { target := 286, numerator := 2557474537549192067452764160 }, { target := 288, numerator := 94090607765939245791292948480 }, { target := 291, numerator := 94090711458082296389907251200 }, { target := 298, numerator := 2557370845406141468838461440 }, { target := 573, numerator := 63169511204677707093770240 }, { target := 575, numerator := 2324033969550756644881694720 }, { target := 578, numerator := 2324036530742235230948556800 }, { target := 585, numerator := 63166950013199121026908160 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk7.Parent2
