import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch2Chunk5Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 2,
parent 54; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk5.Parent1

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
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left3.expected,
    Slot6.Left11.expected,
    Slot6.Left18.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left6.expected,
    Slot10.Left14.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left3.expected,
    Slot11.Left11.expected,
    Slot11.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 16861097074455172607901696 }, { target := 82, numerator := 776941793924677025973403648 }, { target := 85, numerator := 776940563754053910747152384 }, { target := 92, numerator := 16859488389794175773573120 }, { target := 131, numerator := 367957813851569669906890752 }, { target := 134, numerator := 1313576515252035117354319872 }, { target := 136, numerator := 367934945529958278321143808 }, { target := 176, numerator := 824578905423383747245375488 }, { target := 178, numerator := 37995737239582406062997766144 }, { target := 181, numerator := 37995677079039980318597578752 }, { target := 188, numerator := 824500233944827004568207360 }, { target := 227, numerator := 12036216588017425207032545280 }, { target := 230, numerator := 42978705356742938297496502272 }, { target := 232, numerator := 12035508837301119538874548224 }, { target := 263, numerator := 838302717426005275626700800 }, { target := 265, numerator := 838302666819619212817858560 }, { target := 286, numerator := 824579206346029548794019840 }, { target := 288, numerator := 37995751105784541618288721920 }, { target := 291, numerator := 37995690945220160825705103360 }, { target := 298, numerator := 824500534838762358492364800 }, { target := 302, numerator := 145821461341416544256680525824 }, { target := 305, numerator := 520768132330931855660307972096 }, { target := 307, numerator := 145813161416003203389645127680 }, { target := 338, numerator := 38777381781118210856911372288 }, { target := 340, numerator := 38777377113375887867642904576 }, { target := 573, numerator := 16862200457489778286264320 }, { target := 575, numerator := 776992636665840728706908160 }, { target := 578, numerator := 776991406414715770141409280 }, { target := 585, numerator := 16860591667557140162150400 }, { target := 589, numerator := 12036247271365945655392468992 }, { target := 592, numerator := 42978814000576890691368517632 }, { target := 594, numerator := 12035539515312030003870302208 }, { target := 599, numerator := 38768926381059306519730847744 }, { target := 601, numerator := 38768921719059636005313183744 }, { target := 763, numerator := 392163523402032156405399552 }, { target := 766, numerator := 1400390023081389021821140992 }, { target := 768, numerator := 392140692387114178049998848 }, { target := 773, numerator := 843556357027297810920243200 }, { target := 775, numerator := 843556292642711638124789760 }]

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
    Slot12.Left0.expected,
    Slot12.Left2.expected,
    Slot12.Left5.expected,
    Slot12.Left12.expected,
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
    Slot17.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 87554836030586609064738816 }, { target := 27, numerator := 3059819109946752077899235328 }, { target := 29, numerator := 36917791655584205924839981056 }, { target := 37, numerator := 3059891228777360039098712064 }, { target := 44, numerator := 87557411703108321964720128 }, { target := 80, numerator := 422262661483743229771776000 }, { target := 82, numerator := 14881933652917075373792952320 }, { target := 85, numerator := 14881941765552262381347799040 }, { target := 92, numerator := 422258068085154039275192320 }, { target := 131, numerator := 87554836030586609064738816 }, { target := 134, numerator := 306359099166549626012565504 }, { target := 136, numerator := 87668276359427314170200064 }, { target := 157, numerator := 306359099166549626012565504 }, { target := 158, numerator := 10706472293642420282544095232 }, { target := 160, numerator := 129177346535970246585760088064 }, { target := 168, numerator := 10706724641325080341660041216 }, { target := 175, numerator := 306368111583787485266706432 }, { target := 176, numerator := 14881933652917075373792952320 }, { target := 178, numerator := 524410875406207898432600801280 }, { target := 181, numerator := 524411164802732063906825502720 }, { target := 188, numerator := 14881772963543933222142345216 }, { target := 227, numerator := 3059819109946752077899235328 }, { target := 230, numerator := 10706472293642420282544095232 }, { target := 232, numerator := 3063783561275336304164339712 }, { target := 267, numerator := 87668276359427314170200064 }, { target := 268, numerator := 3063783561275336304164339712 }, { target := 270, numerator := 36965624152512406183187841024 }, { target := 278, numerator := 3063855773546629334046867456 }, { target := 285, numerator := 87670855369116350951718912 }, { target := 286, numerator := 14881941765552262381347799040 }, { target := 288, numerator := 524411164802732063906825502720 }, { target := 291, numerator := 524411454199256229381050204160 }, { target := 298, numerator := 14881781076037256841435021312 }, { target := 302, numerator := 36917791655584205924839981056 }, { target := 305, numerator := 129177346535970246585760088064 }, { target := 307, numerator := 36965624152512406183187841024 }, { target := 573, numerator := 422258068085154039275192320 }, { target := 575, numerator := 14881772963543933222142345216 }, { target := 578, numerator := 14881781076037256841435021312 }, { target := 585, numerator := 422253474718090046170202112 }, { target := 589, numerator := 3059891228777360039098712064 }, { target := 592, numerator := 10706724641325080341660041216 }, { target := 594, numerator := 3063855773546629334046867456 }, { target := 763, numerator := 87557411703108321964720128 }, { target := 766, numerator := 306368111583787485266706432 }, { target := 768, numerator := 87670855369116350951718912 }]

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
    Slot18.Left3.expected,
    Slot18.Left5.expected,
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot22.Left0.expected,
    Slot22.Left2.expected,
    Slot22.Left5.expected,
    Slot22.Left12.expected,
    Slot23.Left0.expected,
    Slot23.Left3.expected,
    Slot23.Left5.expected,
    Slot24.Left0.expected,
    Slot24.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 838302717426005275626700800 }, { target := 11, numerator := 38777381781118210856911372288 }, { target := 16, numerator := 38768926381059306519730847744 }, { target := 24, numerator := 843556357027297810920243200 }, { target := 26, numerator := 367957813851569669906890752 }, { target := 27, numerator := 12036216588017425207032545280 }, { target := 29, numerator := 145821461341416544256680525824 }, { target := 37, numerator := 12036247271365945655392468992 }, { target := 44, numerator := 392163523402032156405399552 }, { target := 80, numerator := 16861097074455172607901696 }, { target := 82, numerator := 824578905423383747245375488 }, { target := 85, numerator := 824579206346029548794019840 }, { target := 92, numerator := 16862200457489778286264320 }, { target := 141, numerator := 838302666819619212817858560 }, { target := 142, numerator := 38777377113375887867642904576 }, { target := 147, numerator := 38768921719059636005313183744 }, { target := 155, numerator := 843556292642711638124789760 }, { target := 157, numerator := 1313576515252035117354319872 }, { target := 158, numerator := 42978705356742938297496502272 }, { target := 160, numerator := 520768132330931855660307972096 }, { target := 168, numerator := 42978814000576890691368517632 }, { target := 175, numerator := 1400390023081389021821140992 }, { target := 176, numerator := 776941793924677025973403648 }, { target := 178, numerator := 37995737239582406062997766144 }, { target := 181, numerator := 37995751105784541618288721920 }, { target := 188, numerator := 776992636665840728706908160 }, { target := 267, numerator := 367934945529958278321143808 }, { target := 268, numerator := 12035508837301119538874548224 }, { target := 270, numerator := 145813161416003203389645127680 }, { target := 278, numerator := 12035539515312030003870302208 }, { target := 285, numerator := 392140692387114178049998848 }, { target := 286, numerator := 776940563754053910747152384 }, { target := 288, numerator := 37995677079039980318597578752 }, { target := 291, numerator := 37995690945220160825705103360 }, { target := 298, numerator := 776991406414715770141409280 }, { target := 573, numerator := 16859488389794175773573120 }, { target := 575, numerator := 824500233944827004568207360 }, { target := 578, numerator := 824500534838762358492364800 }, { target := 585, numerator := 16860591667557140162150400 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk5.Parent1
