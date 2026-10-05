import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk3Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 44; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk3.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left0.expected,
    Slot6.Left3.expected,
    Slot6.Left5.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left5.expected,
    Slot7.Left12.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left6.expected,
    Slot9.Left14.expected,
    Slot13.Left0.expected,
    Slot13.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 150049629895867204139745280 }, { target := 27, numerator := 6869132593592377014222848000 }, { target := 29, numerator := 76495630425592427027177144320 }, { target := 37, numerator := 6869159184043660410418626560 }, { target := 44, numerator := 150027167244155022276034560 }, { target := 80, numerator := 80051595870799758580776960 }, { target := 82, numerator := 2662274171307099364754718720 }, { target := 85, numerator := 2662274171307099364754718720 }, { target := 92, numerator := 80050942049464856000593920 }, { target := 131, numerator := 167483724046092161117061120 }, { target := 134, numerator := 570947456165353280891781120 }, { target := 136, numerator := 167483994029852947560529920 }, { target := 157, numerator := 489381878386274322087936000 }, { target := 158, numerator := 22343300981071395756812795904 }, { target := 160, numerator := 248796444542781197050670219264 }, { target := 168, numerator := 22343389501844087515239153664 }, { target := 175, numerator := 489308705539120545608499200 }, { target := 176, numerator := 2810901280553425705191342080 }, { target := 178, numerator := 93482082348356220729488834560 }, { target := 181, numerator := 93482082348356220729488834560 }, { target := 188, numerator := 2810878322519828261408604160 }, { target := 227, numerator := 5672201014373271939338731520 }, { target := 230, numerator := 19336378853886128100495851520 }, { target := 232, numerator := 5672210157961226645479096320 }, { target := 263, numerator := 332675261197531591296942080 }, { target := 265, numerator := 332673119673421331796328448 }, { target := 267, numerator := 33125237288959827278561280 }, { target := 268, numerator := 1125808153958358342684377088 }, { target := 270, numerator := 12396159274417571845875171328 }, { target := 278, numerator := 1125825694459967535073722368 }, { target := 285, numerator := 33120852163557529181224960 }, { target := 286, numerator := 2810751367325636456276295680 }, { target := 288, numerator := 93477096687421681164888309760 }, { target := 291, numerator := 93477096687421681164888309760 }, { target := 298, numerator := 2810728410516455161184911360 }, { target := 302, numerator := 61558372778918736546957885440 }, { target := 305, numerator := 209850817110620876179966525440 }, { target := 307, numerator := 61558472011014782921515991040 }, { target := 338, numerator := 19474429119316071547299430400 }, { target := 340, numerator := 19474303756945144326379274240 }, { target := 573, numerator := 80195995048831242018488320 }, { target := 575, numerator := 2667076451609563910887178240 }, { target := 578, numerator := 2667076451609563910887178240 }, { target := 585, numerator := 80195340048116187020656640 }, { target := 589, numerator := 5672192283759773563538636800 }, { target := 592, numerator := 19336349091462369904479436800 }, { target := 594, numerator := 5672201427333654520843468800 }, { target := 599, numerator := 19480894059839439219908935680 }, { target := 601, numerator := 19480768655851873742364868608 }, { target := 763, numerator := 167444436285349470016634880 }, { target := 766, numerator := 570813525258441398817914880 }, { target := 768, numerator := 167444706205778386700206080 }, { target := 773, numerator := 326210320674163918687436800 }, { target := 775, numerator := 326208220766691915810734080 }]

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
    Slot19.Left0.expected,
    Slot19.Left2.expected,
    Slot20.Left0.expected,
    Slot20.Left3.expected,
    Slot20.Left5.expected,
    Slot21.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 332675261197531591296942080 }, { target := 11, numerator := 19474429119316071547299430400 }, { target := 16, numerator := 19480894059839439219908935680 }, { target := 24, numerator := 326210320674163918687436800 }, { target := 26, numerator := 167483724046092161117061120 }, { target := 27, numerator := 5672201014373271939338731520 }, { target := 29, numerator := 61558372778918736546957885440 }, { target := 37, numerator := 5672192283759773563538636800 }, { target := 44, numerator := 167444436285349470016634880 }, { target := 80, numerator := 288091673050490715053752320 }, { target := 82, numerator := 10464786789133399015722844160 }, { target := 85, numerator := 10464645310836681982481530880 }, { target := 92, numerator := 288227637297449982817730560 }, { target := 131, numerator := 116900248902191785946644480 }, { target := 134, numerator := 377292714610923067838300160 }, { target := 136, numerator := 116668752878488102832701440 }, { target := 141, numerator := 332673119673421331796328448 }, { target := 142, numerator := 19474303756945144326379274240 }, { target := 147, numerator := 19480768655851873742364868608 }, { target := 155, numerator := 326208220766691915810734080 }, { target := 157, numerator := 570947456165353280891781120 }, { target := 158, numerator := 19336378853886128100495851520 }, { target := 160, numerator := 209850817110620876179966525440 }, { target := 168, numerator := 19336349091462369904479436800 }, { target := 175, numerator := 570813525258441398817914880 }, { target := 176, numerator := 7653885508579973310531502080 }, { target := 178, numerator := 281589798334151628398253834240 }, { target := 181, numerator := 281590108658958149883632025600 }, { target := 188, numerator := 7653575183773451825153310720 }, { target := 227, numerator := 5742503881598510372822712320 }, { target := 230, numerator := 18533791831057791878367805440 }, { target := 232, numerator := 5731132076771941723102248960 }, { target := 267, numerator := 284152746908341050393231360 }, { target := 268, numerator := 11403342234733168368581345280 }, { target := 270, numerator := 125521990634289873624508661760 }, { target := 278, numerator := 11403342523374497986290647040 }, { target := 285, numerator := 284095420546463004843048960 }, { target := 286, numerator := 7653893943511045526205235200 }, { target := 288, numerator := 281590108658958149883632025600 }, { target := 291, numerator := 281590418984106663465713664000 }, { target := 298, numerator := 7653583618362531944123596800 }, { target := 302, numerator := 64090436069961151077930762240 }, { target := 305, numerator := 206850326090110581021427630080 }, { target := 307, numerator := 63963518623275090702992670720 }, { target := 573, numerator := 208031642248618740799242240 }, { target := 575, numerator := 7653575183773451825153310720 }, { target := 578, numerator := 7653583618362531944123596800 }, { target := 585, numerator := 208023207659538621828956160 }, { target := 589, numerator := 5742512918763591134431150080 }, { target := 592, numerator := 18533820998288638070866575360 }, { target := 594, numerator := 5731141096040843465447178240 }, { target := 763, numerator := 116882174572030262729768960 }, { target := 766, numerator := 377234380149230682840760320 }, { target := 768, numerator := 116650714340684618142842880 }]

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
    Slot21.Left2.expected,
    Slot21.Left5.expected,
    Slot21.Left12.expected,
    Slot22.Left0.expected,
    Slot22.Left1.expected,
    Slot22.Left3.expected,
    Slot22.Left11.expected,
    Slot22.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 33149380993675418193100800 }, { target := 134, numerator := 112089163775351254249635840 }, { target := 136, numerator := 33125237288959827278561280 }, { target := 176, numerator := 2662274171307099364754718720 }, { target := 178, numerator := 93482082348356220729488834560 }, { target := 181, numerator := 93477096687421681164888309760 }, { target := 188, numerator := 2667076451609563910887178240 }, { target := 227, numerator := 1126628711993866641400135680 }, { target := 230, numerator := 3809509150013603878444990464 }, { target := 232, numerator := 1125808153958358342684377088 }, { target := 286, numerator := 2662274171307099364754718720 }, { target := 288, numerator := 93482082348356220729488834560 }, { target := 291, numerator := 93477096687421681164888309760 }, { target := 298, numerator := 2667076451609563910887178240 }, { target := 302, numerator := 12405194355631275949246382080 }, { target := 305, numerator := 41946118452670616029242589184 }, { target := 307, numerator := 12396159274417571845875171328 }, { target := 573, numerator := 80050942049464856000593920 }, { target := 575, numerator := 2810878322519828261408604160 }, { target := 578, numerator := 2810728410516455161184911360 }, { target := 585, numerator := 80195340048116187020656640 }, { target := 589, numerator := 1126646265280069275987476480 }, { target := 592, numerator := 3809568503555449444372578304 }, { target := 594, numerator := 1125825694459967535073722368 }, { target := 763, numerator := 33144992672124759546265600 }, { target := 766, numerator := 112074325389889862767738880 }, { target := 768, numerator := 33120852163557529181224960 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk3.Parent2
