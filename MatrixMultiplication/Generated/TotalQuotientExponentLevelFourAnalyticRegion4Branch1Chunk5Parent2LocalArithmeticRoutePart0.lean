import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion4Branch1Chunk5Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 4, branch 1,
parent 55; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk5.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot5.Left5.expected,
    Slot5.Left12.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left3.expected,
    Slot6.Left11.expected,
    Slot6.Left18.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected,
    Slot10.Left0.expected,
    Slot10.Left3.expected,
    Slot10.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 102400117530109785208258560 }, { target := 27, numerator := 3480213176317803485542219776 }, { target := 29, numerator := 38320273921339794811577696256 }, { target := 37, numerator := 3480267399308288055192846336 }, { target := 44, numerator := 102386561782488642795601920 }, { target := 80, numerator := 256145814916964168906047488 }, { target := 82, numerator := 8702709968814287482823639040 }, { target := 85, numerator := 8702918014763053483837882368 }, { target := 92, numerator := 255937725238808736077709312 }, { target := 131, numerator := 99441444711153846913597440 }, { target := 134, numerator := 344643244904103629304102912 }, { target := 136, numerator := 99464414929521557523922944 }, { target := 157, numerator := 330493892718207203561963520 }, { target := 158, numerator := 11232303515591815895546068992 }, { target := 160, numerator := 123677753539371444768344113152 }, { target := 168, numerator := 11232478518976893050538688512 }, { target := 175, numerator := 330450141871937914813808640 }, { target := 176, numerator := 9379034025274770410673537024 }, { target := 178, numerator := 318381841016700991904751288320 }, { target := 181, numerator := 318389146262991698516418494464 }, { target := 188, numerator := 9371724100410020755958398976 }, { target := 227, numerator := 3367801061111593502496522240 }, { target := 230, numerator := 11672093957046002607772925952 }, { target := 232, numerator := 3368578997574779900918759424 }, { target := 263, numerator := 332673436936252481351974912 }, { target := 265, numerator := 332674943934700441741295616 }, { target := 267, numerator := 102197335925642510393671680 }, { target := 268, numerator := 3473321355987867206500220928 }, { target := 270, numerator := 38244388787447151893170618368 }, { target := 278, numerator := 3473375471601277660569796608 }, { target := 285, numerator := 102183807022289896876277760 }, { target := 286, numerator := 935632306354699003477622784 }, { target := 288, numerator := 37579470184649537972842004480 }, { target := 291, numerator := 37586775041331026070920495104 }, { target := 298, numerator := 928391728738918531655008256 }, { target := 302, numerator := 36549542697765653464775393280 }, { target := 305, numerator := 126673069078069704912109830144 }, { target := 307, numerator := 36557985364497279012179017728 }, { target := 338, numerator := 19474322329148244655404482560 }, { target := 340, numerator := 19474410547112971218274222080 }, { target := 573, numerator := 26695340142924502627516416 }, { target := 575, numerator := 1072212590519289470538219520 }, { target := 578, numerator := 1072421011746819970848260096 }, { target := 585, numerator := 26488752917396156311404544 }, { target := 589, numerator := 3367795877414942153480601600 }, { target := 592, numerator := 11672075991437802638860615680 }, { target := 594, numerator := 3368573812680734000975708160 }, { target := 599, numerator := 19480787234220401961260285952 }, { target := 601, numerator := 19480875481470911001013518336 }, { target := 763, numerator := 99418118076222776341954560 }, { target := 766, numerator := 344562399667203769198706688 }, { target := 768, numerator := 99441082906315007780192256 }, { target := 773, numerator := 326208531864095175496171520 }, { target := 775, numerator := 326210009576760659001999360 }]

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
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left3.expected,
    Slot12.Left11.expected,
    Slot12.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left6.expected,
    Slot13.Left14.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot17.Left0.expected,
    Slot17.Left3.expected,
    Slot17.Left5.expected,
    Slot18.Left0.expected,
    Slot18.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 377969985105406705857986560 }, { target := 11, numerator := 19429042308965387324180398080 }, { target := 16, numerator := 19433559267044716161909391360 }, { target := 24, numerator := 373637199911696085244968960 }, { target := 26, numerator := 203282731634832291825451008 }, { target := 27, numerator := 9985880153699876530418614272 }, { target := 29, numerator := 111449539571724682057696149504 }, { target := 37, numerator := 9985895868804173606858784768 }, { target := 44, numerator := 203251301426238138945110016 }, { target := 80, numerator := 229498541827407630450032640 }, { target := 82, numerator := 8443351816370632112650321920 }, { target := 85, numerator := 8443361121329598341893324800 }, { target := 92, numerator := 229489236868441401207029760 }, { target := 131, numerator := 203282731634832291825451008 }, { target := 134, numerator := 692985298543460226598699008 }, { target := 136, numerator := 203283059326592803487612928 }, { target := 141, numerator := 377967552006434621369614336 }, { target := 142, numerator := 19428917238762108229200642048 }, { target := 147, numerator := 19433434167764509022765449216 }, { target := 155, numerator := 373634794704079443015499776 }, { target := 157, numerator := 692985298543460226598699008 }, { target := 158, numerator := 34041593616332419984389046272 }, { target := 160, numerator := 379928446609918708287226773504 }, { target := 168, numerator := 34041647188695184737218592768 }, { target := 175, numerator := 692878153817930720939606016 }, { target := 176, numerator := 7632427981146820216073748480 }, { target := 178, numerator := 280800366506895027538954813440 }, { target := 181, numerator := 280800675961711654132619673600 }, { target := 188, numerator := 7632118526330193622408888320 }, { target := 227, numerator := 9985880153699876530418614272 }, { target := 230, numerator := 34041593616332419984389046272 }, { target := 232, numerator := 9985896250938542638919319552 }, { target := 263, numerator := 377969985105406705857986560 }, { target := 265, numerator := 377967552006434621369614336 }, { target := 267, numerator := 203283059326592803487612928 }, { target := 268, numerator := 9985896250938542638919319552 }, { target := 270, numerator := 111449719228380890699308990464 }, { target := 278, numerator := 9985911966068172463263449088 }, { target := 285, numerator := 203251629067333154799353856 }, { target := 286, numerator := 8443361121329598341893324800 }, { target := 288, numerator := 280800675961711654132619673600 }, { target := 291, numerator := 280800675961711654132619673600 }, { target := 298, numerator := 8443292160185484212541849600 }, { target := 302, numerator := 111449539571724682057696149504 }, { target := 305, numerator := 379928446609918708287226773504 }, { target := 307, numerator := 111449719228380890699308990464 }, { target := 338, numerator := 19429042308965387324180398080 }, { target := 340, numerator := 19428917238762108229200642048 }, { target := 573, numerator := 229489236868441401207029760 }, { target := 575, numerator := 7632118526330193622408888320 }, { target := 578, numerator := 7632118526330193622408888320 }, { target := 585, numerator := 229487362515312485880299520 }, { target := 589, numerator := 9985895868804173606858784768 }, { target := 592, numerator := 34041647188695184737218592768 }, { target := 594, numerator := 9985911966068172463263449088 }, { target := 599, numerator := 19433559267044716161909391360 }, { target := 601, numerator := 19433434167764509022765449216 }, { target := 763, numerator := 203251301426238138945110016 }, { target := 766, numerator := 692878153817930720939606016 }, { target := 768, numerator := 203251629067333154799353856 }, { target := 773, numerator := 373637199911696085244968960 }, { target := 775, numerator := 373634794704079443015499776 }]

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
    Slot18.Left5.expected,
    Slot18.Left12.expected,
    Slot19.Left0.expected,
    Slot19.Left1.expected,
    Slot19.Left3.expected,
    Slot19.Left11.expected,
    Slot19.Left18.expected,
    Slot22.Left0.expected,
    Slot22.Left2.expected,
    Slot23.Left0.expected,
    Slot23.Left3.expected,
    Slot23.Left5.expected,
    Slot24.Left0.expected,
    Slot24.Left2.expected,
    Slot24.Left5.expected,
    Slot24.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 332673436936252481351974912 }, { target := 11, numerator := 19474322329148244655404482560 }, { target := 16, numerator := 19480787234220401961260285952 }, { target := 24, numerator := 326208531864095175496171520 }, { target := 26, numerator := 99441444711153846913597440 }, { target := 27, numerator := 3367801061111593502496522240 }, { target := 29, numerator := 36549542697765653464775393280 }, { target := 37, numerator := 3367795877414942153480601600 }, { target := 44, numerator := 99418118076222776341954560 }, { target := 80, numerator := 26647273089556538456014848 }, { target := 82, numerator := 935682208904138298023215104 }, { target := 85, numerator := 935632306354699003477622784 }, { target := 92, numerator := 26695340142924502627516416 }, { target := 131, numerator := 102400117530109785208258560 }, { target := 134, numerator := 330493892718207203561963520 }, { target := 136, numerator := 102197335925642510393671680 }, { target := 141, numerator := 332674943934700441741295616 }, { target := 142, numerator := 19474410547112971218274222080 }, { target := 147, numerator := 19480875481470911001013518336 }, { target := 155, numerator := 326210009576760659001999360 }, { target := 157, numerator := 344643244904103629304102912 }, { target := 158, numerator := 11672093957046002607772925952 }, { target := 160, numerator := 126673069078069704912109830144 }, { target := 168, numerator := 11672075991437802638860615680 }, { target := 175, numerator := 344562399667203769198706688 }, { target := 176, numerator := 1070281987667467266749890560 }, { target := 178, numerator := 37581474509805964365796474880 }, { target := 181, numerator := 37579470184649537972842004480 }, { target := 188, numerator := 1072212590519289470538219520 }, { target := 227, numerator := 3480213176317803485542219776 }, { target := 230, numerator := 11232303515591815895546068992 }, { target := 232, numerator := 3473321355987867206500220928 }, { target := 267, numerator := 99464414929521557523922944 }, { target := 268, numerator := 3368578997574779900918759424 }, { target := 270, numerator := 36557985364497279012179017728 }, { target := 278, numerator := 3368573812680734000975708160 }, { target := 285, numerator := 99441082906315007780192256 }, { target := 286, numerator := 8702918014763053483837882368 }, { target := 288, numerator := 318389146262991698516418494464 }, { target := 291, numerator := 318387451003042680203540168704 }, { target := 298, numerator := 8704539538077013593257148416 }, { target := 302, numerator := 38320273921339794811577696256 }, { target := 305, numerator := 123677753539371444768344113152 }, { target := 307, numerator := 38244388787447151893170618368 }, { target := 573, numerator := 255937725238808736077709312 }, { target := 575, numerator := 9371724100410020755958398976 }, { target := 578, numerator := 9371683888924402744196857856 }, { target := 585, numerator := 255976115432708642191704064 }, { target := 589, numerator := 3480267399308288055192846336 }, { target := 592, numerator := 11232478518976893050538688512 }, { target := 594, numerator := 3473375471601277660569796608 }, { target := 763, numerator := 102386561782488642795601920 }, { target := 766, numerator := 330450141871937914813808640 }, { target := 768, numerator := 102183807022289896876277760 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk5.Parent2
