import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion5Branch2Chunk1Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 5, branch 2,
parent 42; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk1.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected,
    Slot8.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left6.expected,
    Slot11.Left14.expected,
    Slot12.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 71, numerator := 2352078146590556532244480 }, { target := 72, numerator := 55806870775733407717523456 }, { target := 74, numerator := 619223951044306659071492096 }, { target := 82, numerator := 55755505439402219702059008 }, { target := 89, numerator := 2289894070705615041200128 }, { target := 146, numerator := 19739050062902049625866240 }, { target := 147, numerator := 499630157206281230418444288 }, { target := 149, numerator := 5332255381858983743091376128 }, { target := 157, numerator := 500100613742357707084529664 }, { target := 164, numerator := 18695236489315096958337024 }, { target := 200, numerator := 22149153837966444130729984 }, { target := 202, numerator := 774588937627284028927246336 }, { target := 205, numerator := 774590819172661549164658688 }, { target := 212, numerator := 22148656409758101525233664 }, { target := 242, numerator := 204640088029966320114073600 }, { target := 243, numerator := 5179801410265396613029560320 }, { target := 245, numerator := 55280938407096581518964817920 }, { target := 253, numerator := 5184678760829388692872232960 }, { target := 260, numerator := 193818589482416499704463360 }, { target := 296, numerator := 1080186168178822196798423040 }, { target := 298, numerator := 37737475756921696853119991808 }, { target := 301, numerator := 37737568323539142656850395136 }, { target := 308, numerator := 1080163053549436209809326080 }, { target := 640, numerator := 19738128216872198508380160 }, { target := 641, numerator := 499606823658043256856379392 }, { target := 643, numerator := 5332006356782384070317309952 }, { target := 651, numerator := 500077258223027476418789376 }, { target := 658, numerator := 18694363391092037429231616 }, { target := 659, numerator := 1080168872345677335449567232 }, { target := 661, numerator := 37736862617158704339584286720 }, { target := 664, numerator := 37736955182481365250445672448 }, { target := 671, numerator := 1080145758352424795826552832 }, { target := 1017, numerator := 687623975885612127354880 }, { target := 1018, numerator := 17404975116620501620883456 }, { target := 1020, numerator := 185752943248387661455425536 }, { target := 1028, numerator := 17421363807706820240211968 }, { target := 1035, numerator := 651261980892642083340288 }, { target := 1036, numerator := 22146765264676500570898432 }, { target := 1038, numerator := 774513407432266850284601344 }, { target := 1041, numerator := 774515288606097401263947776 }, { target := 1048, numerator := 22146267650694673336369152 }]

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
    Slot12.Left1.expected,
    Slot12.Left3.expected,
    Slot12.Left11.expected,
    Slot12.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected,
    Slot13.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left1.expected,
    Slot16.Left3.expected,
    Slot16.Left11.expected,
    Slot16.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 10773866083946073119784960 }, { target := 30, numerator := 551596200454194532731322368 }, { target := 35, numerator := 551593451847950728431665152 }, { target := 43, numerator := 10767229205454935908417536 }, { target := 71, numerator := 687331326352326058311680 }, { target := 72, numerator := 19739050062902049625866240 }, { target := 74, numerator := 204640088029966320114073600 }, { target := 82, numerator := 19738128216872198508380160 }, { target := 89, numerator := 687623975885612127354880 }, { target := 104, numerator := 368691349816922181992448000 }, { target := 105, numerator := 18876116160602585849816678400 }, { target := 110, numerator := 18876022100834416514931097600 }, { target := 118, numerator := 368464229888903544097996800 }, { target := 146, numerator := 55806870775733407717523456 }, { target := 147, numerator := 1385815701675763706982563840 }, { target := 149, numerator := 15182737355747643403691622400 }, { target := 157, numerator := 1384229297369210387861340160 }, { target := 164, numerator := 55218150045301179368341504 }, { target := 226, numerator := 368692435477166354061066240 }, { target := 227, numerator := 18876171743813014074364526592 }, { target := 232, numerator := 18876077683767873362395660288 }, { target := 240, numerator := 368465314880363171502096384 }, { target := 242, numerator := 619223951044306659071492096 }, { target := 243, numerator := 15335191327341230533753438208 }, { target := 245, numerator := 168190394168216286288538501120 }, { target := 253, numerator := 15317298935397204831263260672 }, { target := 260, numerator := 612574131054316232120467456 }, { target := 624, numerator := 10773866083946073119784960 }, { target := 625, numerator := 551596200454194532731322368 }, { target := 630, numerator := 551593451847950728431665152 }, { target := 638, numerator := 10767229205454935908417536 }, { target := 640, numerator := 55755505439402219702059008 }, { target := 641, numerator := 1384723087453524838089490432 }, { target := 643, numerator := 15169971339444209453818183680 }, { target := 651, numerator := 1383139418149529698841919488 }, { target := 658, numerator := 55167843146080315873689600 }, { target := 1017, numerator := 2289894070705615041200128 }, { target := 1018, numerator := 56508411417995774705795072 }, { target := 1020, numerator := 620639777288345070369505280 }, { target := 1028, numerator := 56440842729465533062709248 }, { target := 1035, numerator := 2264734697876510883184640 }]

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
    Slot17.Left0.expected,
    Slot17.Left2.expected,
    Slot17.Left5.expected,
    Slot17.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 29, numerator := 11375287754020371010945024 }, { target := 30, numerator := 528589967724627664067100672 }, { target := 35, numerator := 528575420497726607017902080 }, { target := 43, numerator := 11379536059221564662480896 }, { target := 104, numerator := 405897587810361846934798336 }, { target := 105, numerator := 18861359596319111003303313408 }, { target := 110, numerator := 18860840516324287824653189120 }, { target := 118, numerator := 406049177543363306186604544 }, { target := 226, numerator := 405898383695495195103592448 }, { target := 227, numerator := 18861396579726128582485868544 }, { target := 232, numerator := 18860877498713491888050012160 }, { target := 240, numerator := 406049973725734229761851392 }, { target := 624, numerator := 11374790325812028405448704 }, { target := 625, numerator := 528566853095241677078003712 }, { target := 630, numerator := 528552306504474067394887680 }, { target := 638, numerator := 11379038445239737427951616 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk1.Parent3
