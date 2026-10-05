import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk1Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 8; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot1.Left4.expected,
    Slot1.Left5.expected,
    Slot1.Left6.expected,
    Slot1.Left7.expected,
    Slot1.Left8.expected,
    Slot1.Left9.expected,
    Slot1.Left10.expected,
    Slot1.Left11.expected,
    Slot1.Left12.expected,
    Slot1.Left13.expected,
    Slot1.Left14.expected,
    Slot1.Left15.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected,
    Slot2.Left7.expected,
    Slot2.Left8.expected,
    Slot2.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 2698465539220376156645621760 }, { target := 134, numerator := 9226236507226459666730975232 }, { target := 136, numerator := 2698464667611718673869307904 }, { target := 227, numerator := 71959081045876697510549913600 }, { target := 230, numerator := 246032973526038924446159339520 }, { target := 232, numerator := 71959057802979164636514877440 }, { target := 253, numerator := 68810871250119591994463354880 }, { target := 256, numerator := 235269030934274721501639868416 }, { target := 258, numerator := 68810849024098826183667351552 }, { target := 263, numerator := 1015727333146183621568102400 }, { target := 265, numerator := 1015268043806393391938273280 }, { target := 302, numerator := 2248721282683646797204684800 }, { target := 305, numerator := 7688530422688716388942479360 }, { target := 307, numerator := 2248720556343098894891089920 }, { target := 328, numerator := 70609848276266509432227102720 }, { target := 331, numerator := 241419855272425694612793851904 }, { target := 333, numerator := 70609825469173305299580223488 }, { target := 338, numerator := 1044748114093217439327191040 }, { target := 340, numerator := 1044275702200861774565081088 }, { target := 342, numerator := 2248721282683646797204684800 }, { target := 345, numerator := 7688530422688716388942479360 }, { target := 347, numerator := 2248720556343098894891089920 }, { target := 352, numerator := 1015727333146183621568102400 }, { target := 354, numerator := 1015268043806393391938273280 }, { target := 443, numerator := 68810871250119591994463354880 }, { target := 446, numerator := 235269030934274721501639868416 }, { target := 448, numerator := 68810849024098826183667351552 }, { target := 469, numerator := 39127750318695454271361515520 }, { target := 472, numerator := 133780429354783665167599140864 }, { target := 474, numerator := 39127737680369920771104964608 }, { target := 479, numerator := 899644209358048350531747840 }, { target := 481, numerator := 899237410228519861431042048 }, { target := 518, numerator := 70609848276266509432227102720 }, { target := 521, numerator := 241419855272425694612793851904 }, { target := 523, numerator := 70609825469173305299580223488 }, { target := 544, numerator := 1102323172771523659989736488960 }, { target := 547, numerator := 3768917613202008773859603382272 }, { target := 549, numerator := 1102322816719387078275612278784 }, { target := 554, numerator := 42109153154146069568437616640 }, { target := 556, numerator := 42090112330373623191498129408 }, { target := 568, numerator := 11463208474078358014840012800 }, { target := 570, numerator := 11458025065815011137589084160 }, { target := 599, numerator := 1044748114093217439327191040 }, { target := 601, numerator := 1044275702200861774565081088 }, { target := 613, numerator := 42109153154146069568437616640 }, { target := 615, numerator := 42090112330373623191498129408 }, { target := 618, numerator := 1015727333146183621568102400 }, { target := 620, numerator := 1015268043806393391938273280 }, { target := 694, numerator := 1015727333146183621568102400 }, { target := 696, numerator := 1015268043806393391938273280 }, { target := 708, numerator := 870623428411014532772659200 }, { target := 710, numerator := 870229751834051478804234240 }, { target := 739, numerator := 1015727333146183621568102400 }, { target := 741, numerator := 1015268043806393391938273280 }, { target := 753, numerator := 11463208474078358014840012800 }, { target := 755, numerator := 11458025065815011137589084160 }, { target := 758, numerator := 870623428411014532772659200 }, { target := 760, numerator := 870229751834051478804234240 }, { target := 773, numerator := 1015727333146183621568102400 }, { target := 775, numerator := 1015268043806393391938273280 }, { target := 778, numerator := 899644209358048350531747840 }, { target := 780, numerator := 899237410228519861431042048 }]

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
    Slot2.Left10.expected,
    Slot2.Left11.expected,
    Slot2.Left12.expected,
    Slot2.Left13.expected,
    Slot2.Left14.expected,
    Slot2.Left15.expected,
    Slot2.Left16.expected,
    Slot2.Left17.expected,
    Slot2.Left18.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot3.Left4.expected,
    Slot3.Left5.expected,
    Slot3.Left6.expected,
    Slot3.Left7.expected,
    Slot3.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 2875830374746539063018258432 }, { target := 82, numerator := 100646893069621601113730973696 }, { target := 85, numerator := 100646942433108742360491098112 }, { target := 92, numerator := 2875805693002968439638196224 }, { target := 115, numerator := 2815917241939319499205378048 }, { target := 117, numerator := 98550082797337817757194911744 }, { target := 120, numerator := 98550131132418976894647533568 }, { target := 127, numerator := 2815893074398739930479067136 }, { target := 176, numerator := 2216785913867123861076574208 }, { target := 178, numerator := 77581980074499984191834292224 }, { target := 181, numerator := 77582018125521322236211888128 }, { target := 188, numerator := 2216766888356454838887776256 }, { target := 211, numerator := 69678973454796352714379886592 }, { target := 213, numerator := 2438590346666040043651440050176 }, { target := 216, numerator := 2438591542702197236776065564672 }, { target := 223, numerator := 69678375436717756152067129344 }, { target := 237, numerator := 2216785913867123861076574208 }, { target := 239, numerator := 77581980074499984191834292224 }, { target := 242, numerator := 77582018125521322236211888128 }, { target := 249, numerator := 2216766888356454838887776256 }, { target := 286, numerator := 2216785913867123861076574208 }, { target := 288, numerator := 77581980074499984191834292224 }, { target := 291, numerator := 77582018125521322236211888128 }, { target := 298, numerator := 2216766888356454838887776256 }, { target := 312, numerator := 2276699046674343424889454592 }, { target := 314, numerator := 79678790346783767548370354176 }, { target := 317, numerator := 79678829426211087702055452672 }, { target := 324, numerator := 2276679506960683348046905344 }, { target := 392, numerator := 2276699046674343424889454592 }, { target := 394, numerator := 79678790346783767548370354176 }, { target := 397, numerator := 79678829426211087702055452672 }, { target := 404, numerator := 2276679506960683348046905344 }, { target := 427, numerator := 38524144395042179531682086912 }, { target := 429, numerator := 1348249005078472698252687835136 }, { target := 432, numerator := 1348249666343519194537412001792 }, { target := 439, numerator := 38523813762518931389320003584 }, { target := 558, numerator := 43175448627526018506329948160 }, { target := 561, numerator := 147619784115623354667695603712 }, { target := 563, numerator := 43175434681787498781908926464 }, { target := 589, numerator := 71959081045876697510549913600 }, { target := 592, numerator := 246032973526038924446159339520 }, { target := 594, numerator := 71959057802979164636514877440 }, { target := 603, numerator := 68810871250119591994463354880 }, { target := 606, numerator := 235269030934274721501639868416 }, { target := 608, numerator := 68810849024098826183667351552 }, { target := 658, numerator := 2248721282683646797204684800 }, { target := 661, numerator := 7688530422688716388942479360 }, { target := 663, numerator := 2248720556343098894891089920 }, { target := 684, numerator := 43175448627526018506329948160 }, { target := 687, numerator := 147619784115623354667695603712 }, { target := 689, numerator := 43175434681787498781908926464 }, { target := 698, numerator := 2248721282683646797204684800 }, { target := 701, numerator := 7688530422688716388942479360 }, { target := 703, numerator := 2248720556343098894891089920 }, { target := 729, numerator := 69260615506656321353904291840 }, { target := 732, numerator := 236806737018812464779428364288 }, { target := 734, numerator := 69260593135367445962645569536 }, { target := 743, numerator := 39127750318695454271361515520 }, { target := 746, numerator := 133780429354783665167599140864 }, { target := 748, numerator := 39127737680369920771104964608 }, { target := 763, numerator := 2698465539220376156645621760 }, { target := 766, numerator := 9226236507226459666730975232 }, { target := 768, numerator := 2698464667611718673869307904 }]

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
    Slot3.Left9.expected,
    Slot3.Left10.expected,
    Slot3.Left11.expected,
    Slot3.Left12.expected,
    Slot3.Left13.expected,
    Slot3.Left14.expected,
    Slot3.Left15.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected,
    Slot4.Left4.expected,
    Slot4.Left5.expected,
    Slot4.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 12959064837317367559094272 }, { target := 27, numerator := 1358734575649169921496055808 }, { target := 29, numerator := 14645800671887418829307904000 }, { target := 37, numerator := 1358735612125602563051487232 }, { target := 44, numerator := 12959064837317367559094272 }, { target := 61, numerator := 317706105689070946610053120 }, { target := 62, numerator := 33310912177205456139903303680 }, { target := 64, numerator := 359058339052723816460451840000 }, { target := 72, numerator := 33310937587595417674810654720 }, { target := 79, numerator := 317706105689070946610053120 }, { target := 96, numerator := 12959064837317367559094272 }, { target := 97, numerator := 1358734575649169921496055808 }, { target := 99, numerator := 14645800671887418829307904000 }, { target := 107, numerator := 1358735612125602563051487232 }, { target := 114, numerator := 12959064837317367559094272 }, { target := 157, numerator := 266287880689392359198162944 }, { target := 158, numerator := 27919804022210362580418953216 }, { target := 160, numerator := 300947581548138251428036608000 }, { target := 168, numerator := 27919825320129317182703140864 }, { target := 175, numerator := 266287880689392359198162944 }, { target := 192, numerator := 261689502843892648128806912 }, { target := 193, numerator := 27437672398592915188920352768 }, { target := 195, numerator := 295750684535533038295056384000 }, { target := 203, numerator := 27437693328729909821620355072 }, { target := 210, numerator := 261689502843892648128806912 }, { target := 267, numerator := 12959064837317367559094272 }, { target := 268, numerator := 1358734575649169921496055808 }, { target := 270, numerator := 14645800671887418829307904000 }, { target := 278, numerator := 1358735612125602563051487232 }, { target := 285, numerator := 12959064837317367559094272 }, { target := 373, numerator := 262107537193483530953293824 }, { target := 374, numerator := 27481502546194501315420225536 }, { target := 376, numerator := 296223129718497148579872768000 }, { target := 384, numerator := 27481523509766219581718790144 }, { target := 391, numerator := 262107537193483530953293824 }, { target := 453, numerator := 2096959648252684733450813440 }, { target := 455, numerator := 73388359529932417478762168320 }, { target := 458, numerator := 73388395524141791304524759040 }, { target := 465, numerator := 2096941651147997820569518080 }, { target := 502, numerator := 69678973454796352714379886592 }, { target := 504, numerator := 2438590346666040043651440050176 }, { target := 507, numerator := 2438591542702197236776065564672 }, { target := 514, numerator := 69678375436717756152067129344 }, { target := 528, numerator := 38524144395042179531682086912 }, { target := 530, numerator := 1348249005078472698252687835136 }, { target := 533, numerator := 1348249666343519194537412001792 }, { target := 540, numerator := 38523813762518931389320003584 }, { target := 573, numerator := 2875830374746539063018258432 }, { target := 575, numerator := 100646893069621601113730973696 }, { target := 578, numerator := 100646942433108742360491098112 }, { target := 585, numerator := 2875805693002968439638196224 }, { target := 642, numerator := 2216785913867123861076574208 }, { target := 644, numerator := 77581980074499984191834292224 }, { target := 647, numerator := 77582018125521322236211888128 }, { target := 654, numerator := 2216766888356454838887776256 }, { target := 668, numerator := 2096959648252684733450813440 }, { target := 670, numerator := 73388359529932417478762168320 }, { target := 673, numerator := 73388395524141791304524759040 }, { target := 680, numerator := 2096941651147997820569518080 }, { target := 713, numerator := 2815917241939319499205378048 }, { target := 715, numerator := 98550082797337817757194911744 }, { target := 718, numerator := 98550131132418976894647533568 }, { target := 725, numerator := 2815893074398739930479067136 }]

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
    Slot4.Left7.expected,
    Slot4.Left8.expected,
    Slot4.Left9.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left6.expected,
    Slot8.Left14.expected,
    Slot9.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 116998618402690906980352000 }, { target := 11, numerator := 9796193102437268325610291200 }, { target := 16, numerator := 9796196647670894991664742400 }, { target := 24, numerator := 116995073169064240925900800 }, { target := 45, numerator := 116199603447745700786339840 }, { target := 46, numerator := 9729292271493794298020757504 }, { target := 51, numerator := 9729295792516069367331422208 }, { target := 59, numerator := 116196082425470631475675136 }, { target := 131, numerator := 12065336227847204279156736 }, { target := 132, numerator := 295795339779479846843842560 }, { target := 133, numerator := 12065336227847204279156736 }, { target := 134, numerator := 247923199262537713736220672 }, { target := 135, numerator := 243641950923624189637165056 }, { target := 136, numerator := 12065336227847204279156736 }, { target := 137, numerator := 244031155318070873646170112 }, { target := 138, numerator := 218732869679036413060841472 }, { target := 139, numerator := 295795339779479846843842560 }, { target := 140, numerator := 12065336227847204279156736 }, { target := 141, numerator := 116998618402690906980352000 }, { target := 142, numerator := 9796193102437268325610291200 }, { target := 147, numerator := 9796196647670894991664742400 }, { target := 155, numerator := 116995073169064240925900800 }, { target := 263, numerator := 116998618402690906980352000 }, { target := 264, numerator := 116199603447745700786339840 }, { target := 265, numerator := 116998618402690906980352000 }, { target := 266, numerator := 117341053383381709634928640 }, { target := 338, numerator := 9796193102437268325610291200 }, { target := 339, numerator := 9729292271493794298020757504 }, { target := 340, numerator := 9796193102437268325610291200 }, { target := 341, numerator := 9824864887127328623148662784 }, { target := 357, numerator := 117341053383381709634928640 }, { target := 358, numerator := 9824864887127328623148662784 }, { target := 363, numerator := 9824868442737248830664736768 }, { target := 371, numerator := 117337497773461502118854656 }, { target := 408, numerator := 234935304470076147361644544 }, { target := 409, numerator := 24632542952091403092928495616 }, { target := 411, numerator := 265514192825829980066807808000 }, { target := 419, numerator := 24632561742406085175320510464 }, { target := 426, numerator := 234935304470076147361644544 }, { target := 483, numerator := 317706105689070946610053120 }, { target := 484, numerator := 33310912177205456139903303680 }, { target := 486, numerator := 359058339052723816460451840000 }, { target := 494, numerator := 33310937587595417674810654720 }, { target := 501, numerator := 317706105689070946610053120 }, { target := 599, numerator := 9796196647670894991664742400 }, { target := 600, numerator := 9729295792516069367331422208 }, { target := 601, numerator := 9796196647670894991664742400 }, { target := 602, numerator := 9824868442737248830664736768 }, { target := 623, numerator := 12959064837317367559094272 }, { target := 624, numerator := 1358734575649169921496055808 }, { target := 626, numerator := 14645800671887418829307904000 }, { target := 634, numerator := 1358735612125602563051487232 }, { target := 641, numerator := 12959064837317367559094272 }, { target := 773, numerator := 116995073169064240925900800 }, { target := 774, numerator := 116196082425470631475675136 }, { target := 775, numerator := 116995073169064240925900800 }, { target := 776, numerator := 117337497773461502118854656 }]

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

namespace RouteChunk4

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 2953206976757656705969422336 }, { target := 81, numerator := 2891681831408538857928392704 }, { target := 82, numerator := 2276430377917360377518096384 }, { target := 83, numerator := 71553744041024057271717462016 }, { target := 84, numerator := 2276430377917360377518096384 }, { target := 85, numerator := 2276430377917360377518096384 }, { target := 86, numerator := 2337955523266478225559126016 }, { target := 87, numerator := 2337955523266478225559126016 }, { target := 88, numerator := 39560668459482776290382053376 }, { target := 89, numerator := 2153380087219124681436037120 }, { target := 90, numerator := 71553744041024057271717462016 }, { target := 91, numerator := 39560668459482776290382053376 }, { target := 92, numerator := 2953206976757656705969422336 }, { target := 93, numerator := 2276430377917360377518096384 }, { target := 94, numerator := 2153380087219124681436037120 }, { target := 95, numerator := 2891681831408538857928392704 }, { target := 227, numerator := 1265028742845778892427362304 }, { target := 228, numerator := 31013607889122321233703075840 }, { target := 229, numerator := 1265028742845778892427362304 }, { target := 230, numerator := 25994300296540682402459025408 }, { target := 231, numerator := 25545419129724438279339638784 }, { target := 232, numerator := 1265028742845778892427362304 }, { target := 233, numerator := 25586226508525915017805037568 }, { target := 234, numerator := 22933746886429927017554116608 }, { target := 235, numerator := 31013607889122321233703075840 }, { target := 236, numerator := 1265028742845778892427362304 }, { target := 302, numerator := 13635745453136562358321152000 }, { target := 303, numerator := 334295694980122173945937920000 }, { target := 304, numerator := 13635745453136562358321152000 }, { target := 305, numerator := 280192575924128716846792704000 }, { target := 306, numerator := 275354085602048001171259392000 }, { target := 307, numerator := 13635745453136562358321152000 }, { target := 308, numerator := 275793948358600793505398784000 }, { target := 309, numerator := 247202869182669291786338304000 }, { target := 310, numerator := 334295694980122173945937920000 }, { target := 311, numerator := 13635745453136562358321152000 }, { target := 589, numerator := 1265029707841078248358281216 }, { target := 590, numerator := 31013631547071595766203023360 }, { target := 591, numerator := 1265029707841078248358281216 }, { target := 592, numerator := 25994320125637640135620165632 }, { target := 593, numerator := 25545438616403709144267227136 }, { target := 594, numerator := 1265029707841078248358281216 }, { target := 595, numerator := 25586246026334066507117494272 }, { target := 596, numerator := 22933764380860837921850130432 }, { target := 597, numerator := 31013631547071595766203023360 }, { target := 598, numerator := 1265029707841078248358281216 }, { target := 763, numerator := 12065336227847204279156736 }, { target := 764, numerator := 295795339779479846843842560 }, { target := 765, numerator := 12065336227847204279156736 }, { target := 766, numerator := 247923199262537713736220672 }, { target := 767, numerator := 243641950923624189637165056 }, { target := 768, numerator := 12065336227847204279156736 }, { target := 769, numerator := 244031155318070873646170112 }, { target := 770, numerator := 218732869679036413060841472 }, { target := 771, numerator := 295795339779479846843842560 }, { target := 772, numerator := 12065336227847204279156736 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk4

namespace RouteChunk5

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 176, numerator := 103354881223961195762530910208 }, { target := 177, numerator := 101201654531795337517478182912 }, { target := 178, numerator := 79669387610136755066950909952 }, { target := 179, numerator := 2504202642988893138996321845248 }, { target := 180, numerator := 79669387610136755066950909952 }, { target := 181, numerator := 79669387610136755066950909952 }, { target := 182, numerator := 81822614302302613312003637248 }, { target := 183, numerator := 81822614302302613312003637248 }, { target := 184, numerator := 1384524763062646851568903651328 }, { target := 185, numerator := 75362934225805038576845455360 }, { target := 186, numerator := 2504202642988893138996321845248 }, { target := 187, numerator := 1384524763062646851568903651328 }, { target := 188, numerator := 103354881223961195762530910208 }, { target := 189, numerator := 79669387610136755066950909952 }, { target := 190, numerator := 75362934225805038576845455360 }, { target := 191, numerator := 101201654531795337517478182912 }, { target := 286, numerator := 103354931915613910316378750976 }, { target := 287, numerator := 101201704167371953851454193664 }, { target := 288, numerator := 79669426684952389202208620544 }, { target := 289, numerator := 2504203871205395368707260153856 }, { target := 290, numerator := 79669426684952389202208620544 }, { target := 291, numerator := 79669426684952389202208620544 }, { target := 292, numerator := 81822654433194345667133177856 }, { target := 293, numerator := 81822654433194345667133177856 }, { target := 294, numerator := 1384525442119578006946490351616 }, { target := 295, numerator := 75362971188468476272359505920 }, { target := 296, numerator := 2504203871205395368707260153856 }, { target := 297, numerator := 1384525442119578006946490351616 }, { target := 298, numerator := 103354931915613910316378750976 }, { target := 299, numerator := 79669426684952389202208620544 }, { target := 300, numerator := 75362971188468476272359505920 }, { target := 301, numerator := 101201704167371953851454193664 }, { target := 573, numerator := 2953181630931299429045501952 }, { target := 574, numerator := 2891657013620230690940387328 }, { target := 575, numerator := 2276410840509543309889241088 }, { target := 576, numerator := 71553129932772942416248307712 }, { target := 577, numerator := 2276410840509543309889241088 }, { target := 578, numerator := 2276410840509543309889241088 }, { target := 579, numerator := 2337935457820612047994355712 }, { target := 580, numerator := 2337935457820612047994355712 }, { target := 581, numerator := 39560328931017198601588703232 }, { target := 582, numerator := 2153361605887405833679011840 }, { target := 583, numerator := 71553129932772942416248307712 }, { target := 584, numerator := 39560328931017198601588703232 }, { target := 585, numerator := 2953181630931299429045501952 }, { target := 586, numerator := 2276410840509543309889241088 }, { target := 587, numerator := 2153361605887405833679011840 }, { target := 588, numerator := 2891657013620230690940387328 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk5

namespace RouteChunk6

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 2698465539220376156645621760 }, { target := 27, numerator := 71959081045876697510549913600 }, { target := 28, numerator := 68810871250119591994463354880 }, { target := 29, numerator := 2248721282683646797204684800 }, { target := 30, numerator := 70609848276266509432227102720 }, { target := 31, numerator := 2248721282683646797204684800 }, { target := 32, numerator := 68810871250119591994463354880 }, { target := 33, numerator := 39127750318695454271361515520 }, { target := 34, numerator := 70609848276266509432227102720 }, { target := 35, numerator := 1102323172771523659989736488960 }, { target := 36, numerator := 43175448627526018506329948160 }, { target := 37, numerator := 71959081045876697510549913600 }, { target := 38, numerator := 68810871250119591994463354880 }, { target := 39, numerator := 2248721282683646797204684800 }, { target := 40, numerator := 43175448627526018506329948160 }, { target := 41, numerator := 2248721282683646797204684800 }, { target := 42, numerator := 69260615506656321353904291840 }, { target := 43, numerator := 39127750318695454271361515520 }, { target := 44, numerator := 2698465539220376156645621760 }, { target := 157, numerator := 9226236507226459666730975232 }, { target := 158, numerator := 246032973526038924446159339520 }, { target := 159, numerator := 235269030934274721501639868416 }, { target := 160, numerator := 7688530422688716388942479360 }, { target := 161, numerator := 241419855272425694612793851904 }, { target := 162, numerator := 7688530422688716388942479360 }, { target := 163, numerator := 235269030934274721501639868416 }, { target := 164, numerator := 133780429354783665167599140864 }, { target := 165, numerator := 241419855272425694612793851904 }, { target := 166, numerator := 3768917613202008773859603382272 }, { target := 167, numerator := 147619784115623354667695603712 }, { target := 168, numerator := 246032973526038924446159339520 }, { target := 169, numerator := 235269030934274721501639868416 }, { target := 170, numerator := 7688530422688716388942479360 }, { target := 171, numerator := 147619784115623354667695603712 }, { target := 172, numerator := 7688530422688716388942479360 }, { target := 173, numerator := 236806737018812464779428364288 }, { target := 174, numerator := 133780429354783665167599140864 }, { target := 175, numerator := 9226236507226459666730975232 }, { target := 267, numerator := 2698464667611718673869307904 }, { target := 268, numerator := 71959057802979164636514877440 }, { target := 269, numerator := 68810849024098826183667351552 }, { target := 270, numerator := 2248720556343098894891089920 }, { target := 271, numerator := 70609825469173305299580223488 }, { target := 272, numerator := 2248720556343098894891089920 }, { target := 273, numerator := 68810849024098826183667351552 }, { target := 274, numerator := 39127737680369920771104964608 }, { target := 275, numerator := 70609825469173305299580223488 }, { target := 276, numerator := 1102322816719387078275612278784 }, { target := 277, numerator := 43175434681787498781908926464 }, { target := 278, numerator := 71959057802979164636514877440 }, { target := 279, numerator := 68810849024098826183667351552 }, { target := 280, numerator := 2248720556343098894891089920 }, { target := 281, numerator := 43175434681787498781908926464 }, { target := 282, numerator := 2248720556343098894891089920 }, { target := 283, numerator := 69260593135367445962645569536 }, { target := 284, numerator := 39127737680369920771104964608 }, { target := 285, numerator := 2698464667611718673869307904 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk6

namespace RouteChunk7

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot12.Left0.expected,
    Slot12.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 1015727333146183621568102400 }, { target := 11, numerator := 1044748114093217439327191040 }, { target := 12, numerator := 1015727333146183621568102400 }, { target := 13, numerator := 899644209358048350531747840 }, { target := 14, numerator := 42109153154146069568437616640 }, { target := 15, numerator := 11463208474078358014840012800 }, { target := 16, numerator := 1044748114093217439327191040 }, { target := 17, numerator := 42109153154146069568437616640 }, { target := 18, numerator := 1015727333146183621568102400 }, { target := 19, numerator := 1015727333146183621568102400 }, { target := 20, numerator := 870623428411014532772659200 }, { target := 21, numerator := 1015727333146183621568102400 }, { target := 22, numerator := 11463208474078358014840012800 }, { target := 23, numerator := 870623428411014532772659200 }, { target := 24, numerator := 1015727333146183621568102400 }, { target := 25, numerator := 899644209358048350531747840 }, { target := 141, numerator := 1015268043806393391938273280 }, { target := 142, numerator := 1044275702200861774565081088 }, { target := 143, numerator := 1015268043806393391938273280 }, { target := 144, numerator := 899237410228519861431042048 }, { target := 145, numerator := 42090112330373623191498129408 }, { target := 146, numerator := 11458025065815011137589084160 }, { target := 147, numerator := 1044275702200861774565081088 }, { target := 148, numerator := 42090112330373623191498129408 }, { target := 149, numerator := 1015268043806393391938273280 }, { target := 150, numerator := 1015268043806393391938273280 }, { target := 151, numerator := 870229751834051478804234240 }, { target := 152, numerator := 1015268043806393391938273280 }, { target := 153, numerator := 11458025065815011137589084160 }, { target := 154, numerator := 870229751834051478804234240 }, { target := 155, numerator := 1015268043806393391938273280 }, { target := 156, numerator := 899237410228519861431042048 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk7

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent3
