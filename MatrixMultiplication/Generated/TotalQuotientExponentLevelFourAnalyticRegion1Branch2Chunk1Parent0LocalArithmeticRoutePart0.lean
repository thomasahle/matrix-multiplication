import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk1Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 5; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent0

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
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected,
    Slot2.Left7.expected,
    Slot2.Left8.expected,
    Slot2.Left9.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 121, numerator := 119067714745541107940065280 }, { target := 122, numerator := 12484035144451772582377553920 }, { target := 124, numerator := 134565421078743136295976960000 }, { target := 132, numerator := 12484044667583400634933575680 }, { target := 139, numerator := 119067714745541107940065280 }, { target := 196, numerator := 122469649452556568166924288 }, { target := 197, numerator := 12840721862864680370445484032 }, { target := 199, numerator := 138410147395278654475862016000 }, { target := 207, numerator := 12840731658085783510217392128 }, { target := 214, numerator := 122469649452556568166924288 }, { target := 250, numerator := 194784848812709344234700800 }, { target := 252, numerator := 6816984069084049029097062400 }, { target := 255, numerator := 6816987412556412388953292800 }, { target := 262, numerator := 194783177076527664306585600 }, { target := 466, numerator := 3903488370206695258463404032 }, { target := 468, numerator := 136612360744444342543105130496 }, { target := 471, numerator := 136612427747630504274623987712 }, { target := 478, numerator := 3903454868613614392703975424 }, { target := 562, numerator := 6552562314059542340055334912 }, { target := 564, numerator := 229323344083987409338825179136 }, { target := 567, numerator := 229323456558397712764388769792 }, { target := 574, numerator := 6552506076854390627273539584 }, { target := 597, numerator := 6287654919674257631896141824 }, { target := 599, numerator := 220052245750033102659253174272 }, { target := 602, numerator := 220052353677320991915412291584 }, { target := 609, numerator := 6287600956030313003816583168 }, { target := 613, numerator := 3819256781700796941284147200 }, { target := 616, numerator := 13058297702026867517727703040 }, { target := 618, numerator := 3819255548074787011957882880 }, { target := 733, numerator := 194784848812709344234700800 }, { target := 735, numerator := 6816984069084049029097062400 }, { target := 738, numerator := 6816987412556412388953292800 }, { target := 745, numerator := 194783177076527664306585600 }, { target := 829, numerator := 6287654919674257631896141824 }, { target := 831, numerator := 220052245750033102659253174272 }, { target := 834, numerator := 220052353677320991915412291584 }, { target := 841, numerator := 6287600956030313003816583168 }, { target := 864, numerator := 4199561340402013461700149248 }, { target := 866, numerator := 146974176529452097067332665344 }, { target := 869, numerator := 146974248614716251105832992768 }, { target := 876, numerator := 4199525297769936442449985536 }, { target := 880, numerator := 3490872086451756456612986880 }, { target := 883, numerator := 11935528179983435918072610816 }, { target := 885, numerator := 3490870958894524951116644352 }, { target := 925, numerator := 202576242765217718004088832 }, { target := 927, numerator := 7089663431847410990260944896 }, { target := 930, numerator := 7089666909058668884511424512 }, { target := 937, numerator := 202574504159588770878849024 }, { target := 960, numerator := 3903488370206695258463404032 }, { target := 962, numerator := 136612360744444342543105130496 }, { target := 965, numerator := 136612427747630504274623987712 }, { target := 972, numerator := 3903454868613614392703975424 }, { target := 976, numerator := 3819256781700796941284147200 }, { target := 979, numerator := 13058297702026867517727703040 }, { target := 981, numerator := 3819255548074787011957882880 }, { target := 986, numerator := 186993454860200970465312768 }, { target := 988, numerator := 6544304706320687067933179904 }, { target := 991, numerator := 6544307916054155893395161088 }, { target := 998, numerator := 186991849993466557734322176 }, { target := 1002, numerator := 3490872086451756456612986880 }, { target := 1005, numerator := 11935528179983435918072610816 }, { target := 1007, numerator := 3490870958894524951116644352 }]

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
    Slot3.Left13.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 231, numerator := 119067714745541107940065280 }, { target := 232, numerator := 12484035144451772582377553920 }, { target := 234, numerator := 134565421078743136295976960000 }, { target := 242, numerator := 12484044667583400634933575680 }, { target := 249, numerator := 119067714745541107940065280 }, { target := 337, numerator := 105459975917479267032629248 }, { target := 338, numerator := 11057288270800141430105833472 }, { target := 340, numerator := 119186515812601063576436736000 }, { target := 348, numerator := 11057296705573869133798309888 }, { target := 355, numerator := 105459975917479267032629248 }, { target := 412, numerator := 4936207259879432789172420608 }, { target := 413, numerator := 517552428417129200486566592512 }, { target := 415, numerator := 5578697885293036879013216256000 }, { target := 423, numerator := 517552823218957552036817666048 }, { target := 430, numerator := 4936207259879432789172420608 }, { target := 447, numerator := 1343764209271106789609308160 }, { target := 448, numerator := 140891253773098576286832394240 }, { target := 450, numerator := 1518666895031529681054597120000 }, { target := 458, numerator := 140891361248441235737107496960 }, { target := 465, numerator := 1343764209271106789609308160 }, { target := 508, numerator := 122469649452556568166924288 }, { target := 509, numerator := 12840721862864680370445484032 }, { target := 511, numerator := 138410147395278654475862016000 }, { target := 519, numerator := 12840731658085783510217392128 }, { target := 526, numerator := 122469649452556568166924288 }, { target := 543, numerator := 4936207259879432789172420608 }, { target := 544, numerator := 517552428417129200486566592512 }, { target := 546, numerator := 5578697885293036879013216256000 }, { target := 554, numerator := 517552823218957552036817666048 }, { target := 561, numerator := 4936207259879432789172420608 }, { target := 578, numerator := 119067714745541107940065280 }, { target := 579, numerator := 12484035144451772582377553920 }, { target := 581, numerator := 134565421078743136295976960000 }, { target := 589, numerator := 12484044667583400634933575680 }, { target := 596, numerator := 119067714745541107940065280 }, { target := 679, numerator := 119067714745541107940065280 }, { target := 680, numerator := 12484035144451772582377553920 }, { target := 682, numerator := 134565421078743136295976960000 }, { target := 690, numerator := 12484044667583400634933575680 }, { target := 697, numerator := 119067714745541107940065280 }, { target := 714, numerator := 102058041210463806805770240 }, { target := 715, numerator := 10700601552387233642037903360 }, { target := 717, numerator := 115341789496065545396551680000 }, { target := 725, numerator := 10700609715071486258514493440 }, { target := 732, numerator := 102058041210463806805770240 }, { target := 775, numerator := 119067714745541107940065280 }, { target := 776, numerator := 12484035144451772582377553920 }, { target := 778, numerator := 134565421078743136295976960000 }, { target := 786, numerator := 12484044667583400634933575680 }, { target := 793, numerator := 119067714745541107940065280 }, { target := 810, numerator := 1343764209271106789609308160 }, { target := 811, numerator := 140891253773098576286832394240 }, { target := 813, numerator := 1518666895031529681054597120000 }, { target := 821, numerator := 140891361248441235737107496960 }, { target := 828, numerator := 1343764209271106789609308160 }, { target := 845, numerator := 102058041210463806805770240 }, { target := 846, numerator := 10700601552387233642037903360 }, { target := 848, numerator := 115341789496065545396551680000 }, { target := 856, numerator := 10700609715071486258514493440 }, { target := 863, numerator := 102058041210463806805770240 }]

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
    Slot3.Left14.expected,
    Slot3.Left15.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected,
    Slot4.Left4.expected,
    Slot4.Left5.expected,
    Slot4.Left6.expected,
    Slot4.Left7.expected,
    Slot4.Left8.expected,
    Slot4.Left9.expected,
    Slot4.Left10.expected,
    Slot4.Left11.expected,
    Slot4.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 84239005249937453025853440 }, { target := 35, numerator := 7053259033754833194439409664 }, { target := 40, numerator := 7053261586323044393998614528 }, { target := 48, numerator := 84236452681726253466648576 }, { target := 79, numerator := 2246373473331665414022758400 }, { target := 80, numerator := 188086907566795551851717591040 }, { target := 85, numerator := 188086975635281183839963054080 }, { target := 93, numerator := 2246305404846033425777295360 }, { target := 105, numerator := 2148094633873405052159262720 }, { target := 106, numerator := 179858105360748246458204946432 }, { target := 111, numerator := 179858170451237632046964670464 }, { target := 119, numerator := 2148029543384019463399538688 }, { target := 154, numerator := 70199171041614544188211200 }, { target := 155, numerator := 5877715861462360995366174720 }, { target := 160, numerator := 5877717988602536994998845440 }, { target := 168, numerator := 70197043901438544555540480 }, { target := 180, numerator := 2204253970706696687509831680 }, { target := 181, numerator := 184560278049918135254497886208 }, { target := 186, numerator := 184560344842119661642963746816 }, { target := 194, numerator := 2204187178505170299043971072 }, { target := 215, numerator := 70199171041614544188211200 }, { target := 216, numerator := 5877715861462360995366174720 }, { target := 221, numerator := 5877717988602536994998845440 }, { target := 229, numerator := 70197043901438544555540480 }, { target := 295, numerator := 2148094633873405052159262720 }, { target := 296, numerator := 179858105360748246458204946432 }, { target := 301, numerator := 179858170451237632046964670464 }, { target := 309, numerator := 2148029543384019463399538688 }, { target := 321, numerator := 1221465576124093068874874880 }, { target := 322, numerator := 102272255989445081319371440128 }, { target := 327, numerator := 102272293001684143712979910656 }, { target := 335, numerator := 1221428563885030675266404352 }, { target := 370, numerator := 2204253970706696687509831680 }, { target := 371, numerator := 184560278049918135254497886208 }, { target := 376, numerator := 184560344842119661642963746816 }, { target := 384, numerator := 2204187178505170299043971072 }, { target := 396, numerator := 34411633644599449561061130240 }, { target := 397, numerator := 2881256315288849359928498847744 }, { target := 402, numerator := 2881257358012963634948434034688 }, { target := 410, numerator := 34410590920485174541125943296 }, { target := 431, numerator := 1347824083998999248413655040 }, { target := 432, numerator := 112852144540077331111030554624 }, { target := 437, numerator := 112852185381168710303977832448 }, { target := 445, numerator := 1347783242907620055466377216 }, { target := 492, numerator := 2246373473331665414022758400 }, { target := 493, numerator := 188086907566795551851717591040 }, { target := 498, numerator := 188086975635281183839963054080 }, { target := 506, numerator := 2246305404846033425777295360 }, { target := 527, numerator := 2148094633873405052159262720 }, { target := 528, numerator := 179858105360748246458204946432 }, { target := 533, numerator := 179858170451237632046964670464 }, { target := 541, numerator := 2148029543384019463399538688 }, { target := 906, numerator := 119067714745541107940065280 }, { target := 907, numerator := 12484035144451772582377553920 }, { target := 909, numerator := 134565421078743136295976960000 }, { target := 917, numerator := 12484044667583400634933575680 }, { target := 924, numerator := 119067714745541107940065280 }, { target := 941, numerator := 105459975917479267032629248 }, { target := 942, numerator := 11057288270800141430105833472 }, { target := 944, numerator := 119186515812601063576436736000 }, { target := 952, numerator := 11057296705573869133798309888 }, { target := 959, numerator := 105459975917479267032629248 }]

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
    Slot4.Left13.expected,
    Slot4.Left14.expected,
    Slot4.Left15.expected,
    Slot4.Left16.expected,
    Slot4.Left17.expected,
    Slot4.Left18.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected,
    Slot5.Left4.expected,
    Slot5.Left5.expected,
    Slot5.Left6.expected,
    Slot5.Left7.expected,
    Slot5.Left8.expected,
    Slot5.Left9.expected,
    Slot5.Left10.expected,
    Slot5.Left11.expected,
    Slot5.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 238349107351060030471274496 }, { target := 12, numerator := 2308666873689985557580480512 }, { target := 17, numerator := 238349107351060030471274496 }, { target := 24, numerator := 233383500947912946503122944 }, { target := 26, numerator := 2260569647154777525130887168 }, { target := 31, numerator := 233383500947912946503122944 }, { target := 55, numerator := 183727436916442106821607424 }, { target := 57, numerator := 1779597381802697200634953728 }, { target := 62, numerator := 183727436916442106821607424 }, { target := 69, numerator := 5775000246860058654960254976 }, { target := 71, numerator := 55937074460446941738877059072 }, { target := 76, numerator := 5775000246860058654960254976 }, { target := 95, numerator := 183727436916442106821607424 }, { target := 97, numerator := 1779597381802697200634953728 }, { target := 102, numerator := 183727436916442106821607424 }, { target := 144, numerator := 183727436916442106821607424 }, { target := 146, numerator := 1779597381802697200634953728 }, { target := 151, numerator := 183727436916442106821607424 }, { target := 170, numerator := 188693043319589190789758976 }, { target := 172, numerator := 1827694608337905233084547072 }, { target := 177, numerator := 188693043319589190789758976 }, { target := 271, numerator := 188693043319589190789758976 }, { target := 273, numerator := 1827694608337905233084547072 }, { target := 278, numerator := 188693043319589190789758976 }, { target := 285, numerator := 3192884917223574991521447936 }, { target := 287, numerator := 30926516662138764865088520192 }, { target := 292, numerator := 3192884917223574991521447936 }, { target := 311, numerator := 173796224110147938885304320 }, { target := 313, numerator := 1683402928732281135735767040 }, { target := 318, numerator := 173796224110147938885304320 }, { target := 360, numerator := 5775000246860058654960254976 }, { target := 362, numerator := 55937074460446941738877059072 }, { target := 367, numerator := 5775000246860058654960254976 }, { target := 386, numerator := 3192884917223574991521447936 }, { target := 388, numerator := 30926516662138764865088520192 }, { target := 393, numerator := 3192884917223574991521447936 }, { target := 482, numerator := 238349107351060030471274496 }, { target := 484, numerator := 2308666873689985557580480512 }, { target := 489, numerator := 238349107351060030471274496 }, { target := 637, numerator := 70199171041614544188211200 }, { target := 638, numerator := 5877715861462360995366174720 }, { target := 643, numerator := 5877717988602536994998845440 }, { target := 651, numerator := 70197043901438544555540480 }, { target := 663, numerator := 1347824083998999248413655040 }, { target := 664, numerator := 112852144540077331111030554624 }, { target := 669, numerator := 112852185381168710303977832448 }, { target := 677, numerator := 1347783242907620055466377216 }, { target := 698, numerator := 70199171041614544188211200 }, { target := 699, numerator := 5877715861462360995366174720 }, { target := 704, numerator := 5877717988602536994998845440 }, { target := 712, numerator := 70197043901438544555540480 }, { target := 759, numerator := 2162134468081727960996904960 }, { target := 760, numerator := 181033648533040718657278181376 }, { target := 765, numerator := 181033714048958139445964439552 }, { target := 773, numerator := 2162068952164307172310646784 }, { target := 794, numerator := 1221465576124093068874874880 }, { target := 795, numerator := 102272255989445081319371440128 }, { target := 800, numerator := 102272293001684143712979910656 }, { target := 808, numerator := 1221428563885030675266404352 }, { target := 890, numerator := 84239005249937453025853440 }, { target := 891, numerator := 7053259033754833194439409664 }, { target := 896, numerator := 7053261586323044393998614528 }, { target := 904, numerator := 84236452681726253466648576 }]

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
    Slot5.Left13.expected,
    Slot5.Left14.expected,
    Slot5.Left15.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 250, numerator := 317798809801413373961699328 }, { target := 251, numerator := 311178001263883928670830592 }, { target := 252, numerator := 244969915888589475762143232 }, { target := 253, numerator := 7700000329146744873280339968 }, { target := 254, numerator := 244969915888589475762143232 }, { target := 255, numerator := 244969915888589475762143232 }, { target := 256, numerator := 251590724426118921053011968 }, { target := 257, numerator := 251590724426118921053011968 }, { target := 258, numerator := 4257179889631433322028597248 }, { target := 259, numerator := 231728298813530585180405760 }, { target := 260, numerator := 7700000329146744873280339968 }, { target := 261, numerator := 4257179889631433322028597248 }, { target := 262, numerator := 317798809801413373961699328 }, { target := 263, numerator := 244969915888589475762143232 }, { target := 264, numerator := 231728298813530585180405760 }, { target := 265, numerator := 311178001263883928670830592 }, { target := 562, numerator := 3078222498253314076773974016 }, { target := 563, numerator := 3014092862873036700174516224 }, { target := 564, numerator := 2372796509070262934179938304 }, { target := 565, numerator := 74582765947262588985169412096 }, { target := 566, numerator := 2372796509070262934179938304 }, { target := 567, numerator := 2372796509070262934179938304 }, { target := 568, numerator := 2436926144450540310779396096 }, { target := 569, numerator := 2436926144450540310779396096 }, { target := 570, numerator := 41235355549518353153451360256 }, { target := 571, numerator := 2244537238309708180981022720 }, { target := 572, numerator := 74582765947262588985169412096 }, { target := 573, numerator := 41235355549518353153451360256 }, { target := 574, numerator := 3078222498253314076773974016 }, { target := 575, numerator := 2372796509070262934179938304 }, { target := 576, numerator := 2244537238309708180981022720 }, { target := 577, numerator := 3014092862873036700174516224 }, { target := 627, numerator := 183727436916442106821607424 }, { target := 629, numerator := 1779597381802697200634953728 }, { target := 634, numerator := 183727436916442106821607424 }, { target := 653, numerator := 173796224110147938885304320 }, { target := 655, numerator := 1683402928732281135735767040 }, { target := 660, numerator := 173796224110147938885304320 }, { target := 749, numerator := 233383500947912946503122944 }, { target := 751, numerator := 2260569647154777525130887168 }, { target := 756, numerator := 233383500947912946503122944 }, { target := 925, numerator := 317798809801413373961699328 }, { target := 926, numerator := 311178001263883928670830592 }, { target := 927, numerator := 244969915888589475762143232 }, { target := 928, numerator := 7700000329146744873280339968 }, { target := 929, numerator := 244969915888589475762143232 }, { target := 930, numerator := 244969915888589475762143232 }, { target := 931, numerator := 251590724426118921053011968 }, { target := 932, numerator := 251590724426118921053011968 }, { target := 933, numerator := 4257179889631433322028597248 }, { target := 934, numerator := 231728298813530585180405760 }, { target := 935, numerator := 7700000329146744873280339968 }, { target := 936, numerator := 4257179889631433322028597248 }, { target := 937, numerator := 317798809801413373961699328 }, { target := 938, numerator := 244969915888589475762143232 }, { target := 939, numerator := 231728298813530585180405760 }, { target := 940, numerator := 311178001263883928670830592 }]

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
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 121, numerator := 86293615134082268953313280 }, { target := 122, numerator := 2301163070242193838755020800 }, { target := 123, numerator := 2200487185919097858309488640 }, { target := 124, numerator := 71911345945068557461094400 }, { target := 125, numerator := 2258016262675152704278364160 }, { target := 126, numerator := 71911345945068557461094400 }, { target := 127, numerator := 2200487185919097858309488640 }, { target := 128, numerator := 1251257419444192899823042560 }, { target := 129, numerator := 2258016262675152704278364160 }, { target := 130, numerator := 35250941782272606867428474880 }, { target := 131, numerator := 1380697842145316303253012480 }, { target := 132, numerator := 2301163070242193838755020800 }, { target := 133, numerator := 2200487185919097858309488640 }, { target := 134, numerator := 71911345945068557461094400 }, { target := 135, numerator := 1380697842145316303253012480 }, { target := 136, numerator := 71911345945068557461094400 }, { target := 137, numerator := 2214869455108111569801707520 }, { target := 138, numerator := 1251257419444192899823042560 }, { target := 139, numerator := 86293615134082268953313280 }, { target := 196, numerator := 7225289741895194979669639168 }, { target := 197, numerator := 192674393117205199457857044480 }, { target := 198, numerator := 184244888418327471981575798784 }, { target := 199, numerator := 6021074784912662483058032640 }, { target := 200, numerator := 189061748246257601968022224896 }, { target := 201, numerator := 6021074784912662483058032640 }, { target := 202, numerator := 184244888418327471981575798784 }, { target := 203, numerator := 104766701257480327205209767936 }, { target := 204, numerator := 189061748246257601968022224896 }, { target := 205, numerator := 2951530859564187149195047600128 }, { target := 206, numerator := 115604635870323119674714226688 }, { target := 207, numerator := 192674393117205199457857044480 }, { target := 208, numerator := 184244888418327471981575798784 }, { target := 209, numerator := 6021074784912662483058032640 }, { target := 210, numerator := 115604635870323119674714226688 }, { target := 211, numerator := 6021074784912662483058032640 }, { target := 212, numerator := 185449103375310004478187405312 }, { target := 213, numerator := 104766701257480327205209767936 }, { target := 214, numerator := 7225289741895194979669639168 }, { target := 508, numerator := 7225292356721167427998580736 }, { target := 509, numerator := 192674462845897798079962152960 }, { target := 510, numerator := 184244955096389769413963808768 }, { target := 511, numerator := 6021076963934306189998817280 }, { target := 512, numerator := 189061816667537214365962862592 }, { target := 513, numerator := 6021076963934306189998817280 }, { target := 514, numerator := 184244955096389769413963808768 }, { target := 515, numerator := 104766739172456927705979420672 }, { target := 516, numerator := 189061816667537214365962862592 }, { target := 517, numerator := 2951531927720596894337420230656 }, { target := 518, numerator := 115604677707538678847977291776 }, { target := 519, numerator := 192674462845897798079962152960 }, { target := 520, numerator := 184244955096389769413963808768 }, { target := 521, numerator := 6021076963934306189998817280 }, { target := 522, numerator := 115604677707538678847977291776 }, { target := 523, numerator := 6021076963934306189998817280 }, { target := 524, numerator := 185449170489176630651963572224 }, { target := 525, numerator := 104766739172456927705979420672 }, { target := 526, numerator := 7225292356721167427998580736 }]

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
    Slot9.Left14.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 121085811605635025023795200 }, { target := 35, numerator := 124545406222938882881617920 }, { target := 36, numerator := 121085811605635025023795200 }, { target := 37, numerator := 107247433136419593592504320 }, { target := 38, numerator := 5019871789707897751700766720 }, { target := 39, numerator := 1366539873835023853839974400 }, { target := 40, numerator := 124545406222938882881617920 }, { target := 41, numerator := 5019871789707897751700766720 }, { target := 42, numerator := 121085811605635025023795200 }, { target := 43, numerator := 121085811605635025023795200 }, { target := 44, numerator := 103787838519115735734681600 }, { target := 45, numerator := 121085811605635025023795200 }, { target := 46, numerator := 1366539873835023853839974400 }, { target := 47, numerator := 103787838519115735734681600 }, { target := 48, numerator := 121085811605635025023795200 }, { target := 49, numerator := 107247433136419593592504320 }, { target := 79, numerator := 12695628960459429744790732800 }, { target := 80, numerator := 13058361216472556308927610880 }, { target := 81, numerator := 12695628960459429744790732800 }, { target := 82, numerator := 11244699936406923488243220480 }, { target := 83, numerator := 526324503475046644562610094080 }, { target := 84, numerator := 143279241125184992834066841600 }, { target := 85, numerator := 13058361216472556308927610880 }, { target := 86, numerator := 526324503475046644562610094080 }, { target := 87, numerator := 12695628960459429744790732800 }, { target := 88, numerator := 12695628960459429744790732800 }, { target := 89, numerator := 10881967680393796924106342400 }, { target := 90, numerator := 12695628960459429744790732800 }, { target := 91, numerator := 143279241125184992834066841600 }, { target := 92, numerator := 10881967680393796924106342400 }, { target := 93, numerator := 12695628960459429744790732800 }, { target := 94, numerator := 11244699936406923488243220480 }, { target := 906, numerator := 86291000308109820624371712 }, { target := 907, numerator := 2301093341549595216649912320 }, { target := 908, numerator := 2200420507856800425921478656 }, { target := 909, numerator := 71909166923424850520309760 }, { target := 910, numerator := 2257947841395540306337726464 }, { target := 911, numerator := 71909166923424850520309760 }, { target := 912, numerator := 2200420507856800425921478656 }, { target := 913, numerator := 1251219504467592399053389824 }, { target := 914, numerator := 2257947841395540306337726464 }, { target := 915, numerator := 35249873625862861725055844352 }, { target := 916, numerator := 1380656004929757129989947392 }, { target := 917, numerator := 2301093341549595216649912320 }, { target := 918, numerator := 2200420507856800425921478656 }, { target := 919, numerator := 71909166923424850520309760 }, { target := 920, numerator := 1380656004929757129989947392 }, { target := 921, numerator := 71909166923424850520309760 }, { target := 922, numerator := 2214802341241485396025540608 }, { target := 923, numerator := 1251219504467592399053389824 }, { target := 924, numerator := 86291000308109820624371712 }]

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
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 194784848812709344234700800 }, { target := 11, numerator := 3903488370206695258463404032 }, { target := 12, numerator := 6552562314059542340055334912 }, { target := 13, numerator := 6287654919674257631896141824 }, { target := 14, numerator := 194784848812709344234700800 }, { target := 15, numerator := 6287654919674257631896141824 }, { target := 16, numerator := 4199561340402013461700149248 }, { target := 17, numerator := 202576242765217718004088832 }, { target := 18, numerator := 3903488370206695258463404032 }, { target := 19, numerator := 186993454860200970465312768 }, { target := 154, numerator := 136846190927535392843366400000 }, { target := 155, numerator := 140756082096893546924605440000 }, { target := 156, numerator := 136846190927535392843366400000 }, { target := 157, numerator := 121206626250102776518410240000 }, { target := 158, numerator := 5673252086738681571877847040000 }, { target := 159, numerator := 1544407011896470862089420800000 }, { target := 160, numerator := 140756082096893546924605440000 }, { target := 161, numerator := 5673252086738681571877847040000 }, { target := 162, numerator := 136846190927535392843366400000 }, { target := 163, numerator := 136846190927535392843366400000 }, { target := 164, numerator := 117296735080744622437171200000 }, { target := 165, numerator := 136846190927535392843366400000 }, { target := 166, numerator := 1544407011896470862089420800000 }, { target := 167, numerator := 117296735080744622437171200000 }, { target := 168, numerator := 136846190927535392843366400000 }, { target := 169, numerator := 121206626250102776518410240000 }, { target := 492, numerator := 12695638645000068442305331200 }, { target := 493, numerator := 13058371177714356112085483520 }, { target := 494, numerator := 12695638645000068442305331200 }, { target := 495, numerator := 11244708514142917763184721920 }, { target := 496, numerator := 526324904968431408851001016320 }, { target := 497, numerator := 143279350422143629563160166400 }, { target := 498, numerator := 13058371177714356112085483520 }, { target := 499, numerator := 526324904968431408851001016320 }, { target := 500, numerator := 12695638645000068442305331200 }, { target := 501, numerator := 12695638645000068442305331200 }, { target := 502, numerator := 10881975981428630093404569600 }, { target := 503, numerator := 12695638645000068442305331200 }, { target := 504, numerator := 143279350422143629563160166400 }, { target := 505, numerator := 10881975981428630093404569600 }, { target := 506, numerator := 12695638645000068442305331200 }, { target := 507, numerator := 11244708514142917763184721920 }, { target := 890, numerator := 121085811605635025023795200 }, { target := 891, numerator := 124545406222938882881617920 }, { target := 892, numerator := 121085811605635025023795200 }, { target := 893, numerator := 107247433136419593592504320 }, { target := 894, numerator := 5019871789707897751700766720 }, { target := 895, numerator := 1366539873835023853839974400 }, { target := 896, numerator := 124545406222938882881617920 }, { target := 897, numerator := 5019871789707897751700766720 }, { target := 898, numerator := 121085811605635025023795200 }, { target := 899, numerator := 121085811605635025023795200 }, { target := 900, numerator := 103787838519115735734681600 }, { target := 901, numerator := 121085811605635025023795200 }, { target := 902, numerator := 1366539873835023853839974400 }, { target := 903, numerator := 103787838519115735734681600 }, { target := 904, numerator := 121085811605635025023795200 }, { target := 905, numerator := 107247433136419593592504320 }]

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

namespace RouteChunk8

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left3.expected,
    Slot12.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 1, numerator := 3819256781700796941284147200 }, { target := 2, numerator := 3490872086451756456612986880 }, { target := 3, numerator := 3819256781700796941284147200 }, { target := 4, numerator := 3490872086451756456612986880 }, { target := 51, numerator := 13058297702026867517727703040 }, { target := 52, numerator := 11935528179983435918072610816 }, { target := 53, numerator := 13058297702026867517727703040 }, { target := 54, numerator := 11935528179983435918072610816 }, { target := 55, numerator := 6816984069084049029097062400 }, { target := 56, numerator := 136612360744444342543105130496 }, { target := 57, numerator := 229323344083987409338825179136 }, { target := 58, numerator := 220052245750033102659253174272 }, { target := 59, numerator := 6816984069084049029097062400 }, { target := 60, numerator := 220052245750033102659253174272 }, { target := 61, numerator := 146974176529452097067332665344 }, { target := 62, numerator := 7089663431847410990260944896 }, { target := 63, numerator := 136612360744444342543105130496 }, { target := 64, numerator := 6544304706320687067933179904 }, { target := 140, numerator := 3819255548074787011957882880 }, { target := 141, numerator := 3490870958894524951116644352 }, { target := 142, numerator := 3819255548074787011957882880 }, { target := 143, numerator := 3490870958894524951116644352 }, { target := 144, numerator := 6816987412556412388953292800 }, { target := 145, numerator := 136612427747630504274623987712 }, { target := 146, numerator := 229323456558397712764388769792 }, { target := 147, numerator := 220052353677320991915412291584 }, { target := 148, numerator := 6816987412556412388953292800 }, { target := 149, numerator := 220052353677320991915412291584 }, { target := 150, numerator := 146974248614716251105832992768 }, { target := 151, numerator := 7089666909058668884511424512 }, { target := 152, numerator := 136612427747630504274623987712 }, { target := 153, numerator := 6544307916054155893395161088 }, { target := 482, numerator := 194783177076527664306585600 }, { target := 483, numerator := 3903454868613614392703975424 }, { target := 484, numerator := 6552506076854390627273539584 }, { target := 485, numerator := 6287600956030313003816583168 }, { target := 486, numerator := 194783177076527664306585600 }, { target := 487, numerator := 6287600956030313003816583168 }, { target := 488, numerator := 4199525297769936442449985536 }, { target := 489, numerator := 202574504159588770878849024 }, { target := 490, numerator := 3903454868613614392703975424 }, { target := 491, numerator := 186991849993466557734322176 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk8

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent0
