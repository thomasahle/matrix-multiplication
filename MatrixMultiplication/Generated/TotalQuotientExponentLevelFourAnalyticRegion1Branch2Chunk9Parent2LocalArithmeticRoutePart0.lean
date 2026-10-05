import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk9Parent2LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 40; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 142, numerator := 4722366482869645213696000 }, { target := 143, numerator := 79335756912210039590092800 }, { target := 144, numerator := 171894139976455085778534400 }, { target := 145, numerator := 5666839779443574256435200 }, { target := 146, numerator := 90669436471097188102963200 }, { target := 147, numerator := 6611313076017503299174400 }, { target := 148, numerator := 171894139976455085778534400 }, { target := 149, numerator := 171894139976455085778534400 }, { target := 150, numerator := 90669436471097188102963200 }, { target := 151, numerator := 2121287024105044629992243200 }, { target := 152, numerator := 170005193383307227693056000 }, { target := 153, numerator := 79335756912210039590092800 }, { target := 154, numerator := 171894139976455085778534400 }, { target := 155, numerator := 6611313076017503299174400 }, { target := 156, numerator := 170005193383307227693056000 }, { target := 157, numerator := 6611313076017503299174400 }, { target := 158, numerator := 171894139976455085778534400 }, { target := 159, numerator := 171894139976455085778534400 }, { target := 160, numerator := 5666839779443574256435200 }, { target := 282, numerator := 94636224316707690082467840 }, { target := 283, numerator := 1589888568520689193385459712 }, { target := 284, numerator := 3444758565128159919001829376 }, { target := 285, numerator := 113563469180049228098961408 }, { target := 286, numerator := 1817015506880787649583382528 }, { target := 287, numerator := 132490714043390766115454976 }, { target := 288, numerator := 3444758565128159919001829376 }, { target := 289, numerator := 3444758565128159919001829376 }, { target := 290, numerator := 1817015506880787649583382528 }, { target := 291, numerator := 42510591963065094385044553728 }, { target := 292, numerator := 3406904075401476842968842240 }, { target := 293, numerator := 1589888568520689193385459712 }, { target := 294, numerator := 3444758565128159919001829376 }, { target := 295, numerator := 132490714043390766115454976 }, { target := 296, numerator := 3406904075401476842968842240 }, { target := 297, numerator := 132490714043390766115454976 }, { target := 298, numerator := 3444758565128159919001829376 }, { target := 299, numerator := 3444758565128159919001829376 }, { target := 300, numerator := 113563469180049228098961408 }, { target := 411, numerator := 1364192986820246156135628800 }, { target := 413, numerator := 50377832092685882521288704000 }, { target := 416, numerator := 50377819756425783228026060800 }, { target := 423, numerator := 1364205323080345449398272000 }, { target := 627, numerator := 1246897888888038075421163520 }, { target := 629, numerator := 46046280174436255239084441600 }, { target := 632, numerator := 46046268898863940184121016320 }, { target := 639, numerator := 1246909164460353130384588800 }, { target := 723, numerator := 1364192986820246156135628800 }, { target := 725, numerator := 50377832092685882521288704000 }, { target := 728, numerator := 50377819756425783228026060800 }, { target := 735, numerator := 1364205323080345449398272000 }, { target := 758, numerator := 1246897888888038075421163520 }, { target := 760, numerator := 46046280174436255239084441600 }, { target := 763, numerator := 46046268898863940184121016320 }, { target := 770, numerator := 1246909164460353130384588800 }, { target := 774, numerator := 70272425875459716058384957440 }, { target := 777, numerator := 255595960820402255850949836800 }, { target := 779, numerator := 70272425875459716058384957440 }]

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
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot2.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 357, numerator := 158860408483734864988733440 }, { target := 358, numerator := 2668854862526745731810721792 }, { target := 359, numerator := 5782518868807949085589897216 }, { target := 360, numerator := 190632490180481837986480128 }, { target := 361, numerator := 3050119842887709407783682048 }, { target := 362, numerator := 222404571877228810984226816 }, { target := 363, numerator := 5782518868807949085589897216 }, { target := 364, numerator := 5782518868807949085589897216 }, { target := 365, numerator := 3050119842887709407783682048 }, { target := 366, numerator := 71360095490893701352939061248 }, { target := 367, numerator := 5718974705414455139594403840 }, { target := 368, numerator := 2668854862526745731810721792 }, { target := 369, numerator := 5782518868807949085589897216 }, { target := 370, numerator := 222404571877228810984226816 }, { target := 371, numerator := 5718974705414455139594403840 }, { target := 372, numerator := 222404571877228810984226816 }, { target := 373, numerator := 5782518868807949085589897216 }, { target := 374, numerator := 5782518868807949085589897216 }, { target := 375, numerator := 190632490180481837986480128 }, { target := 392, numerator := 152437990067032147498106880 }, { target := 393, numerator := 2560958233126140077968195584 }, { target := 394, numerator := 5548742838439970168931090432 }, { target := 395, numerator := 182925588080438576997728256 }, { target := 396, numerator := 2926809409287017231963652096 }, { target := 397, numerator := 213413186093845006497349632 }, { target := 398, numerator := 5548742838439970168931090432 }, { target := 399, numerator := 5548742838439970168931090432 }, { target := 400, numerator := 2926809409287017231963652096 }, { target := 401, numerator := 68475145138110840656149610496 }, { target := 402, numerator := 5487767642413157309931847680 }, { target := 403, numerator := 2560958233126140077968195584 }, { target := 404, numerator := 5548742838439970168931090432 }, { target := 405, numerator := 213413186093845006497349632 }, { target := 406, numerator := 5487767642413157309931847680 }, { target := 407, numerator := 213413186093845006497349632 }, { target := 408, numerator := 5548742838439970168931090432 }, { target := 409, numerator := 5548742838439970168931090432 }, { target := 410, numerator := 182925588080438576997728256 }, { target := 498, numerator := 4722366482869645213696000 }, { target := 499, numerator := 79335756912210039590092800 }, { target := 500, numerator := 171894139976455085778534400 }, { target := 501, numerator := 5666839779443574256435200 }, { target := 502, numerator := 90669436471097188102963200 }, { target := 503, numerator := 6611313076017503299174400 }, { target := 504, numerator := 171894139976455085778534400 }, { target := 505, numerator := 171894139976455085778534400 }, { target := 506, numerator := 90669436471097188102963200 }, { target := 507, numerator := 2121287024105044629992243200 }, { target := 508, numerator := 170005193383307227693056000 }, { target := 509, numerator := 79335756912210039590092800 }, { target := 510, numerator := 171894139976455085778534400 }, { target := 511, numerator := 6611313076017503299174400 }, { target := 512, numerator := 170005193383307227693056000 }, { target := 513, numerator := 6611313076017503299174400 }, { target := 514, numerator := 171894139976455085778534400 }, { target := 515, numerator := 171894139976455085778534400 }, { target := 516, numerator := 5666839779443574256435200 }]

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
    Slot2.Left5.expected,
    Slot2.Left6.expected,
    Slot2.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 573, numerator := 152437990067032147498106880 }, { target := 574, numerator := 2560958233126140077968195584 }, { target := 575, numerator := 5548742838439970168931090432 }, { target := 576, numerator := 182925588080438576997728256 }, { target := 577, numerator := 2926809409287017231963652096 }, { target := 578, numerator := 213413186093845006497349632 }, { target := 579, numerator := 5548742838439970168931090432 }, { target := 580, numerator := 5548742838439970168931090432 }, { target := 581, numerator := 2926809409287017231963652096 }, { target := 582, numerator := 68475145138110840656149610496 }, { target := 583, numerator := 5487767642413157309931847680 }, { target := 584, numerator := 2560958233126140077968195584 }, { target := 585, numerator := 5548742838439970168931090432 }, { target := 586, numerator := 213413186093845006497349632 }, { target := 587, numerator := 5487767642413157309931847680 }, { target := 588, numerator := 213413186093845006497349632 }, { target := 589, numerator := 5548742838439970168931090432 }, { target := 590, numerator := 5548742838439970168931090432 }, { target := 591, numerator := 182925588080438576997728256 }, { target := 608, numerator := 101814221370669550807285760 }, { target := 609, numerator := 1710478919027248453562400768 }, { target := 610, numerator := 3706037657892371649385201664 }, { target := 611, numerator := 122177065644803460968742912 }, { target := 612, numerator := 1954833050316855375499886592 }, { target := 613, numerator := 142539909918937371130200064 }, { target := 614, numerator := 3706037657892371649385201664 }, { target := 615, numerator := 3706037657892371649385201664 }, { target := 616, numerator := 1954833050316855375499886592 }, { target := 617, numerator := 45734948239704762222632763392 }, { target := 618, numerator := 3665311969344103829062287360 }, { target := 619, numerator := 1710478919027248453562400768 }, { target := 620, numerator := 3706037657892371649385201664 }, { target := 621, numerator := 142539909918937371130200064 }, { target := 622, numerator := 3665311969344103829062287360 }, { target := 623, numerator := 142539909918937371130200064 }, { target := 624, numerator := 3706037657892371649385201664 }, { target := 625, numerator := 3706037657892371649385201664 }, { target := 626, numerator := 122177065644803460968742912 }, { target := 669, numerator := 4911261142184431022243840 }, { target := 670, numerator := 82509187188698441173696512 }, { target := 671, numerator := 178769905575513289209675776 }, { target := 672, numerator := 5893513370621317226692608 }, { target := 673, numerator := 94296213929941075627081728 }, { target := 674, numerator := 6875765599058203431141376 }, { target := 675, numerator := 178769905575513289209675776 }, { target := 676, numerator := 178769905575513289209675776 }, { target := 677, numerator := 94296213929941075627081728 }, { target := 678, numerator := 2206138505069246415191932928 }, { target := 679, numerator := 176805401118639516800778240 }, { target := 680, numerator := 82509187188698441173696512 }, { target := 681, numerator := 178769905575513289209675776 }, { target := 682, numerator := 6875765599058203431141376 }, { target := 683, numerator := 176805401118639516800778240 }, { target := 684, numerator := 6875765599058203431141376 }, { target := 685, numerator := 178769905575513289209675776 }, { target := 686, numerator := 178769905575513289209675776 }, { target := 687, numerator := 5893513370621317226692608 }]

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
    Slot2.Left8.expected,
    Slot2.Left9.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot4.Left0.expected,
    Slot4.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 142, numerator := 138120475762537492836777984 }, { target := 143, numerator := 22050546259950115019122802688 }, { target := 145, numerator := 220031292043331882100518289408 }, { target := 153, numerator := 22050546259950115019122802688 }, { target := 160, numerator := 138104715781277504533168128 }, { target := 357, numerator := 1337845022853838269786882048 }, { target := 358, numerator := 213583202651289606058395303936 }, { target := 360, numerator := 2131239175850800735159138123776 }, { target := 368, numerator := 213583202651289606058395303936 }, { target := 375, numerator := 1337692370523526330230767616 }, { target := 411, numerator := 3081004119685676887481253888 }, { target := 413, numerator := 115761239651710829502834671616 }, { target := 416, numerator := 115752484384251589180608479232 }, { target := 423, numerator := 3089759387144917209707446272 }, { target := 627, numerator := 3081004119685676887481253888 }, { target := 629, numerator := 115761239651710829502834671616 }, { target := 632, numerator := 115752484384251589180608479232 }, { target := 639, numerator := 3089759387144917209707446272 }, { target := 704, numerator := 94636224316707690082467840 }, { target := 705, numerator := 1589888568520689193385459712 }, { target := 706, numerator := 3444758565128159919001829376 }, { target := 707, numerator := 113563469180049228098961408 }, { target := 708, numerator := 1817015506880787649583382528 }, { target := 709, numerator := 132490714043390766115454976 }, { target := 710, numerator := 3444758565128159919001829376 }, { target := 711, numerator := 3444758565128159919001829376 }, { target := 712, numerator := 1817015506880787649583382528 }, { target := 713, numerator := 42510591963065094385044553728 }, { target := 714, numerator := 3406904075401476842968842240 }, { target := 715, numerator := 1589888568520689193385459712 }, { target := 716, numerator := 3444758565128159919001829376 }, { target := 717, numerator := 132490714043390766115454976 }, { target := 718, numerator := 3406904075401476842968842240 }, { target := 719, numerator := 132490714043390766115454976 }, { target := 720, numerator := 3444758565128159919001829376 }, { target := 721, numerator := 3444758565128159919001829376 }, { target := 722, numerator := 113563469180049228098961408 }, { target := 723, numerator := 3081004119685676887481253888 }, { target := 725, numerator := 115761239651710829502834671616 }, { target := 728, numerator := 115752484384251589180608479232 }, { target := 735, numerator := 3089759387144917209707446272 }, { target := 739, numerator := 4533471823554859405148160 }, { target := 740, numerator := 76162326635721638006489088 }, { target := 741, numerator := 165018374377396882347393024 }, { target := 742, numerator := 5440166188265831286177792 }, { target := 743, numerator := 87042659012253300578844672 }, { target := 744, numerator := 6346860552976803167207424 }, { target := 745, numerator := 165018374377396882347393024 }, { target := 746, numerator := 165018374377396882347393024 }, { target := 747, numerator := 87042659012253300578844672 }, { target := 748, numerator := 2036435543140842844792553472 }, { target := 749, numerator := 163204985647974938585333760 }, { target := 750, numerator := 76162326635721638006489088 }, { target := 751, numerator := 165018374377396882347393024 }, { target := 752, numerator := 6346860552976803167207424 }, { target := 753, numerator := 163204985647974938585333760 }, { target := 754, numerator := 6346860552976803167207424 }, { target := 755, numerator := 165018374377396882347393024 }, { target := 756, numerator := 165018374377396882347393024 }, { target := 757, numerator := 5440166188265831286177792 }, { target := 758, numerator := 3081004119685676887481253888 }, { target := 760, numerator := 115761239651710829502834671616 }, { target := 763, numerator := 115752484384251589180608479232 }, { target := 770, numerator := 3089759387144917209707446272 }]

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
    Slot4.Left7.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 55, numerator := 272235809649188110388428800 }, { target := 56, numerator := 211738963060479641413222400 }, { target := 57, numerator := 241987386354833875900825600 }, { target := 58, numerator := 284335178966929804183470080 }, { target := 59, numerator := 3357574985673320028123955200 }, { target := 60, numerator := 7550006454270816928105758720 }, { target := 61, numerator := 211738963060479641413222400 }, { target := 62, numerator := 3357574985673320028123955200 }, { target := 63, numerator := 241987386354833875900825600 }, { target := 64, numerator := 235937701695963029003304960 }, { target := 65, numerator := 235937701695963029003304960 }, { target := 66, numerator := 235937701695963029003304960 }, { target := 67, numerator := 7550006454270816928105758720 }, { target := 68, numerator := 235937701695963029003304960 }, { target := 69, numerator := 272235809649188110388428800 }, { target := 70, numerator := 284335178966929804183470080 }, { target := 100, numerator := 22794068828597936543005409280 }, { target := 101, numerator := 17728720200020617311226429440 }, { target := 102, numerator := 20261394514309276927115919360 }, { target := 103, numerator := 23807138554313400389361205248 }, { target := 104, numerator := 281126848886041217363733381120 }, { target := 105, numerator := 632155508846449440126016684032 }, { target := 106, numerator := 17728720200020617311226429440 }, { target := 107, numerator := 281126848886041217363733381120 }, { target := 108, numerator := 20261394514309276927115919360 }, { target := 109, numerator := 19754859651451545003938021376 }, { target := 110, numerator := 19754859651451545003938021376 }, { target := 111, numerator := 19754859651451545003938021376 }, { target := 112, numerator := 632155508846449440126016684032 }, { target := 113, numerator := 19754859651451545003938021376 }, { target := 114, numerator := 22794068828597936543005409280 }, { target := 115, numerator := 23807138554313400389361205248 }, { target := 315, numerator := 22794077077751302004995522560 }, { target := 316, numerator := 17728726616028790448329850880 }, { target := 317, numerator := 20261401846890046226662686720 }, { target := 318, numerator := 23807147170095804316328656896 }, { target := 319, numerator := 281126950625599391394944778240 }, { target := 320, numerator := 632155737622969442271875825664 }, { target := 321, numerator := 17728726616028790448329850880 }, { target := 322, numerator := 281126950625599391394944778240 }, { target := 323, numerator := 20261401846890046226662686720 }, { target := 324, numerator := 19754866800717795070996119552 }, { target := 325, numerator := 19754866800717795070996119552 }, { target := 326, numerator := 19754866800717795070996119552 }, { target := 327, numerator := 632155737622969442271875825664 }, { target := 328, numerator := 19754866800717795070996119552 }, { target := 329, numerator := 22794077077751302004995522560 }, { target := 330, numerator := 23807147170095804316328656896 }, { target := 669, numerator := 138120475762537492836777984 }, { target := 670, numerator := 22050546259950115019122802688 }, { target := 672, numerator := 220031292043331882100518289408 }, { target := 680, numerator := 22050546259950115019122802688 }, { target := 687, numerator := 138104715781277504533168128 }]

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
    Slot5.Left14.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left2.expected,
    Slot6.Left3.expected,
    Slot6.Left4.expected,
    Slot6.Left5.expected,
    Slot6.Left6.expected,
    Slot6.Left7.expected,
    Slot6.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 142, numerator := 13711082100048780242976768 }, { target := 143, numerator := 2025055073415612732002009088 }, { target := 145, numerator := 21106810363180631942989086720 }, { target := 153, numerator := 2025055073415612732002009088 }, { target := 160, numerator := 13711082100048780242976768 }, { target := 282, numerator := 328181384459232094848024576 }, { target := 283, numerator := 48470673047560795069209378816 }, { target := 285, numerator := 505201719015484803280577495040 }, { target := 293, numerator := 48470673047560795069209378816 }, { target := 300, numerator := 328181384459232094848024576 }, { target := 357, numerator := 245472598887970097898455040 }, { target := 358, numerator := 36255018249860163427777904640 }, { target := 360, numerator := 377879991985975829947062681600 }, { target := 368, numerator := 36255018249860163427777904640 }, { target := 375, numerator := 245472598887970097898455040 }, { target := 392, numerator := 284836673304239176660549632 }, { target := 393, numerator := 42068886041279180626106253312 }, { target := 395, numerator := 438476963673816999073708769280 }, { target := 403, numerator := 42068886041279180626106253312 }, { target := 410, numerator := 284836673304239176660549632 }, { target := 498, numerator := 13711082100048780242976768 }, { target := 499, numerator := 2025055073415612732002009088 }, { target := 501, numerator := 21106810363180631942989086720 }, { target := 509, numerator := 2025055073415612732002009088 }, { target := 516, numerator := 13711082100048780242976768 }, { target := 573, numerator := 284394380333269861168840704 }, { target := 574, numerator := 42003561684072225376686833664 }, { target := 576, numerator := 437796098823391817398128476160 }, { target := 584, numerator := 42003561684072225376686833664 }, { target := 591, numerator := 284394380333269861168840704 }, { target := 608, numerator := 285721259246177807643967488 }, { target := 609, numerator := 42199534755693091124945092608 }, { target := 611, numerator := 439838693374667362424869355520 }, { target := 619, numerator := 42199534755693091124945092608 }, { target := 626, numerator := 285721259246177807643967488 }, { target := 653, numerator := 272227560495822648398315520 }, { target := 654, numerator := 211732547052306504309800960 }, { target := 655, numerator := 241980053774064576354058240 }, { target := 656, numerator := 284326563184525877216018432 }, { target := 657, numerator := 3357473246115145996912558080 }, { target := 658, numerator := 7549777677750814782246617088 }, { target := 659, numerator := 211732547052306504309800960 }, { target := 660, numerator := 3357473246115145996912558080 }, { target := 661, numerator := 241980053774064576354058240 }, { target := 662, numerator := 235930552429712961945206784 }, { target := 663, numerator := 235930552429712961945206784 }, { target := 664, numerator := 235930552429712961945206784 }, { target := 665, numerator := 7549777677750814782246617088 }, { target := 666, numerator := 235930552429712961945206784 }, { target := 667, numerator := 272227560495822648398315520 }, { target := 668, numerator := 284326563184525877216018432 }, { target := 669, numerator := 13711082100048780242976768 }, { target := 670, numerator := 2025055073415612732002009088 }, { target := 672, numerator := 21106810363180631942989086720 }, { target := 680, numerator := 2025055073415612732002009088 }, { target := 687, numerator := 13711082100048780242976768 }, { target := 704, numerator := 328181384459232094848024576 }, { target := 705, numerator := 48470673047560795069209378816 }, { target := 707, numerator := 505201719015484803280577495040 }, { target := 715, numerator := 48470673047560795069209378816 }, { target := 722, numerator := 328181384459232094848024576 }]

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
    Slot6.Left9.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
    Slot7.Left14.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left3.expected,
    Slot8.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 11, numerator := 14037536435764227391619072 }, { target := 12, numerator := 335995226946356668534882304 }, { target := 13, numerator := 251317184575778909753180160 }, { target := 14, numerator := 291618498859102014200086528 }, { target := 15, numerator := 14037536435764227391619072 }, { target := 16, numerator := 291165675103109619768098816 }, { target := 17, numerator := 292524146371086803064061952 }, { target := 18, numerator := 14037536435764227391619072 }, { target := 19, numerator := 335995226946356668534882304 }, { target := 20, numerator := 14037536435764227391619072 }, { target := 31, numerator := 2073270670401698749430628352 }, { target := 32, numerator := 49624736691550337808952459264 }, { target := 33, numerator := 37118232970094929223677378560 }, { target := 34, numerator := 43070526185119161117204021248 }, { target := 35, numerator := 2073270670401698749430628352 }, { target := 36, numerator := 43003646486073945028512710656 }, { target := 37, numerator := 43204285583209593294586642432 }, { target := 38, numerator := 2073270670401698749430628352 }, { target := 39, numerator := 49624736691550337808952459264 }, { target := 40, numerator := 2073270670401698749430628352 }, { target := 55, numerator := 311871102294426692263870464 }, { target := 56, numerator := 26225004556276223360869859328 }, { target := 61, numerator := 26224998229392035049614868480 }, { target := 69, numerator := 311877429178615003518861312 }, { target := 76, numerator := 21609353467065885084488826880 }, { target := 77, numerator := 517230331372996346215829340160 }, { target := 78, numerator := 386877134652308587802945126400 }, { target := 79, numerator := 448916891380336451432606597120 }, { target := 80, numerator := 21609353467065885084488826880 }, { target := 81, numerator := 448219815462044003526655344640 }, { target := 82, numerator := 450311043216921347244509102080 }, { target := 83, numerator := 21609353467065885084488826880 }, { target := 84, numerator := 517230331372996346215829340160 }, { target := 85, numerator := 21609353467065885084488826880 }, { target := 100, numerator := 26225004556276223360869859328 }, { target := 101, numerator := 2205240751441686748001998995456 }, { target := 106, numerator := 2205240219418791889173699624960 }, { target := 114, numerator := 26225536579171082189169229824 }, { target := 305, numerator := 2073270670401698749430628352 }, { target := 306, numerator := 49624736691550337808952459264 }, { target := 307, numerator := 37118232970094929223677378560 }, { target := 308, numerator := 43070526185119161117204021248 }, { target := 309, numerator := 2073270670401698749430628352 }, { target := 310, numerator := 43003646486073945028512710656 }, { target := 311, numerator := 43204285583209593294586642432 }, { target := 312, numerator := 2073270670401698749430628352 }, { target := 313, numerator := 49624736691550337808952459264 }, { target := 314, numerator := 2073270670401698749430628352 }, { target := 315, numerator := 26224998229392035049614868480 }, { target := 316, numerator := 2205240219418791889173699624960 }, { target := 321, numerator := 2205239687396025382934780313600 }, { target := 329, numerator := 26225530252158541288534179840 }, { target := 653, numerator := 311877429178615003518861312 }, { target := 654, numerator := 26225536579171082189169229824 }, { target := 659, numerator := 26225530252158541288534179840 }, { target := 667, numerator := 311883756191155904153911296 }, { target := 739, numerator := 13711082100048780242976768 }, { target := 740, numerator := 2025055073415612732002009088 }, { target := 742, numerator := 21106810363180631942989086720 }, { target := 750, numerator := 2025055073415612732002009088 }, { target := 757, numerator := 13711082100048780242976768 }]

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
    Slot8.Left18.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left2.expected,
    Slot9.Left3.expected,
    Slot9.Left4.expected,
    Slot9.Left5.expected,
    Slot9.Left6.expected,
    Slot9.Left7.expected,
    Slot9.Left8.expected,
    Slot9.Left9.expected,
    Slot9.Left10.expected,
    Slot9.Left11.expected,
    Slot9.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 55, numerator := 267099284938826070569779200 }, { target := 56, numerator := 22363992058247032079929835520 }, { target := 61, numerator := 22364000151755994419995607040 }, { target := 69, numerator := 267091191429863730504007680 }, { target := 100, numerator := 207743888285753610443161600 }, { target := 101, numerator := 17394216045303247173278760960 }, { target := 106, numerator := 17394222340254662326663249920 }, { target := 114, numerator := 207737593334338457058672640 }, { target := 126, numerator := 237421586612289840506470400 }, { target := 127, numerator := 19879104051775139626604298240 }, { target := 132, numerator := 19879111246005328373329428480 }, { target := 140, numerator := 237414392382101093781340160 }, { target := 195, numerator := 278970364269440562595102720 }, { target := 196, numerator := 23357947260835789061260050432 }, { target := 201, numerator := 23357955714056260838662078464 }, { target := 209, numerator := 278961911048968785193074688 }, { target := 240, numerator := 3294224514245521537027276800 }, { target := 241, numerator := 275822568718380062319134638080 }, { target := 246, numerator := 275822668538323931179945820160 }, { target := 254, numerator := 3294124694301652676216094720 }, { target := 266, numerator := 7407553502303443023801876480 }, { target := 267, numerator := 620228046415384356350054105088 }, { target := 272, numerator := 620228270875366245247878168576 }, { target := 280, numerator := 7407329042321554125977812992 }, { target := 315, numerator := 207743888285753610443161600 }, { target := 316, numerator := 17394216045303247173278760960 }, { target := 321, numerator := 17394222340254662326663249920 }, { target := 329, numerator := 207737593334338457058672640 }, { target := 341, numerator := 3294224514245521537027276800 }, { target := 342, numerator := 275822568718380062319134638080 }, { target := 347, numerator := 275822668538323931179945820160 }, { target := 355, numerator := 3294124694301652676216094720 }, { target := 376, numerator := 237421586612289840506470400 }, { target := 377, numerator := 19879104051775139626604298240 }, { target := 382, numerator := 19879111246005328373329428480 }, { target := 390, numerator := 237414392382101093781340160 }, { target := 456, numerator := 231486046946982594493808640 }, { target := 457, numerator := 19382126450480761135939190784 }, { target := 462, numerator := 19382133464855195163996192768 }, { target := 470, numerator := 231479032572548566436806656 }, { target := 482, numerator := 231486046946982594493808640 }, { target := 483, numerator := 19382126450480761135939190784 }, { target := 488, numerator := 19382133464855195163996192768 }, { target := 496, numerator := 231479032572548566436806656 }, { target := 531, numerator := 231486046946982594493808640 }, { target := 532, numerator := 19382126450480761135939190784 }, { target := 537, numerator := 19382133464855195163996192768 }, { target := 545, numerator := 231479032572548566436806656 }, { target := 557, numerator := 7407553502303443023801876480 }, { target := 558, numerator := 620228046415384356350054105088 }, { target := 563, numerator := 620228270875366245247878168576 }, { target := 571, numerator := 7407329042321554125977812992 }, { target := 643, numerator := 14037536435764227391619072 }, { target := 644, numerator := 335995226946356668534882304 }, { target := 645, numerator := 251317184575778909753180160 }, { target := 646, numerator := 291618498859102014200086528 }, { target := 647, numerator := 14037536435764227391619072 }, { target := 648, numerator := 291165675103109619768098816 }, { target := 649, numerator := 292524146371086803064061952 }, { target := 650, numerator := 14037536435764227391619072 }, { target := 651, numerator := 335995226946356668534882304 }, { target := 652, numerator := 14037536435764227391619072 }]

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
    Slot9.Left13.expected,
    Slot9.Left14.expected,
    Slot9.Left15.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left3.expected,
    Slot10.Left11.expected,
    Slot10.Left18.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 2, numerator := 3081004119685676887481253888 }, { target := 3, numerator := 3081004119685676887481253888 }, { target := 4, numerator := 3081004119685676887481253888 }, { target := 5, numerator := 3081004119685676887481253888 }, { target := 11, numerator := 139301291584829253618761728 }, { target := 12, numerator := 94636224316707690082467840 }, { target := 13, numerator := 1462401712802859332986208256 }, { target := 14, numerator := 152437990067032147498106880 }, { target := 15, numerator := 4722366482869645213696000 }, { target := 16, numerator := 152437990067032147498106880 }, { target := 17, numerator := 101814221370669550807285760 }, { target := 18, numerator := 139490186244144039427309568 }, { target := 19, numerator := 94636224316707690082467840 }, { target := 20, numerator := 4533471823554859405148160 }, { target := 22, numerator := 115761239651710829502834671616 }, { target := 23, numerator := 115761239651710829502834671616 }, { target := 24, numerator := 115761239651710829502834671616 }, { target := 25, numerator := 115761239651710829502834671616 }, { target := 31, numerator := 21564483394812322109504618496 }, { target := 32, numerator := 1589888568520689193385459712 }, { target := 33, numerator := 210775565138142259327170248704 }, { target := 34, numerator := 2560958233126140077968195584 }, { target := 35, numerator := 79335756912210039590092800 }, { target := 36, numerator := 2560958233126140077968195584 }, { target := 37, numerator := 1710478919027248453562400768 }, { target := 38, numerator := 21567656825088810511088222208 }, { target := 39, numerator := 1589888568520689193385459712 }, { target := 40, numerator := 76162326635721638006489088 }, { target := 72, numerator := 115752484384251589180608479232 }, { target := 73, numerator := 115752484384251589180608479232 }, { target := 74, numerator := 115752484384251589180608479232 }, { target := 75, numerator := 115752484384251589180608479232 }, { target := 76, numerator := 214389464042220808200504999936 }, { target := 78, numerator := 2076592017495651998360185864192 }, { target := 83, numerator := 214389464042220808200504999936 }, { target := 301, numerator := 3089759387144917209707446272 }, { target := 302, numerator := 3089759387144917209707446272 }, { target := 303, numerator := 3089759387144917209707446272 }, { target := 304, numerator := 3089759387144917209707446272 }, { target := 305, numerator := 21485147637900112069914525696 }, { target := 307, numerator := 208106710275615513595359526912 }, { target := 312, numerator := 21485147637900112069914525696 }, { target := 592, numerator := 231486046946982594493808640 }, { target := 593, numerator := 19382126450480761135939190784 }, { target := 598, numerator := 19382133464855195163996192768 }, { target := 606, numerator := 231479032572548566436806656 }, { target := 643, numerator := 134563569222783209545138176 }, { target := 645, numerator := 1303392566151128219199209472 }, { target := 650, numerator := 134563569222783209545138176 }, { target := 653, numerator := 267099284938826070569779200 }, { target := 654, numerator := 22363992058247032079929835520 }, { target := 659, numerator := 22364000151755994419995607040 }, { target := 667, numerator := 267091191429863730504007680 }, { target := 688, numerator := 278970364269440562595102720 }, { target := 689, numerator := 23357947260835789061260050432 }, { target := 694, numerator := 23357955714056260838662078464 }, { target := 702, numerator := 278961911048968785193074688 }]

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

namespace RouteChunk9

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot12.Left2.expected,
    Slot12.Left3.expected,
    Slot12.Left4.expected,
    Slot12.Left5.expected,
    Slot12.Left6.expected,
    Slot12.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 45, numerator := 171894139976455085778534400 }, { target := 46, numerator := 3444758565128159919001829376 }, { target := 47, numerator := 5782518868807949085589897216 }, { target := 48, numerator := 5548742838439970168931090432 }, { target := 49, numerator := 171894139976455085778534400 }, { target := 50, numerator := 5548742838439970168931090432 }, { target := 51, numerator := 3706037657892371649385201664 }, { target := 52, numerator := 178769905575513289209675776 }, { target := 53, numerator := 3444758565128159919001829376 }, { target := 54, numerator := 165018374377396882347393024 }, { target := 76, numerator := 5666839779443574256435200 }, { target := 77, numerator := 113563469180049228098961408 }, { target := 78, numerator := 190632490180481837986480128 }, { target := 79, numerator := 182925588080438576997728256 }, { target := 80, numerator := 5666839779443574256435200 }, { target := 81, numerator := 182925588080438576997728256 }, { target := 82, numerator := 122177065644803460968742912 }, { target := 83, numerator := 5893513370621317226692608 }, { target := 84, numerator := 113563469180049228098961408 }, { target := 85, numerator := 5440166188265831286177792 }, { target := 90, numerator := 90669436471097188102963200 }, { target := 91, numerator := 1817015506880787649583382528 }, { target := 92, numerator := 3050119842887709407783682048 }, { target := 93, numerator := 2926809409287017231963652096 }, { target := 94, numerator := 90669436471097188102963200 }, { target := 95, numerator := 2926809409287017231963652096 }, { target := 96, numerator := 1954833050316855375499886592 }, { target := 97, numerator := 94296213929941075627081728 }, { target := 98, numerator := 1817015506880787649583382528 }, { target := 99, numerator := 87042659012253300578844672 }, { target := 116, numerator := 6611313076017503299174400 }, { target := 117, numerator := 132490714043390766115454976 }, { target := 118, numerator := 222404571877228810984226816 }, { target := 119, numerator := 213413186093845006497349632 }, { target := 120, numerator := 6611313076017503299174400 }, { target := 121, numerator := 213413186093845006497349632 }, { target := 122, numerator := 142539909918937371130200064 }, { target := 123, numerator := 6875765599058203431141376 }, { target := 124, numerator := 132490714043390766115454976 }, { target := 125, numerator := 6346860552976803167207424 }, { target := 171, numerator := 171894139976455085778534400 }, { target := 172, numerator := 3444758565128159919001829376 }, { target := 173, numerator := 5782518868807949085589897216 }, { target := 174, numerator := 5548742838439970168931090432 }, { target := 175, numerator := 171894139976455085778534400 }, { target := 176, numerator := 5548742838439970168931090432 }, { target := 177, numerator := 3706037657892371649385201664 }, { target := 178, numerator := 178769905575513289209675776 }, { target := 179, numerator := 3444758565128159919001829376 }, { target := 180, numerator := 165018374377396882347393024 }, { target := 185, numerator := 171894139976455085778534400 }, { target := 186, numerator := 3444758565128159919001829376 }, { target := 187, numerator := 5782518868807949085589897216 }, { target := 188, numerator := 5548742838439970168931090432 }, { target := 189, numerator := 171894139976455085778534400 }, { target := 190, numerator := 5548742838439970168931090432 }, { target := 191, numerator := 3706037657892371649385201664 }, { target := 192, numerator := 178769905575513289209675776 }, { target := 193, numerator := 3444758565128159919001829376 }, { target := 194, numerator := 165018374377396882347393024 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk9

namespace RouteChunk10

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot12.Left8.expected,
    Slot12.Left9.expected,
    Slot12.Left10.expected,
    Slot12.Left11.expected,
    Slot12.Left12.expected,
    Slot12.Left13.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 216, numerator := 90669436471097188102963200 }, { target := 217, numerator := 1817015506880787649583382528 }, { target := 218, numerator := 3050119842887709407783682048 }, { target := 219, numerator := 2926809409287017231963652096 }, { target := 220, numerator := 90669436471097188102963200 }, { target := 221, numerator := 2926809409287017231963652096 }, { target := 222, numerator := 1954833050316855375499886592 }, { target := 223, numerator := 94296213929941075627081728 }, { target := 224, numerator := 1817015506880787649583382528 }, { target := 225, numerator := 87042659012253300578844672 }, { target := 230, numerator := 2121287024105044629992243200 }, { target := 231, numerator := 42510591963065094385044553728 }, { target := 232, numerator := 71360095490893701352939061248 }, { target := 233, numerator := 68475145138110840656149610496 }, { target := 234, numerator := 2121287024105044629992243200 }, { target := 235, numerator := 68475145138110840656149610496 }, { target := 236, numerator := 45734948239704762222632763392 }, { target := 237, numerator := 2206138505069246415191932928 }, { target := 238, numerator := 42510591963065094385044553728 }, { target := 239, numerator := 2036435543140842844792553472 }, { target := 256, numerator := 170005193383307227693056000 }, { target := 257, numerator := 3406904075401476842968842240 }, { target := 258, numerator := 5718974705414455139594403840 }, { target := 259, numerator := 5487767642413157309931847680 }, { target := 260, numerator := 170005193383307227693056000 }, { target := 261, numerator := 5487767642413157309931847680 }, { target := 262, numerator := 3665311969344103829062287360 }, { target := 263, numerator := 176805401118639516800778240 }, { target := 264, numerator := 3406904075401476842968842240 }, { target := 265, numerator := 163204985647974938585333760 }, { target := 305, numerator := 79335756912210039590092800 }, { target := 306, numerator := 1589888568520689193385459712 }, { target := 307, numerator := 2668854862526745731810721792 }, { target := 308, numerator := 2560958233126140077968195584 }, { target := 309, numerator := 79335756912210039590092800 }, { target := 310, numerator := 2560958233126140077968195584 }, { target := 311, numerator := 1710478919027248453562400768 }, { target := 312, numerator := 82509187188698441173696512 }, { target := 313, numerator := 1589888568520689193385459712 }, { target := 314, numerator := 76162326635721638006489088 }, { target := 331, numerator := 171894139976455085778534400 }, { target := 332, numerator := 3444758565128159919001829376 }, { target := 333, numerator := 5782518868807949085589897216 }, { target := 334, numerator := 5548742838439970168931090432 }, { target := 335, numerator := 171894139976455085778534400 }, { target := 336, numerator := 5548742838439970168931090432 }, { target := 337, numerator := 3706037657892371649385201664 }, { target := 338, numerator := 178769905575513289209675776 }, { target := 339, numerator := 3444758565128159919001829376 }, { target := 340, numerator := 165018374377396882347393024 }, { target := 432, numerator := 6611313076017503299174400 }, { target := 433, numerator := 132490714043390766115454976 }, { target := 434, numerator := 222404571877228810984226816 }, { target := 435, numerator := 213413186093845006497349632 }, { target := 436, numerator := 6611313076017503299174400 }, { target := 437, numerator := 213413186093845006497349632 }, { target := 438, numerator := 142539909918937371130200064 }, { target := 439, numerator := 6875765599058203431141376 }, { target := 440, numerator := 132490714043390766115454976 }, { target := 441, numerator := 6346860552976803167207424 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk10

namespace RouteChunk11

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot12.Left14.expected,
    Slot12.Left15.expected,
    Slot12.Left16.expected,
    Slot12.Left17.expected,
    Slot12.Left18.expected,
    Slot13.Left0.expected,
    Slot13.Left2.expected,
    Slot13.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 2, numerator := 1364192986820246156135628800 }, { target := 3, numerator := 1246897888888038075421163520 }, { target := 4, numerator := 1364192986820246156135628800 }, { target := 5, numerator := 1246897888888038075421163520 }, { target := 22, numerator := 50377832092685882521288704000 }, { target := 23, numerator := 46046280174436255239084441600 }, { target := 24, numerator := 50377832092685882521288704000 }, { target := 25, numerator := 46046280174436255239084441600 }, { target := 72, numerator := 50377819756425783228026060800 }, { target := 73, numerator := 46046268898863940184121016320 }, { target := 74, numerator := 50377819756425783228026060800 }, { target := 75, numerator := 46046268898863940184121016320 }, { target := 446, numerator := 170005193383307227693056000 }, { target := 447, numerator := 3406904075401476842968842240 }, { target := 448, numerator := 5718974705414455139594403840 }, { target := 449, numerator := 5487767642413157309931847680 }, { target := 450, numerator := 170005193383307227693056000 }, { target := 451, numerator := 5487767642413157309931847680 }, { target := 452, numerator := 3665311969344103829062287360 }, { target := 453, numerator := 176805401118639516800778240 }, { target := 454, numerator := 3406904075401476842968842240 }, { target := 455, numerator := 163204985647974938585333760 }, { target := 472, numerator := 6611313076017503299174400 }, { target := 473, numerator := 132490714043390766115454976 }, { target := 474, numerator := 222404571877228810984226816 }, { target := 475, numerator := 213413186093845006497349632 }, { target := 476, numerator := 6611313076017503299174400 }, { target := 477, numerator := 213413186093845006497349632 }, { target := 478, numerator := 142539909918937371130200064 }, { target := 479, numerator := 6875765599058203431141376 }, { target := 480, numerator := 132490714043390766115454976 }, { target := 481, numerator := 6346860552976803167207424 }, { target := 521, numerator := 171894139976455085778534400 }, { target := 522, numerator := 3444758565128159919001829376 }, { target := 523, numerator := 5782518868807949085589897216 }, { target := 524, numerator := 5548742838439970168931090432 }, { target := 525, numerator := 171894139976455085778534400 }, { target := 526, numerator := 5548742838439970168931090432 }, { target := 527, numerator := 3706037657892371649385201664 }, { target := 528, numerator := 178769905575513289209675776 }, { target := 529, numerator := 3444758565128159919001829376 }, { target := 530, numerator := 165018374377396882347393024 }, { target := 547, numerator := 171894139976455085778534400 }, { target := 548, numerator := 3444758565128159919001829376 }, { target := 549, numerator := 5782518868807949085589897216 }, { target := 550, numerator := 5548742838439970168931090432 }, { target := 551, numerator := 171894139976455085778534400 }, { target := 552, numerator := 5548742838439970168931090432 }, { target := 553, numerator := 3706037657892371649385201664 }, { target := 554, numerator := 178769905575513289209675776 }, { target := 555, numerator := 3444758565128159919001829376 }, { target := 556, numerator := 165018374377396882347393024 }, { target := 643, numerator := 5666839779443574256435200 }, { target := 644, numerator := 113563469180049228098961408 }, { target := 645, numerator := 190632490180481837986480128 }, { target := 646, numerator := 182925588080438576997728256 }, { target := 647, numerator := 5666839779443574256435200 }, { target := 648, numerator := 182925588080438576997728256 }, { target := 649, numerator := 122177065644803460968742912 }, { target := 650, numerator := 5893513370621317226692608 }, { target := 651, numerator := 113563469180049228098961408 }, { target := 652, numerator := 5440166188265831286177792 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk11

namespace RouteChunk12

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot13.Left12.expected,
    Slot14.Left0.expected,
    Slot14.Left3.expected,
    Slot14.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 70272425875459716058384957440 }, { target := 21, numerator := 255595960820402255850949836800 }, { target := 71, numerator := 70272425875459716058384957440 }, { target := 301, numerator := 1364205323080345449398272000 }, { target := 302, numerator := 1246909164460353130384588800 }, { target := 303, numerator := 1364205323080345449398272000 }, { target := 304, numerator := 1246909164460353130384588800 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk12

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9.Parent2
