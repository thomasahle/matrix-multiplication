import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk21Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 89; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21.Parent3

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
    Slot1.Left6.expected,
    Slot1.Left14.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left3.expected,
    Slot3.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 11946849331897254008586240 }, { target := 132, numerator := 238936986637945080171724800 }, { target := 133, numerator := 12373522522322155937464320 }, { target := 134, numerator := 222296732211373904945479680 }, { target := 135, numerator := 332805088531423504524902400 }, { target := 136, numerator := 11946849331897254008586240 }, { target := 137, numerator := 333231761721848406453780480 }, { target := 138, numerator := 333231761721848406453780480 }, { target := 139, numerator := 238510313447520178242846720 }, { target := 140, numerator := 12373522522322155937464320 }, { target := 227, numerator := 1412040889468396939499274240 }, { target := 228, numerator := 28240817789367938789985484800 }, { target := 229, numerator := 1462470921235125401624248320 }, { target := 230, numerator := 26274046550465528767111495680 }, { target := 231, numerator := 39335424778048200457479782400 }, { target := 232, numerator := 1412040889468396939499274240 }, { target := 233, numerator := 39385854809814928919604756480 }, { target := 234, numerator := 39385854809814928919604756480 }, { target := 235, numerator := 28190387757601210327860510720 }, { target := 236, numerator := 1462470921235125401624248320 }, { target := 263, numerator := 53513580282717713918328832 }, { target := 264, numerator := 58777211130198144795541504 }, { target := 265, numerator := 53513580282717713918328832 }, { target := 266, numerator := 58777211130198144795541504 }, { target := 302, numerator := 13399986569565963851283824640 }, { target := 303, numerator := 267999731391319277025676492800 }, { target := 304, numerator := 13878557518479033988829675520 }, { target := 305, numerator := 249335464383709541661388308480 }, { target := 306, numerator := 373285340152194707285763686400 }, { target := 307, numerator := 13399986569565963851283824640 }, { target := 308, numerator := 373763911101107777423309537280 }, { target := 309, numerator := 373763911101107777423309537280 }, { target := 310, numerator := 267521160442406206888130641920 }, { target := 311, numerator := 13878557518479033988829675520 }, { target := 338, numerator := 9385779219268306882187493376 }, { target := 339, numerator := 10308970617884861657484623872 }, { target := 340, numerator := 9385779219268306882187493376 }, { target := 341, numerator := 10308970617884861657484623872 }, { target := 589, numerator := 1412041857922460809250734080 }, { target := 590, numerator := 28240837158449216185014681600 }, { target := 591, numerator := 1462471924276834409581117440 }, { target := 592, numerator := 26274064570628645772129730560 }, { target := 593, numerator := 39335451756411408257699020800 }, { target := 594, numerator := 1412041857922460809250734080 }, { target := 595, numerator := 39385881822765781858029404160 }, { target := 596, numerator := 39385881822765781858029404160 }, { target := 597, numerator := 28190407092094842584684298240 }, { target := 598, numerator := 1462471924276834409581117440 }, { target := 599, numerator := 9385780344519695378470141952 }, { target := 600, numerator := 10308971853816714596024582144 }, { target := 601, numerator := 9385780344519695378470141952 }, { target := 602, numerator := 10308971853816714596024582144 }, { target := 773, numerator := 53512455031329217635680256 }, { target := 774, numerator := 58775975198345206255583232 }, { target := 775, numerator := 53512455031329217635680256 }, { target := 776, numerator := 58775975198345206255583232 }]

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
    Slot3.Left18.expected,
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
    Slot4.Left12.expected,
    Slot4.Left13.expected,
    Slot4.Left14.expected,
    Slot4.Left15.expected,
    Slot5.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 2149664577462521737148104704 }, { target := 81, numerator := 2448229102110094200640897024 }, { target := 82, numerator := 1910812957744463766353870848 }, { target := 83, numerator := 25616836214761717367681581056 }, { target := 84, numerator := 2269090387321550722545221632 }, { target := 85, numerator := 1910812957744463766353870848 }, { target := 86, numerator := 2269090387321550722545221632 }, { target := 87, numerator := 2209377482392036229846663168 }, { target := 88, numerator := 83478641091461260792584732672 }, { target := 89, numerator := 2209377482392036229846663168 }, { target := 90, numerator := 25616836214761717367681581056 }, { target := 91, numerator := 83478641091461260792584732672 }, { target := 92, numerator := 2149664577462521737148104704 }, { target := 93, numerator := 2209377482392036229846663168 }, { target := 94, numerator := 2209377482392036229846663168 }, { target := 95, numerator := 2448229102110094200640897024 }, { target := 263, numerator := 1392682544196052809261514752 }, { target := 265, numerator := 1392682544196052809261514752 }, { target := 338, numerator := 1044511908147039606946136064 }, { target := 340, numerator := 1044511908147039606946136064 }, { target := 352, numerator := 1102540347488541807332032512 }, { target := 354, numerator := 1102540347488541807332032512 }, { target := 479, numerator := 1421696763866803909454462976 }, { target := 481, numerator := 1421696763866803909454462976 }, { target := 554, numerator := 19033328104012721726574034944 }, { target := 556, numerator := 19033328104012721726574034944 }, { target := 568, numerator := 33279309962351511921311612928 }, { target := 570, numerator := 33279309962351511921311612928 }, { target := 599, numerator := 1015497688476288506753187840 }, { target := 601, numerator := 1015497688476288506753187840 }, { target := 613, numerator := 19033328104012721726574034944 }, { target := 615, numerator := 19033328104012721726574034944 }, { target := 618, numerator := 1073526127817790707139084288 }, { target := 620, numerator := 1073526127817790707139084288 }, { target := 694, numerator := 1102540347488541807332032512 }, { target := 696, numerator := 1102540347488541807332032512 }, { target := 708, numerator := 1102540347488541807332032512 }, { target := 710, numerator := 1102540347488541807332032512 }, { target := 739, numerator := 1073526127817790707139084288 }, { target := 741, numerator := 1073526127817790707139084288 }, { target := 753, numerator := 33279309962351511921311612928 }, { target := 755, numerator := 33279309962351511921311612928 }, { target := 758, numerator := 1073526127817790707139084288 }, { target := 760, numerator := 1073526127817790707139084288 }, { target := 763, numerator := 11946849331897254008586240 }, { target := 764, numerator := 238936986637945080171724800 }, { target := 765, numerator := 12373522522322155937464320 }, { target := 766, numerator := 222296732211373904945479680 }, { target := 767, numerator := 332805088531423504524902400 }, { target := 768, numerator := 11946849331897254008586240 }, { target := 769, numerator := 333231761721848406453780480 }, { target := 770, numerator := 333231761721848406453780480 }, { target := 771, numerator := 238510313447520178242846720 }, { target := 772, numerator := 12373522522322155937464320 }, { target := 773, numerator := 1392682544196052809261514752 }, { target := 775, numerator := 1392682544196052809261514752 }, { target := 778, numerator := 1421696763866803909454462976 }, { target := 780, numerator := 1421696763866803909454462976 }]

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
    Slot5.Left2.expected,
    Slot5.Left5.expected,
    Slot5.Left12.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left2.expected,
    Slot6.Left3.expected,
    Slot6.Left4.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 2484358718655871523588407296 }, { target := 134, numerator := 9074165720352801790781030400 }, { target := 136, numerator := 2484357881634859179017502720 }, { target := 176, numerator := 83848492778421758198833741824 }, { target := 177, numerator := 95494116775424780170893983744 }, { target := 178, numerator := 74531993580819340621185548288 }, { target := 179, numerator := 999194538942859285202768756736 }, { target := 180, numerator := 88506742377222966987657838592 }, { target := 181, numerator := 74531993580819340621185548288 }, { target := 182, numerator := 88506742377222966987657838592 }, { target := 183, numerator := 86177617577822362593245790208 }, { target := 184, numerator := 3256116469562044943388043640832 }, { target := 185, numerator := 86177617577822362593245790208 }, { target := 186, numerator := 999194538942859285202768756736 }, { target := 187, numerator := 3256116469562044943388043640832 }, { target := 188, numerator := 83848492778421758198833741824 }, { target := 189, numerator := 86177617577822362593245790208 }, { target := 190, numerator := 86177617577822362593245790208 }, { target := 191, numerator := 95494116775424780170893983744 }, { target := 227, numerator := 37265380779838072853826109440 }, { target := 230, numerator := 136112485805292026861715456000 }, { target := 232, numerator := 37265368224522887685262540800 }, { target := 253, numerator := 65421446257937950121161392128 }, { target := 256, numerator := 238953030635957113823900467200 }, { target := 258, numerator := 65421424216384625047460904960 }, { target := 286, numerator := 83848462023087701306583810048 }, { target := 287, numerator := 95494081748516548710276005888 }, { target := 288, numerator := 74531966242744623383630053376 }, { target := 289, numerator := 999194172441795107236790403072 }, { target := 290, numerator := 88506709913259240268060688384 }, { target := 291, numerator := 74531966242744623383630053376 }, { target := 292, numerator := 88506709913259240268060688384 }, { target := 293, numerator := 86177585968173470787322249216 }, { target := 294, numerator := 3256115275229905734072337956864 }, { target := 295, numerator := 86177585968173470787322249216 }, { target := 296, numerator := 999194172441795107236790403072 }, { target := 297, numerator := 3256115275229905734072337956864 }, { target := 298, numerator := 83848462023087701306583810048 }, { target := 299, numerator := 86177585968173470787322249216 }, { target := 300, numerator := 86177585968173470787322249216 }, { target := 301, numerator := 95494081748516548710276005888 }, { target := 302, numerator := 2484358718655871523588407296 }, { target := 305, numerator := 9074165720352801790781030400 }, { target := 307, numerator := 2484357881634859179017502720 }, { target := 328, numerator := 41405978644264525393140121600 }, { target := 331, numerator := 151236095339213363179683840000 }, { target := 333, numerator := 41405964693914319650291712000 }, { target := 573, numerator := 2149674829240540701231415296 }, { target := 574, numerator := 2448240777746171354180222976 }, { target := 575, numerator := 1910822070436036178872369152 }, { target := 576, numerator := 25616958381783110023007698944 }, { target := 577, numerator := 2269101208642792962410938368 }, { target := 578, numerator := 1910822070436036178872369152 }, { target := 579, numerator := 2269101208642792962410938368 }, { target := 580, numerator := 2209388018941666831821176832 }, { target := 581, numerator := 83479039202174330564486627328 }, { target := 582, numerator := 2209388018941666831821176832 }, { target := 583, numerator := 25616958381783110023007698944 }, { target := 584, numerator := 83479039202174330564486627328 }, { target := 585, numerator := 2149674829240540701231415296 }, { target := 586, numerator := 2209388018941666831821176832 }, { target := 587, numerator := 2209388018941666831821176832 }, { target := 588, numerator := 2448240777746171354180222976 }]

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
    Slot6.Left5.expected,
    Slot6.Left6.expected,
    Slot6.Left7.expected,
    Slot6.Left8.expected,
    Slot6.Left9.expected,
    Slot6.Left10.expected,
    Slot6.Left11.expected,
    Slot6.Left12.expected,
    Slot6.Left13.expected,
    Slot6.Left14.expected,
    Slot6.Left15.expected,
    Slot6.Left16.expected,
    Slot6.Left17.expected,
    Slot6.Left18.expected,
    Slot7.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 2463826828419046139095941120 }, { target := 27, numerator := 36957402426285692086439116800 }, { target := 28, numerator := 64880773148368214996193116160 }, { target := 29, numerator := 2463826828419046139095941120 }, { target := 30, numerator := 41063780473650768984932352000 }, { target := 31, numerator := 2463826828419046139095941120 }, { target := 32, numerator := 64880773148368214996193116160 }, { target := 33, numerator := 64470135343631707306343792640 }, { target := 34, numerator := 41063780473650768984932352000 }, { target := 35, numerator := 994975400876558132504910888960 }, { target := 36, numerator := 63648859734158691926645145600 }, { target := 37, numerator := 36957402426285692086439116800 }, { target := 38, numerator := 64880773148368214996193116160 }, { target := 39, numerator := 2463826828419046139095941120 }, { target := 40, numerator := 63648859734158691926645145600 }, { target := 41, numerator := 2463826828419046139095941120 }, { target := 42, numerator := 64880773148368214996193116160 }, { target := 43, numerator := 64880773148368214996193116160 }, { target := 44, numerator := 2463826828419046139095941120 }, { target := 342, numerator := 2484358718655871523588407296 }, { target := 345, numerator := 9074165720352801790781030400 }, { target := 347, numerator := 2484357881634859179017502720 }, { target := 443, numerator := 65421446257937950121161392128 }, { target := 446, numerator := 238953030635957113823900467200 }, { target := 448, numerator := 65421424216384625047460904960 }, { target := 469, numerator := 65007386471495304867229990912 }, { target := 472, numerator := 237440669682564980192103628800 }, { target := 474, numerator := 65007364569445481850957987840 }, { target := 518, numerator := 41405978644264525393140121600 }, { target := 521, numerator := 151236095339213363179683840000 }, { target := 523, numerator := 41405964693914319650291712000 }, { target := 544, numerator := 1003266862550529450275785146368 }, { target := 547, numerator := 3664450590069139789843739443200 }, { target := 549, numerator := 1003266524533543965126568181760 }, { target := 558, numerator := 64179266898610014359367188480 }, { target := 561, numerator := 234415947775780712928509952000 }, { target := 563, numerator := 64179245275567195457952153600 }, { target := 589, numerator := 37265380779838072853826109440 }, { target := 592, numerator := 136112485805292026861715456000 }, { target := 594, numerator := 37265368224522887685262540800 }, { target := 603, numerator := 65421446257937950121161392128 }, { target := 606, numerator := 238953030635957113823900467200 }, { target := 608, numerator := 65421424216384625047460904960 }, { target := 658, numerator := 2484358718655871523588407296 }, { target := 661, numerator := 9074165720352801790781030400 }, { target := 663, numerator := 2484357881634859179017502720 }, { target := 684, numerator := 64179266898610014359367188480 }, { target := 687, numerator := 234415947775780712928509952000 }, { target := 689, numerator := 64179245275567195457952153600 }, { target := 698, numerator := 2484358718655871523588407296 }, { target := 701, numerator := 9074165720352801790781030400 }, { target := 703, numerator := 2484357881634859179017502720 }, { target := 729, numerator := 65421446257937950121161392128 }, { target := 732, numerator := 238953030635957113823900467200 }, { target := 734, numerator := 65421424216384625047460904960 }, { target := 743, numerator := 65421446257937950121161392128 }, { target := 746, numerator := 238953030635957113823900467200 }, { target := 748, numerator := 65421424216384625047460904960 }, { target := 763, numerator := 2484358718655871523588407296 }, { target := 766, numerator := 9074165720352801790781030400 }, { target := 768, numerator := 2484357881634859179017502720 }]

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
    Slot7.Left3.expected,
    Slot7.Left5.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left2.expected,
    Slot8.Left3.expected,
    Slot8.Left4.expected,
    Slot8.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 2132258386551894030774435840 }, { target := 82, numerator := 83169557614224011168883671040 }, { target := 85, numerator := 83169527107920999271712686080 }, { target := 92, numerator := 2132268555319564663164764160 }, { target := 115, numerator := 2428405384684101535048663040 }, { target := 117, numerator := 94720885060644012720117514240 }, { target := 120, numerator := 94720850317354471392783892480 }, { target := 127, numerator := 2428416965780615310826536960 }, { target := 157, numerator := 8999172615225919131353088000 }, { target := 158, numerator := 134987589228388786970296320000 }, { target := 159, numerator := 236978212200949203792297984000 }, { target := 160, numerator := 8999172615225919131353088000 }, { target := 161, numerator := 149986210253765318855884800000 }, { target := 162, numerator := 8999172615225919131353088000 }, { target := 163, numerator := 236978212200949203792297984000 }, { target := 164, numerator := 235478350098411550603739136000 }, { target := 165, numerator := 149986210253765318855884800000 }, { target := 166, numerator := 3634165874448733675878088704000 }, { target := 167, numerator := 232478625893336244226621440000 }, { target := 168, numerator := 134987589228388786970296320000 }, { target := 169, numerator := 236978212200949203792297984000 }, { target := 170, numerator := 8999172615225919131353088000 }, { target := 171, numerator := 232478625893336244226621440000 }, { target := 172, numerator := 8999172615225919131353088000 }, { target := 173, numerator := 236978212200949203792297984000 }, { target := 174, numerator := 236978212200949203792297984000 }, { target := 175, numerator := 8999172615225919131353088000 }, { target := 176, numerator := 1895340788046128027355054080 }, { target := 178, numerator := 73928495657088009927896596480 }, { target := 181, numerator := 73928468540374221574855720960 }, { target := 188, numerator := 1895349826950724145035345920 }, { target := 211, numerator := 25409412439743403866728693760 }, { target := 213, numerator := 991103894902836133095863746560 }, { target := 216, numerator := 991103531369391907987909509120 }, { target := 223, numerator := 25409533617558145569380106240 }, { target := 237, numerator := 2250717185804777032484126720 }, { target := 239, numerator := 87790088592792011789377208320 }, { target := 242, numerator := 87790056391694388120141168640 }, { target := 249, numerator := 2250727919503984922229473280 }, { target := 267, numerator := 2463825998315562822166118400 }, { target := 268, numerator := 36957389974733442332491776000 }, { target := 269, numerator := 64880751288976487650374451200 }, { target := 270, numerator := 2463825998315562822166118400 }, { target := 271, numerator := 41063766638592713702768640000 }, { target := 272, numerator := 2463825998315562822166118400 }, { target := 273, numerator := 64880751288976487650374451200 }, { target := 274, numerator := 64470113622590560513346764800 }, { target := 275, numerator := 41063766638592713702768640000 }, { target := 276, numerator := 994975065653101453018084147200 }, { target := 277, numerator := 63648838289818706239291392000 }, { target := 278, numerator := 36957389974733442332491776000 }, { target := 279, numerator := 64880751288976487650374451200 }, { target := 280, numerator := 2463825998315562822166118400 }, { target := 281, numerator := 63648838289818706239291392000 }, { target := 282, numerator := 2463825998315562822166118400 }, { target := 283, numerator := 64880751288976487650374451200 }, { target := 284, numerator := 64880751288976487650374451200 }, { target := 285, numerator := 2463825998315562822166118400 }, { target := 286, numerator := 1895340788046128027355054080 }, { target := 288, numerator := 73928495657088009927896596480 }, { target := 291, numerator := 73928468540374221574855720960 }, { target := 298, numerator := 1895349826950724145035345920 }]

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
    Slot8.Left6.expected,
    Slot8.Left7.expected,
    Slot8.Left8.expected,
    Slot8.Left9.expected,
    Slot8.Left10.expected,
    Slot8.Left11.expected,
    Slot8.Left12.expected,
    Slot8.Left13.expected,
    Slot8.Left14.expected,
    Slot8.Left15.expected,
    Slot9.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 1392682544196052809261514752 }, { target := 11, numerator := 1044511908147039606946136064 }, { target := 12, numerator := 1102540347488541807332032512 }, { target := 13, numerator := 1421696763866803909454462976 }, { target := 14, numerator := 19033328104012721726574034944 }, { target := 15, numerator := 33279309962351511921311612928 }, { target := 16, numerator := 1015497688476288506753187840 }, { target := 17, numerator := 19033328104012721726574034944 }, { target := 18, numerator := 1073526127817790707139084288 }, { target := 19, numerator := 1102540347488541807332032512 }, { target := 20, numerator := 1102540347488541807332032512 }, { target := 21, numerator := 1073526127817790707139084288 }, { target := 22, numerator := 33279309962351511921311612928 }, { target := 23, numerator := 1073526127817790707139084288 }, { target := 24, numerator := 1392682544196052809261514752 }, { target := 25, numerator := 1421696763866803909454462976 }, { target := 312, numerator := 2250717185804777032484126720 }, { target := 314, numerator := 87790088592792011789377208320 }, { target := 317, numerator := 87790056391694388120141168640 }, { target := 324, numerator := 2250727919503984922229473280 }, { target := 392, numerator := 2191487786178335531629281280 }, { target := 394, numerator := 85479823103508011479130439680 }, { target := 397, numerator := 85479791749807693695926927360 }, { target := 404, numerator := 2191498237411774792697118720 }, { target := 427, numerator := 82802700677765218195073925120 }, { target := 429, numerator := 3229751154019032433724982558720 }, { target := 432, numerator := 3229749969357598805051509309440 }, { target := 439, numerator := 82803095564909761086231674880 }, { target := 453, numerator := 2191487786178335531629281280 }, { target := 455, numerator := 85479823103508011479130439680 }, { target := 458, numerator := 85479791749807693695926927360 }, { target := 465, numerator := 2191498237411774792697118720 }, { target := 502, numerator := 25409412439743403866728693760 }, { target := 504, numerator := 991103894902836133095863746560 }, { target := 507, numerator := 991103531369391907987909509120 }, { target := 514, numerator := 25409533617558145569380106240 }, { target := 528, numerator := 82802700677765218195073925120 }, { target := 530, numerator := 3229751154019032433724982558720 }, { target := 533, numerator := 3229749969357598805051509309440 }, { target := 540, numerator := 82803095564909761086231674880 }, { target := 573, numerator := 2132258386551894030774435840 }, { target := 575, numerator := 83169557614224011168883671040 }, { target := 578, numerator := 83169527107920999271712686080 }, { target := 585, numerator := 2132268555319564663164764160 }, { target := 642, numerator := 2191487786178335531629281280 }, { target := 644, numerator := 85479823103508011479130439680 }, { target := 647, numerator := 85479791749807693695926927360 }, { target := 654, numerator := 2191498237411774792697118720 }, { target := 668, numerator := 2191487786178335531629281280 }, { target := 670, numerator := 85479823103508011479130439680 }, { target := 673, numerator := 85479791749807693695926927360 }, { target := 680, numerator := 2191498237411774792697118720 }, { target := 713, numerator := 2428405384684101535048663040 }, { target := 715, numerator := 94720885060644012720117514240 }, { target := 718, numerator := 94720850317354471392783892480 }, { target := 725, numerator := 2428416965780615310826536960 }]

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
    Slot9.Left2.expected,
    Slot10.Left0.expected,
    Slot10.Left1.expected,
    Slot10.Left2.expected,
    Slot10.Left3.expected,
    Slot10.Left4.expected,
    Slot10.Left5.expected,
    Slot10.Left6.expected,
    Slot10.Left7.expected,
    Slot10.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 11946849331897254008586240 }, { target := 27, numerator := 1412040889468396939499274240 }, { target := 29, numerator := 13399986569565963851283824640 }, { target := 37, numerator := 1412041857922460809250734080 }, { target := 44, numerator := 11946849331897254008586240 }, { target := 61, numerator := 238936986637945080171724800 }, { target := 62, numerator := 28240817789367938789985484800 }, { target := 64, numerator := 267999731391319277025676492800 }, { target := 72, numerator := 28240837158449216185014681600 }, { target := 79, numerator := 238936986637945080171724800 }, { target := 96, numerator := 12373522522322155937464320 }, { target := 97, numerator := 1462470921235125401624248320 }, { target := 99, numerator := 13878557518479033988829675520 }, { target := 107, numerator := 1462471924276834409581117440 }, { target := 114, numerator := 12373522522322155937464320 }, { target := 141, numerator := 1392682544196052809261514752 }, { target := 142, numerator := 1044511908147039606946136064 }, { target := 143, numerator := 1102540347488541807332032512 }, { target := 144, numerator := 1421696763866803909454462976 }, { target := 145, numerator := 19033328104012721726574034944 }, { target := 146, numerator := 33279309962351511921311612928 }, { target := 147, numerator := 1015497688476288506753187840 }, { target := 148, numerator := 19033328104012721726574034944 }, { target := 149, numerator := 1073526127817790707139084288 }, { target := 150, numerator := 1102540347488541807332032512 }, { target := 151, numerator := 1102540347488541807332032512 }, { target := 152, numerator := 1073526127817790707139084288 }, { target := 153, numerator := 33279309962351511921311612928 }, { target := 154, numerator := 1073526127817790707139084288 }, { target := 155, numerator := 1392682544196052809261514752 }, { target := 156, numerator := 1421696763866803909454462976 }, { target := 157, numerator := 222296732211373904945479680 }, { target := 158, numerator := 26274046550465528767111495680 }, { target := 160, numerator := 249335464383709541661388308480 }, { target := 168, numerator := 26274064570628645772129730560 }, { target := 175, numerator := 222296732211373904945479680 }, { target := 192, numerator := 332805088531423504524902400 }, { target := 193, numerator := 39335424778048200457479782400 }, { target := 195, numerator := 373285340152194707285763686400 }, { target := 203, numerator := 39335451756411408257699020800 }, { target := 210, numerator := 332805088531423504524902400 }, { target := 267, numerator := 11946849331897254008586240 }, { target := 268, numerator := 1412040889468396939499274240 }, { target := 270, numerator := 13399986569565963851283824640 }, { target := 278, numerator := 1412041857922460809250734080 }, { target := 285, numerator := 11946849331897254008586240 }, { target := 373, numerator := 333231761721848406453780480 }, { target := 374, numerator := 39385854809814928919604756480 }, { target := 376, numerator := 373763911101107777423309537280 }, { target := 384, numerator := 39385881822765781858029404160 }, { target := 391, numerator := 333231761721848406453780480 }, { target := 408, numerator := 333231761721848406453780480 }, { target := 409, numerator := 39385854809814928919604756480 }, { target := 411, numerator := 373763911101107777423309537280 }, { target := 419, numerator := 39385881822765781858029404160 }, { target := 426, numerator := 333231761721848406453780480 }, { target := 483, numerator := 238510313447520178242846720 }, { target := 484, numerator := 28190387757601210327860510720 }, { target := 486, numerator := 267521160442406206888130641920 }, { target := 494, numerator := 28190407092094842584684298240 }, { target := 501, numerator := 238510313447520178242846720 }]

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
    Slot10.Left9.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected,
    Slot12.Left2.expected,
    Slot12.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 53513580282717713918328832 }, { target := 11, numerator := 9385779219268306882187493376 }, { target := 16, numerator := 9385780344519695378470141952 }, { target := 24, numerator := 53512455031329217635680256 }, { target := 45, numerator := 58777211130198144795541504 }, { target := 46, numerator := 10308970617884861657484623872 }, { target := 51, numerator := 10308971853816714596024582144 }, { target := 59, numerator := 58775975198345206255583232 }, { target := 141, numerator := 53513580282717713918328832 }, { target := 142, numerator := 9385779219268306882187493376 }, { target := 147, numerator := 9385780344519695378470141952 }, { target := 155, numerator := 53512455031329217635680256 }, { target := 357, numerator := 58777211130198144795541504 }, { target := 358, numerator := 10308970617884861657484623872 }, { target := 363, numerator := 10308971853816714596024582144 }, { target := 371, numerator := 58775975198345206255583232 }, { target := 623, numerator := 12373522522322155937464320 }, { target := 624, numerator := 1462470921235125401624248320 }, { target := 626, numerator := 13878557518479033988829675520 }, { target := 634, numerator := 1462471924276834409581117440 }, { target := 641, numerator := 12373522522322155937464320 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21.Parent3
