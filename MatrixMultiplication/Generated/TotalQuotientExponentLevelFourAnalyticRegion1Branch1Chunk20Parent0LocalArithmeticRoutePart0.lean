import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk20Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 82; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20.Parent0

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
  [{ target := 131, numerator := 6650051238572293357568000 }, { target := 132, numerator := 133001024771445867151360000 }, { target := 133, numerator := 6887553068521303834624000 }, { target := 134, numerator := 123738453403434458546176000 }, { target := 135, numerator := 185251427360228172103680000 }, { target := 136, numerator := 6650051238572293357568000 }, { target := 137, numerator := 185488929190177182580736000 }, { target := 138, numerator := 185488929190177182580736000 }, { target := 139, numerator := 132763522941496856674304000 }, { target := 140, numerator := 6887553068521303834624000 }, { target := 227, numerator := 2142123543873503254020096000 }, { target := 228, numerator := 42842470877470065080401920000 }, { target := 229, numerator := 2218627956154699798806528000 }, { target := 230, numerator := 39858798798503399833731072000 }, { target := 231, numerator := 59673441579333304933416960000 }, { target := 232, numerator := 2142123543873503254020096000 }, { target := 233, numerator := 59749945991614501478203392000 }, { target := 234, numerator := 59749945991614501478203392000 }, { target := 235, numerator := 42765966465188868535615488000 }, { target := 236, numerator := 2218627956154699798806528000 }, { target := 263, numerator := 47353954182089062700023808 }, { target := 264, numerator := 52011720167212577063960576 }, { target := 265, numerator := 47353954182089062700023808 }, { target := 266, numerator := 52011720167212577063960576 }, { target := 302, numerator := 22782384712783116620319948800 }, { target := 303, numerator := 455647694255662332406398976000 }, { target := 304, numerator := 23596041309668227928188518400 }, { target := 305, numerator := 423915086977142991399524761600 }, { target := 306, numerator := 634652145570386820137484288000 }, { target := 307, numerator := 22782384712783116620319948800 }, { target := 308, numerator := 635465802167271931445352857600 }, { target := 309, numerator := 635465802167271931445352857600 }, { target := 310, numerator := 454834037658777221098530406400 }, { target := 311, numerator := 23596041309668227928188518400 }, { target := 338, numerator := 9391938845368935533405798400 }, { target := 339, numerator := 10315736108847847225216204800 }, { target := 340, numerator := 9391938845368935533405798400 }, { target := 341, numerator := 10315736108847847225216204800 }, { target := 589, numerator := 2142130000233929052363161600 }, { target := 590, numerator := 42842600004678581047263232000 }, { target := 591, numerator := 2218634643099426518518988800 }, { target := 592, numerator := 39858918932924179867185971200 }, { target := 593, numerator := 59673621435088023601545216000 }, { target := 594, numerator := 2142130000233929052363161600 }, { target := 595, numerator := 59750126077953521067701043200 }, { target := 596, numerator := 59750126077953521067701043200 }, { target := 597, numerator := 42766095361813083581107404800 }, { target := 598, numerator := 2218634643099426518518988800 }, { target := 599, numerator := 9391938845368935533405798400 }, { target := 600, numerator := 10315736108847847225216204800 }, { target := 601, numerator := 9391938845368935533405798400 }, { target := 602, numerator := 10315736108847847225216204800 }, { target := 773, numerator := 47353954182089062700023808 }, { target := 774, numerator := 52011720167212577063960576 }, { target := 775, numerator := 47353954182089062700023808 }, { target := 776, numerator := 52011720167212577063960576 }]

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
    Slot4.Left6.expected,
    Slot4.Left14.expected,
    Slot6.Left0.expected,
    Slot6.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 7339046998733424545035714560 }, { target := 81, numerator := 8358359081890844620735119360 }, { target := 82, numerator := 6523597332207488484476190720 }, { target := 83, numerator := 87456976734906642495008931840 }, { target := 84, numerator := 7746771831996392575315476480 }, { target := 85, numerator := 6523597332207488484476190720 }, { target := 86, numerator := 7746771831996392575315476480 }, { target := 87, numerator := 7542909415364908560175595520 }, { target := 88, numerator := 284999658450814653165553582080 }, { target := 89, numerator := 7542909415364908560175595520 }, { target := 90, numerator := 87456976734906642495008931840 }, { target := 91, numerator := 284999658450814653165553582080 }, { target := 92, numerator := 7339046998733424545035714560 }, { target := 93, numerator := 7542909415364908560175595520 }, { target := 94, numerator := 7542909415364908560175595520 }, { target := 95, numerator := 8358359081890844620735119360 }, { target := 176, numerator := 287213311098731744613774655488 }, { target := 177, numerator := 327104048751333375810132246528 }, { target := 178, numerator := 255300720976650439656688582656 }, { target := 179, numerator := 3422625290593219956647481311232 }, { target := 180, numerator := 303169606159772397092317691904 }, { target := 181, numerator := 255300720976650439656688582656 }, { target := 182, numerator := 303169606159772397092317691904 }, { target := 183, numerator := 295191458629252070853046173696 }, { target := 184, numerator := 11153450247667416082501582454784 }, { target := 185, numerator := 295191458629252070853046173696 }, { target := 186, numerator := 3422625290593219956647481311232 }, { target := 187, numerator := 11153450247667416082501582454784 }, { target := 188, numerator := 287213311098731744613774655488 }, { target := 189, numerator := 295191458629252070853046173696 }, { target := 190, numerator := 295191458629252070853046173696 }, { target := 191, numerator := 327104048751333375810132246528 }, { target := 263, numerator := 1010617122716242728424833024 }, { target := 265, numerator := 1010617122716242728424833024 }, { target := 338, numerator := 177252748534378516857049055232 }, { target := 340, numerator := 177252748534378516857049055232 }, { target := 599, numerator := 177252769785027689770452516864 }, { target := 601, numerator := 177252769785027689770452516864 }, { target := 763, numerator := 6650051238572293357568000 }, { target := 764, numerator := 133001024771445867151360000 }, { target := 765, numerator := 6887553068521303834624000 }, { target := 766, numerator := 123738453403434458546176000 }, { target := 767, numerator := 185251427360228172103680000 }, { target := 768, numerator := 6650051238572293357568000 }, { target := 769, numerator := 185488929190177182580736000 }, { target := 770, numerator := 185488929190177182580736000 }, { target := 771, numerator := 132763522941496856674304000 }, { target := 772, numerator := 6887553068521303834624000 }, { target := 773, numerator := 1010595872067069815021371392 }, { target := 775, numerator := 1010595872067069815021371392 }]

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
    Slot6.Left5.expected,
    Slot6.Left12.expected,
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left3.expected,
    Slot7.Left11.expected,
    Slot7.Left18.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left2.expected,
    Slot8.Left3.expected,
    Slot8.Left4.expected,
    Slot8.Left5.expected,
    Slot8.Left6.expected,
    Slot8.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 131, numerator := 5709549742458446471227244544 }, { target := 134, numerator := 20854235003428318914124185600 }, { target := 136, numerator := 5709547818817923233957806080 }, { target := 227, numerator := 674832122916272978203817017344 }, { target := 230, numerator := 2464836688347812288932714905600 }, { target := 232, numerator := 674831895554313352816707502080 }, { target := 263, numerator := 21818690591413912952050286592 }, { target := 265, numerator := 21818695793395741738143842304 }, { target := 286, numerator := 287213311098731744613774655488 }, { target := 287, numerator := 327104048751333375810132246528 }, { target := 288, numerator := 255300720976650439656688582656 }, { target := 289, numerator := 3422625290593219956647481311232 }, { target := 290, numerator := 303169606159772397092317691904 }, { target := 291, numerator := 255300720976650439656688582656 }, { target := 292, numerator := 303169606159772397092317691904 }, { target := 293, numerator := 295191458629252070853046173696 }, { target := 294, numerator := 11153450247667416082501582454784 }, { target := 295, numerator := 295191458629252070853046173696 }, { target := 296, numerator := 3422625290593219956647481311232 }, { target := 297, numerator := 11153450247667416082501582454784 }, { target := 298, numerator := 287213311098731744613774655488 }, { target := 299, numerator := 295191458629252070853046173696 }, { target := 300, numerator := 295191458629252070853046173696 }, { target := 301, numerator := 327104048751333375810132246528 }, { target := 302, numerator := 6404022327706206493530164035584 }, { target := 305, numerator := 23390808840152467188232067481600 }, { target := 307, numerator := 6404020170086531218132571258880 }, { target := 338, numerator := 16364017943560434714037714944 }, { target := 340, numerator := 16364021845046806303607881728 }, { target := 352, numerator := 17273130051536014420373143552 }, { target := 354, numerator := 17273134169771628876030541824 }, { target := 479, numerator := 22273246645401702805218000896 }, { target := 481, numerator := 22273251955758153024355172352 }, { target := 554, numerator := 298188771415990143678020583424 }, { target := 556, numerator := 298188842509741803754632511488 }, { target := 568, numerator := 521375793923994961583368306688 }, { target := 570, numerator := 521375918229685745284395565056 }, { target := 573, numerator := 7339046998733424545035714560 }, { target := 574, numerator := 8358359081890844620735119360 }, { target := 575, numerator := 6523597332207488484476190720 }, { target := 576, numerator := 87456976734906642495008931840 }, { target := 577, numerator := 7746771831996392575315476480 }, { target := 578, numerator := 6523597332207488484476190720 }, { target := 579, numerator := 7746771831996392575315476480 }, { target := 580, numerator := 7542909415364908560175595520 }, { target := 581, numerator := 284999658450814653165553582080 }, { target := 582, numerator := 7542909415364908560175595520 }, { target := 583, numerator := 87456976734906642495008931840 }, { target := 584, numerator := 284999658450814653165553582080 }, { target := 585, numerator := 7339046998733424545035714560 }, { target := 586, numerator := 7542909415364908560175595520 }, { target := 587, numerator := 7542909415364908560175595520 }, { target := 588, numerator := 8358359081890844620735119360 }, { target := 589, numerator := 674832585752665849348958978048 }, { target := 592, numerator := 2464838378866213993562977075200 }, { target := 594, numerator := 674832358390550286824751759360 }, { target := 599, numerator := 15909461889572644860870000640 }, { target := 601, numerator := 15909465682684395017396551680 }, { target := 613, numerator := 298188771415990143678020583424 }, { target := 615, numerator := 298188842509741803754632511488 }, { target := 763, numerator := 5709549742458446471227244544 }, { target := 766, numerator := 20854235003428318914124185600 }, { target := 768, numerator := 5709547818817923233957806080 }]

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
    Slot8.Left8.expected,
    Slot8.Left9.expected,
    Slot8.Left10.expected,
    Slot8.Left11.expected,
    Slot8.Left12.expected,
    Slot8.Left13.expected,
    Slot8.Left14.expected,
    Slot8.Left15.expected,
    Slot9.Left0.expected,
    Slot9.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 15904251135164130213815648256 }, { target := 27, numerator := 238563767027461953207234723840 }, { target := 28, numerator := 418811946559322095630478737408 }, { target := 29, numerator := 15904251135164130213815648256 }, { target := 30, numerator := 265070852252735503563594137600 }, { target := 31, numerator := 15904251135164130213815648256 }, { target := 32, numerator := 418811946559322095630478737408 }, { target := 33, numerator := 416161238036794740594842796032 }, { target := 34, numerator := 265070852252735503563594137600 }, { target := 35, numerator := 6422666750083781251345885954048 }, { target := 36, numerator := 410859820991740030523570913280 }, { target := 37, numerator := 238563767027461953207234723840 }, { target := 38, numerator := 418811946559322095630478737408 }, { target := 39, numerator := 15904251135164130213815648256 }, { target := 40, numerator := 410859820991740030523570913280 }, { target := 41, numerator := 15904251135164130213815648256 }, { target := 42, numerator := 418811946559322095630478737408 }, { target := 43, numerator := 418811946559322095630478737408 }, { target := 44, numerator := 15904251135164130213815648256 }, { target := 157, numerator := 57207118373791350763624071168 }, { target := 158, numerator := 858106775606870261454361067520 }, { target := 159, numerator := 1506454117176505570108767207424 }, { target := 160, numerator := 57207118373791350763624071168 }, { target := 161, numerator := 953451972896522512727067852800 }, { target := 162, numerator := 57207118373791350763624071168 }, { target := 163, numerator := 1506454117176505570108767207424 }, { target := 164, numerator := 1496919597447540344981496528896 }, { target := 165, numerator := 953451972896522512727067852800 }, { target := 166, numerator := 23102141303282740483376854073344 }, { target := 167, numerator := 1477850557989609894726955171840 }, { target := 168, numerator := 858106775606870261454361067520 }, { target := 169, numerator := 1506454117176505570108767207424 }, { target := 170, numerator := 57207118373791350763624071168 }, { target := 171, numerator := 1477850557989609894726955171840 }, { target := 172, numerator := 57207118373791350763624071168 }, { target := 173, numerator := 1506454117176505570108767207424 }, { target := 174, numerator := 1506454117176505570108767207424 }, { target := 175, numerator := 57207118373791350763624071168 }, { target := 618, numerator := 16818573997548224567205429248 }, { target := 620, numerator := 16818578007409217589819211776 }, { target := 694, numerator := 17273130051536014420373143552 }, { target := 696, numerator := 17273134169771628876030541824 }, { target := 708, numerator := 17273130051536014420373143552 }, { target := 710, numerator := 17273134169771628876030541824 }, { target := 739, numerator := 16818573997548224567205429248 }, { target := 741, numerator := 16818578007409217589819211776 }, { target := 753, numerator := 521375793923994961583368306688 }, { target := 755, numerator := 521375918229685745284395565056 }, { target := 758, numerator := 16818573997548224567205429248 }, { target := 760, numerator := 16818578007409217589819211776 }, { target := 773, numerator := 21818690591413912952050286592 }, { target := 775, numerator := 21818695793395741738143842304 }, { target := 778, numerator := 22273246645401702805218000896 }, { target := 780, numerator := 22273251955758153024355172352 }]

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
    Slot9.Left5.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left1.expected,
    Slot11.Left2.expected,
    Slot11.Left3.expected,
    Slot11.Left4.expected,
    Slot11.Left5.expected,
    Slot11.Left6.expected,
    Slot11.Left7.expected,
    Slot11.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 80, numerator := 31422845153393468386255568896 }, { target := 82, numerator := 1225660148352941351827486539776 }, { target := 85, numerator := 1225659698785083257713854513152 }, { target := 92, numerator := 31422995009346166424132911104 }, { target := 131, numerator := 16173814713726234115744727040 }, { target := 134, numerator := 58176730549618322810465157120 }, { target := 136, numerator := 16173820109398875675788574720 }, { target := 176, numerator := 1225660148352941351827486539776 }, { target := 178, numerator := 47807345004159226786455859757056 }, { target := 181, numerator := 47807327468592190876628090355712 }, { target := 188, numerator := 1225665993541953321770076340224 }, { target := 227, numerator := 242607220705893511736170905600 }, { target := 230, numerator := 872650958244274842156977356800 }, { target := 232, numerator := 242607301640983135136828620800 }, { target := 253, numerator := 425910454128124165047944478720 }, { target := 256, numerator := 1531987237806615834008915804160 }, { target := 258, numerator := 425910596214170392795765800960 }, { target := 267, numerator := 15904256440908894414525431808 }, { target := 268, numerator := 238563846613633416217881477120 }, { target := 269, numerator := 418812086277267552915836370944 }, { target := 270, numerator := 15904256440908894414525431808 }, { target := 271, numerator := 265070940681814906908757196800 }, { target := 272, numerator := 15904256440908894414525431808 }, { target := 273, numerator := 418812086277267552915836370944 }, { target := 274, numerator := 416161376870449403846748798976 }, { target := 275, numerator := 265070940681814906908757196800 }, { target := 276, numerator := 6422668892720375194399186878464 }, { target := 277, numerator := 410859958056813105708573655040 }, { target := 278, numerator := 238563846613633416217881477120 }, { target := 279, numerator := 418812086277267552915836370944 }, { target := 280, numerator := 15904256440908894414525431808 }, { target := 281, numerator := 410859958056813105708573655040 }, { target := 282, numerator := 15904256440908894414525431808 }, { target := 283, numerator := 418812086277267552915836370944 }, { target := 284, numerator := 418812086277267552915836370944 }, { target := 285, numerator := 15904256440908894414525431808 }, { target := 286, numerator := 1225659698785083257713854513152 }, { target := 288, numerator := 47807327468592190876628090355712 }, { target := 291, numerator := 47807309933031586951493136154624 }, { target := 298, numerator := 1225665543971951232758839246848 }, { target := 302, numerator := 16173814713726234115744727040 }, { target := 305, numerator := 58176730549618322810465157120 }, { target := 307, numerator := 16173820109398875675788574720 }, { target := 328, numerator := 269563578562103901929078784000 }, { target := 331, numerator := 969612175826972046841085952000 }, { target := 333, numerator := 269563668489981261263142912000 }, { target := 342, numerator := 16173814713726234115744727040 }, { target := 345, numerator := 58176730549618322810465157120 }, { target := 347, numerator := 16173820109398875675788574720 }, { target := 443, numerator := 425910454128124165047944478720 }, { target := 446, numerator := 1531987237806615834008915804160 }, { target := 448, numerator := 425910596214170392795765800960 }, { target := 469, numerator := 423214818342503126028653690880 }, { target := 472, numerator := 1522291116048346113540504944640 }, { target := 474, numerator := 423214959529270580183134371840 }, { target := 518, numerator := 269563578562103901929078784000 }, { target := 521, numerator := 969612175826972046841085952000 }, { target := 523, numerator := 269563668489981261263142912000 }, { target := 573, numerator := 31422995009346166424132911104 }, { target := 575, numerator := 1225665993541953321770076340224 }, { target := 578, numerator := 1225665543971951232758839246848 }, { target := 585, numerator := 31423144866013529427878608896 }]

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
    Slot11.Left9.expected,
    Slot11.Left10.expected,
    Slot11.Left11.expected,
    Slot11.Left12.expected,
    Slot11.Left13.expected,
    Slot11.Left14.expected,
    Slot11.Left15.expected,
    Slot11.Left16.expected,
    Slot11.Left17.expected,
    Slot11.Left18.expected,
    Slot12.Left0.expected,
    Slot12.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 22282918050805698334008803328 }, { target := 11, numerator := 16712188538104273750506602496 }, { target := 12, numerator := 17640643456887844514423635968 }, { target := 13, numerator := 22747145510197483715967320064 }, { target := 14, numerator := 304533213361011210564786978816 }, { target := 15, numerator := 532468895922377833106418696192 }, { target := 16, numerator := 16247961078712488368548085760 }, { target := 17, numerator := 304533213361011210564786978816 }, { target := 18, numerator := 17176415997496059132465119232 }, { target := 19, numerator := 17640643456887844514423635968 }, { target := 20, numerator := 17640643456887844514423635968 }, { target := 21, numerator := 17176415997496059132465119232 }, { target := 22, numerator := 532468895922377833106418696192 }, { target := 23, numerator := 17176415997496059132465119232 }, { target := 24, numerator := 22282918050805698334008803328 }, { target := 25, numerator := 22747145510197483715967320064 }, { target := 141, numerator := 22282923363467991562359668736 }, { target := 142, numerator := 16712192522600993671769751552 }, { target := 143, numerator := 17640647662745493320201404416 }, { target := 144, numerator := 22747150933540241386575495168 }, { target := 145, numerator := 304533285967395884685582139392 }, { target := 146, numerator := 532469022872870548375552917504 }, { target := 147, numerator := 16247964952528743847553925120 }, { target := 148, numerator := 304533285967395884685582139392 }, { target := 149, numerator := 17176420092673243495985577984 }, { target := 150, numerator := 17640647662745493320201404416 }, { target := 151, numerator := 17640647662745493320201404416 }, { target := 152, numerator := 17176420092673243495985577984 }, { target := 153, numerator := 532469022872870548375552917504 }, { target := 154, numerator := 17176420092673243495985577984 }, { target := 155, numerator := 22282923363467991562359668736 }, { target := 156, numerator := 22747150933540241386575495168 }, { target := 544, numerator := 6531525508559777543741578936320 }, { target := 547, numerator := 23493703020287532694959512616960 }, { target := 549, numerator := 6531527687512245960405952757760 }, { target := 558, numerator := 417823546771261047990072115200 }, { target := 561, numerator := 1502898872531806672603683225600 }, { target := 563, numerator := 417823686159470954957871513600 }, { target := 589, numerator := 242607220705893511736170905600 }, { target := 592, numerator := 872650958244274842156977356800 }, { target := 594, numerator := 242607301640983135136828620800 }, { target := 603, numerator := 425910454128124165047944478720 }, { target := 606, numerator := 1531987237806615834008915804160 }, { target := 608, numerator := 425910596214170392795765800960 }, { target := 658, numerator := 16173814713726234115744727040 }, { target := 661, numerator := 58176730549618322810465157120 }, { target := 663, numerator := 16173820109398875675788574720 }, { target := 684, numerator := 417823546771261047990072115200 }, { target := 687, numerator := 1502898872531806672603683225600 }, { target := 689, numerator := 417823686159470954957871513600 }, { target := 698, numerator := 16173814713726234115744727040 }, { target := 701, numerator := 58176730549618322810465157120 }, { target := 703, numerator := 16173820109398875675788574720 }, { target := 729, numerator := 425910454128124165047944478720 }, { target := 732, numerator := 1531987237806615834008915804160 }, { target := 734, numerator := 425910596214170392795765800960 }, { target := 743, numerator := 425910454128124165047944478720 }, { target := 746, numerator := 1531987237806615834008915804160 }, { target := 748, numerator := 425910596214170392795765800960 }, { target := 763, numerator := 16173814713726234115744727040 }, { target := 766, numerator := 58176730549618322810465157120 }, { target := 768, numerator := 16173820109398875675788574720 }]

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
    Slot13.Left0.expected,
    Slot13.Left3.expected,
    Slot13.Left5.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left2.expected,
    Slot14.Left3.expected,
    Slot14.Left4.expected,
    Slot14.Left5.expected,
    Slot14.Left6.expected,
    Slot14.Left7.expected,
    Slot14.Left8.expected,
    Slot14.Left9.expected,
    Slot14.Left10.expected,
    Slot14.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 26, numerator := 5781692067724166914004484096 }, { target := 27, numerator := 683358882592110362404948279296 }, { target := 29, numerator := 6484939577334263254278740115456 }, { target := 37, numerator := 683359351276616500875028856832 }, { target := 44, numerator := 5781692067724166914004484096 }, { target := 80, numerator := 7313022009376213819698708480 }, { target := 82, numerator := 286194824179941915732165525504 }, { target := 85, numerator := 286194824179941915732165525504 }, { target := 92, numerator := 7313022009376213819698708480 }, { target := 115, numerator := 8328719510678465739101306880 }, { target := 117, numerator := 325944105316044959583855181824 }, { target := 120, numerator := 325944105316044959583855181824 }, { target := 127, numerator := 8328719510678465739101306880 }, { target := 157, numerator := 21117736167731564820981350400 }, { target := 158, numerator := 2495980834229463346735113830400 }, { target := 160, numerator := 23686360576399881033570739814400 }, { target := 168, numerator := 2495982546108205867127852236800 }, { target := 175, numerator := 21117736167731564820981350400 }, { target := 176, numerator := 6500464008334412284176629760 }, { target := 178, numerator := 254395399271059480650813800448 }, { target := 181, numerator := 254395399271059480650813800448 }, { target := 188, numerator := 6500464008334412284176629760 }, { target := 211, numerator := 87146845611733214684742942720 }, { target := 213, numerator := 3410488321477641162474972512256 }, { target := 216, numerator := 3410488321477641162474972512256 }, { target := 223, numerator := 87146845611733214684742942720 }, { target := 237, numerator := 7719301009897114587459747840 }, { target := 239, numerator := 302094536634383133272841388032 }, { target := 242, numerator := 302094536634383133272841388032 }, { target := 249, numerator := 7719301009897114587459747840 }, { target := 267, numerator := 5781690119777716487816478720 }, { target := 268, numerator := 683358652357346193014752542720 }, { target := 270, numerator := 6484937392452245511502477393920 }, { target := 278, numerator := 683359121041694424022898442240 }, { target := 285, numerator := 5781690119777716487816478720 }, { target := 286, numerator := 6500464008334412284176629760 }, { target := 288, numerator := 254395399271059480650813800448 }, { target := 291, numerator := 254395399271059480650813800448 }, { target := 298, numerator := 6500464008334412284176629760 }, { target := 312, numerator := 7719301009897114587459747840 }, { target := 314, numerator := 302094536634383133272841388032 }, { target := 317, numerator := 302094536634383133272841388032 }, { target := 324, numerator := 7719301009897114587459747840 }, { target := 392, numerator := 7516161509636664203579228160 }, { target := 394, numerator := 294144680407162524502503456768 }, { target := 397, numerator := 294144680407162524502503456768 }, { target := 404, numerator := 7516161509636664203579228160 }, { target := 427, numerator := 283989021364109636664966512640 }, { target := 429, numerator := 11113899005654411060932427907072 }, { target := 432, numerator := 11113899005654411060932427907072 }, { target := 439, numerator := 283989021364109636664966512640 }, { target := 453, numerator := 7516161509636664203579228160 }, { target := 455, numerator := 294144680407162524502503456768 }, { target := 458, numerator := 294144680407162524502503456768 }, { target := 465, numerator := 7516161509636664203579228160 }, { target := 502, numerator := 87146845611733214684742942720 }, { target := 504, numerator := 3410488321477641162474972512256 }, { target := 507, numerator := 3410488321477641162474972512256 }, { target := 514, numerator := 87146845611733214684742942720 }, { target := 528, numerator := 283989021364109636664966512640 }, { target := 530, numerator := 11113899005654411060932427907072 }, { target := 533, numerator := 11113899005654411060932427907072 }, { target := 540, numerator := 283989021364109636664966512640 }]

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
    Slot14.Left12.expected,
    Slot14.Left13.expected,
    Slot14.Left14.expected,
    Slot14.Left15.expected,
    Slot16.Left0.expected,
    Slot16.Left2.expected,
    Slot17.Left0.expected,
    Slot17.Left1.expected,
    Slot17.Left2.expected,
    Slot17.Left3.expected,
    Slot17.Left4.expected,
    Slot17.Left5.expected,
    Slot17.Left6.expected,
    Slot17.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 898326331303326869710962688 }, { target := 11, numerator := 157557998697225348317376937984 }, { target := 16, numerator := 157558017586691279795957792768 }, { target := 24, numerator := 898307441837395391130107904 }, { target := 26, numerator := 6783052263343739224719360 }, { target := 27, numerator := 2184966014750973319100497920 }, { target := 29, numerator := 23238032407038778952726347776 }, { target := 37, numerator := 2184972600238607633410424832 }, { target := 44, numerator := 6783052263343739224719360 }, { target := 61, numerator := 135661045266874784494387200 }, { target := 62, numerator := 43699320295019466382009958400 }, { target := 64, numerator := 464760648140775579054526955520 }, { target := 72, numerator := 43699452004772152668208496640 }, { target := 79, numerator := 135661045266874784494387200 }, { target := 96, numerator := 7025304129891729911316480 }, { target := 97, numerator := 2263000515277793794782658560 }, { target := 99, numerator := 24067962135861592486752288768 }, { target := 107, numerator := 2263007335961415048889368576 }, { target := 114, numerator := 7025304129891729911316480 }, { target := 141, numerator := 898326331303326869710962688 }, { target := 142, numerator := 157557998697225348317376937984 }, { target := 147, numerator := 157558017586691279795957792768 }, { target := 155, numerator := 898307441837395391130107904 }, { target := 157, numerator := 126213222471503147717099520 }, { target := 158, numerator := 40655974774473467830405693440 }, { target := 160, numerator := 432393388716685851227515256832 }, { target := 168, numerator := 40656097311582663464529690624 }, { target := 175, numerator := 126213222471503147717099520 }, { target := 192, numerator := 188956455907432735545753600 }, { target := 193, numerator := 60866910410919971032085299200 }, { target := 195, numerator := 647345188481794556540233973760 }, { target := 203, numerator := 60867093863789784073576120320 }, { target := 210, numerator := 188956455907432735545753600 }, { target := 267, numerator := 6783052263343739224719360 }, { target := 268, numerator := 2184966014750973319100497920 }, { target := 270, numerator := 23238032407038778952726347776 }, { target := 278, numerator := 2184972600238607633410424832 }, { target := 285, numerator := 6783052263343739224719360 }, { target := 373, numerator := 189198707773980726232350720 }, { target := 374, numerator := 60944944911446791507767459840 }, { target := 376, numerator := 648175118210617370074259914752 }, { target := 384, numerator := 60945128599512591489055064064 }, { target := 391, numerator := 189198707773980726232350720 }, { target := 408, numerator := 189198707773980726232350720 }, { target := 409, numerator := 60944944911446791507767459840 }, { target := 411, numerator := 648175118210617370074259914752 }, { target := 419, numerator := 60945128599512591489055064064 }, { target := 426, numerator := 189198707773980726232350720 }, { target := 573, numerator := 7313022009376213819698708480 }, { target := 575, numerator := 286194824179941915732165525504 }, { target := 578, numerator := 286194824179941915732165525504 }, { target := 585, numerator := 7313022009376213819698708480 }, { target := 642, numerator := 7516161509636664203579228160 }, { target := 644, numerator := 294144680407162524502503456768 }, { target := 647, numerator := 294144680407162524502503456768 }, { target := 654, numerator := 7516161509636664203579228160 }, { target := 668, numerator := 7516161509636664203579228160 }, { target := 670, numerator := 294144680407162524502503456768 }, { target := 673, numerator := 294144680407162524502503456768 }, { target := 680, numerator := 7516161509636664203579228160 }, { target := 713, numerator := 8328719510678465739101306880 }, { target := 715, numerator := 325944105316044959583855181824 }, { target := 718, numerator := 325944105316044959583855181824 }, { target := 725, numerator := 8328719510678465739101306880 }]

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
    Slot17.Left8.expected,
    Slot17.Left9.expected,
    Slot19.Left0.expected,
    Slot19.Left1.expected,
    Slot19.Left2.expected,
    Slot19.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 47353954182089062700023808 }, { target := 11, numerator := 9391938845368935533405798400 }, { target := 16, numerator := 9391938845368935533405798400 }, { target := 24, numerator := 47353954182089062700023808 }, { target := 45, numerator := 52011720167212577063960576 }, { target := 46, numerator := 10315736108847847225216204800 }, { target := 51, numerator := 10315736108847847225216204800 }, { target := 59, numerator := 52011720167212577063960576 }, { target := 141, numerator := 47353954182089062700023808 }, { target := 142, numerator := 9391938845368935533405798400 }, { target := 147, numerator := 9391938845368935533405798400 }, { target := 155, numerator := 47353954182089062700023808 }, { target := 357, numerator := 52011720167212577063960576 }, { target := 358, numerator := 10315736108847847225216204800 }, { target := 363, numerator := 10315736108847847225216204800 }, { target := 371, numerator := 52011720167212577063960576 }, { target := 483, numerator := 135418793400326793807790080 }, { target := 484, numerator := 43621285794492645906327797760 }, { target := 486, numerator := 463930718411952765520501014528 }, { target := 494, numerator := 43621417269049345252729552896 }, { target := 501, numerator := 135418793400326793807790080 }, { target := 623, numerator := 7025304129891729911316480 }, { target := 624, numerator := 2263000515277793794782658560 }, { target := 626, numerator := 24067962135861592486752288768 }, { target := 634, numerator := 2263007335961415048889368576 }, { target := 641, numerator := 7025304129891729911316480 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20.Parent0
