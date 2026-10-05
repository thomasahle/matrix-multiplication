import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk5Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 23; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot0.Left1.expected,
    Slot0.Left2.expected,
    Slot0.Left3.expected,
    Slot0.Left4.expected,
    Slot0.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 11, numerator := 5270160994882524058484736 }, { target := 12, numerator := 127673900230863727997485056 }, { target := 13, numerator := 96732955035101812557348864 }, { target := 14, numerator := 107783292605016782357397504 }, { target := 15, numerator := 5270160994882524058484736 }, { target := 16, numerator := 107783292605016782357397504 }, { target := 17, numerator := 107613287411633475129704448 }, { target := 18, numerator := 5270160994882524058484736 }, { target := 19, numerator := 127673900230863727997485056 }, { target := 20, numerator := 5270160994882524058484736 }, { target := 31, numerator := 76417334425796598848028672 }, { target := 32, numerator := 1851271553347524055963533312 }, { target := 33, numerator := 1402627848008976282081558528 }, { target := 34, numerator := 1562857742772743344182263808 }, { target := 35, numerator := 76417334425796598848028672 }, { target := 36, numerator := 1562857742772743344182263808 }, { target := 37, numerator := 1560392667468685389380714496 }, { target := 38, numerator := 76417334425796598848028672 }, { target := 39, numerator := 1851271553347524055963533312 }, { target := 40, numerator := 76417334425796598848028672 }, { target := 45, numerator := 135267465535318117501108224 }, { target := 46, numerator := 3276963439258835685268783104 }, { target := 47, numerator := 2482812512567613188971954176 }, { target := 48, numerator := 2766437843528764080506535936 }, { target := 49, numerator := 135267465535318117501108224 }, { target := 50, numerator := 2766437843528764080506535936 }, { target := 51, numerator := 2762074376898592528329080832 }, { target := 52, numerator := 135267465535318117501108224 }, { target := 53, numerator := 3276963439258835685268783104 }, { target := 54, numerator := 135267465535318117501108224 }, { target := 76, numerator := 4391800829068770048737280 }, { target := 77, numerator := 106394916859053106664570880 }, { target := 78, numerator := 80610795862584843797790720 }, { target := 79, numerator := 89819410504180651964497920 }, { target := 80, numerator := 4391800829068770048737280 }, { target := 81, numerator := 89819410504180651964497920 }, { target := 82, numerator := 89677739509694562608087040 }, { target := 83, numerator := 4391800829068770048737280 }, { target := 84, numerator := 106394916859053106664570880 }, { target := 85, numerator := 4391800829068770048737280 }, { target := 90, numerator := 84322575918120384935755776 }, { target := 91, numerator := 2042782403693819647959760896 }, { target := 92, numerator := 1547727280561629000917581824 }, { target := 93, numerator := 1724532681680268517718360064 }, { target := 94, numerator := 84322575918120384935755776 }, { target := 95, numerator := 1724532681680268517718360064 }, { target := 96, numerator := 1721812598586135602075271168 }, { target := 97, numerator := 84322575918120384935755776 }, { target := 98, numerator := 2042782403693819647959760896 }, { target := 99, numerator := 84322575918120384935755776 }, { target := 116, numerator := 4391800829068770048737280 }, { target := 117, numerator := 106394916859053106664570880 }, { target := 118, numerator := 80610795862584843797790720 }, { target := 119, numerator := 89819410504180651964497920 }, { target := 120, numerator := 4391800829068770048737280 }, { target := 121, numerator := 89819410504180651964497920 }, { target := 122, numerator := 89677739509694562608087040 }, { target := 123, numerator := 4391800829068770048737280 }, { target := 124, numerator := 106394916859053106664570880 }, { target := 125, numerator := 4391800829068770048737280 }]

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
    Slot0.Left6.expected,
    Slot0.Left7.expected,
    Slot0.Left8.expected,
    Slot0.Left9.expected,
    Slot0.Left10.expected,
    Slot0.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 171, numerator := 134389105369504363491360768 }, { target := 172, numerator := 3255684455887025063935868928 }, { target := 173, numerator := 2466690353395096220212396032 }, { target := 174, numerator := 2748473961427927950113636352 }, { target := 175, numerator := 134389105369504363491360768 }, { target := 176, numerator := 2748473961427927950113636352 }, { target := 177, numerator := 2744138828996653615807463424 }, { target := 178, numerator := 134389105369504363491360768 }, { target := 179, numerator := 3255684455887025063935868928 }, { target := 180, numerator := 134389105369504363491360768 }, { target := 185, numerator := 140537626530200641559592960 }, { target := 186, numerator := 3404637339489699413266268160 }, { target := 187, numerator := 2579545467602715001529303040 }, { target := 188, numerator := 2874221136133780862863933440 }, { target := 189, numerator := 140537626530200641559592960 }, { target := 190, numerator := 2874221136133780862863933440 }, { target := 191, numerator := 2869687664310226003458785280 }, { target := 192, numerator := 140537626530200641559592960 }, { target := 193, numerator := 3404637339489699413266268160 }, { target := 194, numerator := 140537626530200641559592960 }, { target := 216, numerator := 84322575918120384935755776 }, { target := 217, numerator := 2042782403693819647959760896 }, { target := 218, numerator := 1547727280561629000917581824 }, { target := 219, numerator := 1724532681680268517718360064 }, { target := 220, numerator := 84322575918120384935755776 }, { target := 221, numerator := 1724532681680268517718360064 }, { target := 222, numerator := 1721812598586135602075271168 }, { target := 223, numerator := 84322575918120384935755776 }, { target := 224, numerator := 2042782403693819647959760896 }, { target := 225, numerator := 84322575918120384935755776 }, { target := 230, numerator := 2152860766409511077891014656 }, { target := 231, numerator := 52154788244307832886972645376 }, { target := 232, numerator := 39515412131839090429677010944 }, { target := 233, numerator := 44029475029149355592996880384 }, { target := 234, numerator := 2152860766409511077891014656 }, { target := 235, numerator := 44029475029149355592996880384 }, { target := 236, numerator := 43960027907652274590484267008 }, { target := 237, numerator := 2152860766409511077891014656 }, { target := 238, numerator := 52154788244307832886972645376 }, { target := 239, numerator := 2152860766409511077891014656 }, { target := 256, numerator := 137902546032759379530350592 }, { target := 257, numerator := 3340800389374267549267525632 }, { target := 258, numerator := 2531178990085164095250628608 }, { target := 259, numerator := 2820329489831272471685234688 }, { target := 260, numerator := 137902546032759379530350592 }, { target := 261, numerator := 2820329489831272471685234688 }, { target := 262, numerator := 2815881020604409265893933056 }, { target := 263, numerator := 137902546032759379530350592 }, { target := 264, numerator := 3340800389374267549267525632 }, { target := 265, numerator := 137902546032759379530350592 }, { target := 305, numerator := 76417334425796598848028672 }, { target := 306, numerator := 1851271553347524055963533312 }, { target := 307, numerator := 1402627848008976282081558528 }, { target := 308, numerator := 1562857742772743344182263808 }, { target := 309, numerator := 76417334425796598848028672 }, { target := 310, numerator := 1562857742772743344182263808 }, { target := 311, numerator := 1560392667468685389380714496 }, { target := 312, numerator := 76417334425796598848028672 }, { target := 313, numerator := 1851271553347524055963533312 }, { target := 314, numerator := 76417334425796598848028672 }]

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
    Slot0.Left12.expected,
    Slot0.Left13.expected,
    Slot0.Left14.expected,
    Slot0.Left15.expected,
    Slot0.Left16.expected,
    Slot0.Left17.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 331, numerator := 134389105369504363491360768 }, { target := 332, numerator := 3255684455887025063935868928 }, { target := 333, numerator := 2466690353395096220212396032 }, { target := 334, numerator := 2748473961427927950113636352 }, { target := 335, numerator := 134389105369504363491360768 }, { target := 336, numerator := 2748473961427927950113636352 }, { target := 337, numerator := 2744138828996653615807463424 }, { target := 338, numerator := 134389105369504363491360768 }, { target := 339, numerator := 3255684455887025063935868928 }, { target := 340, numerator := 134389105369504363491360768 }, { target := 432, numerator := 4391800829068770048737280 }, { target := 433, numerator := 106394916859053106664570880 }, { target := 434, numerator := 80610795862584843797790720 }, { target := 435, numerator := 89819410504180651964497920 }, { target := 436, numerator := 4391800829068770048737280 }, { target := 437, numerator := 89819410504180651964497920 }, { target := 438, numerator := 89677739509694562608087040 }, { target := 439, numerator := 4391800829068770048737280 }, { target := 440, numerator := 106394916859053106664570880 }, { target := 441, numerator := 4391800829068770048737280 }, { target := 446, numerator := 137902546032759379530350592 }, { target := 447, numerator := 3340800389374267549267525632 }, { target := 448, numerator := 2531178990085164095250628608 }, { target := 449, numerator := 2820329489831272471685234688 }, { target := 450, numerator := 137902546032759379530350592 }, { target := 451, numerator := 2820329489831272471685234688 }, { target := 452, numerator := 2815881020604409265893933056 }, { target := 453, numerator := 137902546032759379530350592 }, { target := 454, numerator := 3340800389374267549267525632 }, { target := 455, numerator := 137902546032759379530350592 }, { target := 472, numerator := 4391800829068770048737280 }, { target := 473, numerator := 106394916859053106664570880 }, { target := 474, numerator := 80610795862584843797790720 }, { target := 475, numerator := 89819410504180651964497920 }, { target := 476, numerator := 4391800829068770048737280 }, { target := 477, numerator := 89819410504180651964497920 }, { target := 478, numerator := 89677739509694562608087040 }, { target := 479, numerator := 4391800829068770048737280 }, { target := 480, numerator := 106394916859053106664570880 }, { target := 481, numerator := 4391800829068770048737280 }, { target := 521, numerator := 134389105369504363491360768 }, { target := 522, numerator := 3255684455887025063935868928 }, { target := 523, numerator := 2466690353395096220212396032 }, { target := 524, numerator := 2748473961427927950113636352 }, { target := 525, numerator := 134389105369504363491360768 }, { target := 526, numerator := 2748473961427927950113636352 }, { target := 527, numerator := 2744138828996653615807463424 }, { target := 528, numerator := 134389105369504363491360768 }, { target := 529, numerator := 3255684455887025063935868928 }, { target := 530, numerator := 134389105369504363491360768 }, { target := 547, numerator := 140537626530200641559592960 }, { target := 548, numerator := 3404637339489699413266268160 }, { target := 549, numerator := 2579545467602715001529303040 }, { target := 550, numerator := 2874221136133780862863933440 }, { target := 551, numerator := 140537626530200641559592960 }, { target := 552, numerator := 2874221136133780862863933440 }, { target := 553, numerator := 2869687664310226003458785280 }, { target := 554, numerator := 140537626530200641559592960 }, { target := 555, numerator := 3404637339489699413266268160 }, { target := 556, numerator := 140537626530200641559592960 }]

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
    Slot0.Left18.expected,
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
    Slot1.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 55, numerator := 128849296787281380848435200 }, { target := 56, numerator := 22598956111967747103627673600 }, { target := 61, numerator := 22598958821333282929718067200 }, { target := 69, numerator := 128846587421745554758041600 }, { target := 100, numerator := 95951603990528687865856000 }, { target := 101, numerator := 16829009870614279758020608000 }, { target := 106, numerator := 16829011888226912820002816000 }, { target := 114, numerator := 95949586377895625883648000 }, { target := 126, numerator := 101434552789987470029619200 }, { target := 127, numerator := 17790667577506524315621785600 }, { target := 132, numerator := 17790669710411307838288691200 }, { target := 140, numerator := 101432419885203947362713600 }, { target := 195, numerator := 131590771187010771930316800 }, { target := 196, numerator := 23079784965413869382428262400 }, { target := 201, numerator := 23079787732425480438861004800 }, { target := 209, numerator := 131588004175399715497574400 }, { target := 240, numerator := 1762768039025998465649868800 }, { target := 241, numerator := 309172952765856625268778598400 }, { target := 246, numerator := 309172989832282998378908876800 }, { target := 254, numerator := 1762730972599625355519590400 }, { target := 266, numerator := 3188334726885281828228300800 }, { target := 267, numerator := 559203956557840210245084774400 }, { target := 272, numerator := 559204023600225703133236428800 }, { target := 280, numerator := 3188267684499788940076646400 }, { target := 315, numerator := 95951603990528687865856000 }, { target := 316, numerator := 16829009870614279758020608000 }, { target := 321, numerator := 16829011888226912820002816000 }, { target := 329, numerator := 95949586377895625883648000 }, { target := 341, numerator := 1762768039025998465649868800 }, { target := 342, numerator := 309172952765856625268778598400 }, { target := 347, numerator := 309172989832282998378908876800 }, { target := 355, numerator := 1762730972599625355519590400 }, { target := 376, numerator := 104176027189716861111500800 }, { target := 377, numerator := 18271496430952646594422374400 }, { target := 382, numerator := 18271498621503505347431628800 }, { target := 390, numerator := 104173836638858108102246400 }, { target := 456, numerator := 104176027189716861111500800 }, { target := 457, numerator := 18271496430952646594422374400 }, { target := 462, numerator := 18271498621503505347431628800 }, { target := 470, numerator := 104173836638858108102246400 }, { target := 482, numerator := 101434552789987470029619200 }, { target := 483, numerator := 17790667577506524315621785600 }, { target := 488, numerator := 17790669710411307838288691200 }, { target := 496, numerator := 101432419885203947362713600 }, { target := 531, numerator := 101434552789987470029619200 }, { target := 532, numerator := 17790667577506524315621785600 }, { target := 537, numerator := 17790669710411307838288691200 }, { target := 545, numerator := 101432419885203947362713600 }, { target := 557, numerator := 3188334726885281828228300800 }, { target := 558, numerator := 559203956557840210245084774400 }, { target := 563, numerator := 559204023600225703133236428800 }, { target := 571, numerator := 3188267684499788940076646400 }, { target := 643, numerator := 5270160994882524058484736 }, { target := 644, numerator := 127673900230863727997485056 }, { target := 645, numerator := 96732955035101812557348864 }, { target := 646, numerator := 107783292605016782357397504 }, { target := 647, numerator := 5270160994882524058484736 }, { target := 648, numerator := 107783292605016782357397504 }, { target := 649, numerator := 107613287411633475129704448 }, { target := 650, numerator := 5270160994882524058484736 }, { target := 651, numerator := 127673900230863727997485056 }, { target := 652, numerator := 5270160994882524058484736 }]

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
  [{ target := 142, numerator := 6479049921009005814087680 }, { target := 143, numerator := 2087040367031041741773864960 }, { target := 145, numerator := 22196551963025836478654578688 }, { target := 153, numerator := 2087046657370770876730966016 }, { target := 160, numerator := 6479049921009005814087680 }, { target := 282, numerator := 158841223869898207055052800 }, { target := 283, numerator := 51166150933664249153165721600 }, { target := 285, numerator := 544173531996762442702499348480 }, { target := 293, numerator := 51166305148444705365017231360 }, { target := 300, numerator := 158841223869898207055052800 }, { target := 357, numerator := 117458905019582621532815360 }, { target := 358, numerator := 37836022137788563189577809920 }, { target := 360, numerator := 402402006555500648419479781376 }, { target := 368, numerator := 37836136175560426862025900032 }, { target := 375, numerator := 117458905019582621532815360 }, { target := 392, numerator := 131044009692666020820418560 }, { target := 393, numerator := 42212074520273005551361720320 }, { target := 395, numerator := 448943163897329015229561962496 }, { target := 403, numerator := 42212201747466881926139215872 }, { target := 410, numerator := 131044009692666020820418560 }, { target := 498, numerator := 6479049921009005814087680 }, { target := 499, numerator := 2087040367031041741773864960 }, { target := 501, numerator := 22196551963025836478654578688 }, { target := 509, numerator := 2087046657370770876730966016 }, { target := 516, numerator := 6479049921009005814087680 }, { target := 573, numerator := 130835008082310891600609280 }, { target := 574, numerator := 42144750637465552591949660160 }, { target := 576, numerator := 448227146092070117278637621248 }, { target := 584, numerator := 42144877661745244155922087936 }, { target := 591, numerator := 130835008082310891600609280 }, { target := 592, numerator := 101434552789987470029619200 }, { target := 593, numerator := 17790667577506524315621785600 }, { target := 598, numerator := 17790669710411307838288691200 }, { target := 606, numerator := 101432419885203947362713600 }, { target := 608, numerator := 133134025796217313018511360 }, { target := 609, numerator := 42885313348347535145482321920 }, { target := 611, numerator := 456103341949917994738805374976 }, { target := 619, numerator := 42885442604683259628310495232 }, { target := 626, numerator := 133134025796217313018511360 }, { target := 653, numerator := 128849296787281380848435200 }, { target := 654, numerator := 22598956111967747103627673600 }, { target := 659, numerator := 22598958821333282929718067200 }, { target := 667, numerator := 128846587421745554758041600 }, { target := 669, numerator := 6479049921009005814087680 }, { target := 670, numerator := 2087040367031041741773864960 }, { target := 672, numerator := 22196551963025836478654578688 }, { target := 680, numerator := 2087046657370770876730966016 }, { target := 687, numerator := 6479049921009005814087680 }, { target := 688, numerator := 131590771187010771930316800 }, { target := 689, numerator := 23079784965413869382428262400 }, { target := 694, numerator := 23079787732425480438861004800 }, { target := 702, numerator := 131588004175399715497574400 }, { target := 704, numerator := 158841223869898207055052800 }, { target := 705, numerator := 51166150933664249153165721600 }, { target := 707, numerator := 544173531996762442702499348480 }, { target := 715, numerator := 51166305148444705365017231360 }, { target := 722, numerator := 158841223869898207055052800 }, { target := 739, numerator := 6479049921009005814087680 }, { target := 740, numerator := 2087040367031041741773864960 }, { target := 742, numerator := 22196551963025836478654578688 }, { target := 750, numerator := 2087046657370770876730966016 }, { target := 757, numerator := 6479049921009005814087680 }]

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
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot4.Left0.expected,
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
    Slot7.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 2, numerator := 1208341426762374056110981120 }, { target := 3, numerator := 1208341426762374056110981120 }, { target := 4, numerator := 1208341426762374056110981120 }, { target := 5, numerator := 1208341426762374056110981120 }, { target := 11, numerator := 29125425616886728952381440 }, { target := 13, numerator := 1316416251722553693243965440 }, { target := 18, numerator := 29280876818399388866969600 }, { target := 22, numerator := 48309266047610940526910504960 }, { target := 23, numerator := 48309266047610940526910504960 }, { target := 24, numerator := 48309266047610940526910504960 }, { target := 25, numerator := 48309266047610940526910504960 }, { target := 31, numerator := 4773096319297344726944972800 }, { target := 33, numerator := 215735270220980559327055052800 }, { target := 38, numerator := 4798571777322590878564352000 }, { target := 55, numerator := 54335000327460889670189056 }, { target := 56, numerator := 10776523503746417844604108800 }, { target := 61, numerator := 10776523503746417844604108800 }, { target := 69, numerator := 54335000327460889670189056 }, { target := 72, numerator := 48309254241694733352797470720 }, { target := 73, numerator := 48309254241694733352797470720 }, { target := 74, numerator := 48309254241694733352797470720 }, { target := 75, numerator := 48309254241694733352797470720 }, { target := 76, numerator := 49140874695605763965766860800 }, { target := 78, numerator := 2221078137160347005884353740800 }, { target := 83, numerator := 49403154399782376436662272000 }, { target := 100, numerator := 10776523503746417844604108800 }, { target := 101, numerator := 2137360046505882902845194240000 }, { target := 106, numerator := 2137360046505882902845194240000 }, { target := 114, numerator := 10776523503746417844604108800 }, { target := 301, numerator := 1208341426762374056110981120 }, { target := 302, numerator := 1208341426762374056110981120 }, { target := 303, numerator := 1208341426762374056110981120 }, { target := 304, numerator := 1208341426762374056110981120 }, { target := 305, numerator := 4773096319297344726944972800 }, { target := 307, numerator := 215735270220980559327055052800 }, { target := 312, numerator := 4798571777322590878564352000 }, { target := 315, numerator := 10776523503746417844604108800 }, { target := 316, numerator := 2137360046505882902845194240000 }, { target := 321, numerator := 2137360046505882902845194240000 }, { target := 329, numerator := 10776523503746417844604108800 }, { target := 411, numerator := 3220259014973223987950125056 }, { target := 413, numerator := 126028371988737047640527601664 }, { target := 416, numerator := 126028418211666010338236563456 }, { target := 423, numerator := 3220305237902186685659086848 }, { target := 627, numerator := 3210861371933418859580620800 }, { target := 629, numerator := 125660584910948904505389875200 }, { target := 632, numerator := 125660630998986051164097740800 }, { target := 639, numerator := 3210907459970565518288486400 }, { target := 643, numerator := 29125425616886728952381440 }, { target := 645, numerator := 1316416251722553693243965440 }, { target := 650, numerator := 29280876818399388866969600 }, { target := 723, numerator := 3188933538173873560051777536 }, { target := 725, numerator := 124802415062776570523401846784 }, { target := 728, numerator := 124802460836066146424440487936 }, { target := 735, numerator := 3188979311463449461090418688 }, { target := 758, numerator := 3210861371933418859580620800 }, { target := 760, numerator := 125660584910948904505389875200 }, { target := 763, numerator := 125660630998986051164097740800 }, { target := 770, numerator := 3210907459970565518288486400 }, { target := 774, numerator := 70933415512066980298945986560 }, { target := 777, numerator := 254253368417490001368469995520 }, { target := 779, numerator := 70954028641764706300303769600 }]

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
    Slot7.Left14.expected,
    Slot8.Left0.expected,
    Slot8.Left2.expected,
    Slot8.Left7.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left2.expected,
    Slot9.Left3.expected,
    Slot10.Left0.expected,
    Slot10.Left3.expected,
    Slot10.Left5.expected,
    Slot11.Left0.expected,
    Slot11.Left2.expected,
    Slot11.Left5.expected,
    Slot11.Left12.expected,
    Slot12.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 70933415512066980298945986560 }, { target := 2, numerator := 3467971246894241217792442368 }, { target := 3, numerator := 3457850708235989541086822400 }, { target := 4, numerator := 3434236118033402295440375808 }, { target := 5, numerator := 3457850708235989541086822400 }, { target := 11, numerator := 6331798786440619318312960 }, { target := 12, numerator := 155231196054673247803801600 }, { target := 13, numerator := 114789384450955743770705920 }, { target := 14, numerator := 128065736745105429438136320 }, { target := 15, numerator := 6331798786440619318312960 }, { target := 16, numerator := 127861485171349280427868160 }, { target := 17, numerator := 130108252482666919540817920 }, { target := 18, numerator := 6331798786440619318312960 }, { target := 19, numerator := 155231196054673247803801600 }, { target := 20, numerator := 6331798786440619318312960 }, { target := 21, numerator := 254253368417490001368469995520 }, { target := 22, numerator := 135722862141716820535952801792 }, { target := 23, numerator := 135326783750252666390419865600 }, { target := 24, numerator := 134402600836836306717509681152 }, { target := 25, numerator := 135326783750252666390419865600 }, { target := 71, numerator := 70954028641764706300303769600 }, { target := 72, numerator := 135722911920255703441177837568 }, { target := 73, numerator := 135326833383523439715182182400 }, { target := 74, numerator := 134402650131148157687858987008 }, { target := 75, numerator := 135326833383523439715182182400 }, { target := 142, numerator := 29957580634512064065306624 }, { target := 143, numerator := 4909470499848697433429114880 }, { target := 145, numerator := 50544899686908785793360199680 }, { target := 153, numerator := 4909470499848697433429114880 }, { target := 160, numerator := 29957580634512064065306624 }, { target := 301, numerator := 3468021025433124123017478144 }, { target := 302, numerator := 3457900341506762865849139200 }, { target := 303, numerator := 3434285412345253265789681664 }, { target := 304, numerator := 3457900341506762865849139200 }, { target := 357, numerator := 1354028144628912370193793024 }, { target := 358, numerator := 221899135084437146736399482880 }, { target := 360, numerator := 2284537512507785491766763847680 }, { target := 368, numerator := 221899135084437146736399482880 }, { target := 375, numerator := 1354028144628912370193793024 }, { target := 411, numerator := 1208341426762374056110981120 }, { target := 413, numerator := 48309266047610940526910504960 }, { target := 416, numerator := 48309254241694733352797470720 }, { target := 423, numerator := 1208341426762374056110981120 }, { target := 627, numerator := 1208341426762374056110981120 }, { target := 629, numerator := 48309266047610940526910504960 }, { target := 632, numerator := 48309254241694733352797470720 }, { target := 639, numerator := 1208341426762374056110981120 }, { target := 653, numerator := 54335000327460889670189056 }, { target := 654, numerator := 10776523503746417844604108800 }, { target := 659, numerator := 10776523503746417844604108800 }, { target := 667, numerator := 54335000327460889670189056 }, { target := 669, numerator := 30117473298925085691740160 }, { target := 670, numerator := 4935673828103236332237619200 }, { target := 672, numerator := 50814673096919015763424051200 }, { target := 680, numerator := 4935673828103236332237619200 }, { target := 687, numerator := 30117473298925085691740160 }, { target := 723, numerator := 1208341426762374056110981120 }, { target := 725, numerator := 48309266047610940526910504960 }, { target := 728, numerator := 48309254241694733352797470720 }, { target := 735, numerator := 1208341426762374056110981120 }, { target := 758, numerator := 1208341426762374056110981120 }, { target := 760, numerator := 48309266047610940526910504960 }, { target := 763, numerator := 48309254241694733352797470720 }, { target := 770, numerator := 1208341426762374056110981120 }]

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
    Slot12.Left1.expected,
    Slot12.Left3.expected,
    Slot12.Left11.expected,
    Slot12.Left18.expected,
    Slot13.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 31, numerator := 2039607631416699884006277120 }, { target := 32, numerator := 50003283866990061672411955200 }, { target := 33, numerator := 36976112543747914026178314240 }, { target := 34, numerator := 41252709190266800879739863040 }, { target := 35, numerator := 2039607631416699884006277120 }, { target := 36, numerator := 41186915395704971851223531520 }, { target := 37, numerator := 41910647135885091164903178240 }, { target := 38, numerator := 2039607631416699884006277120 }, { target := 39, numerator := 50003283866990061672411955200 }, { target := 40, numerator := 2039607631416699884006277120 }, { target := 55, numerator := 128849296787281380848435200 }, { target := 56, numerator := 95951603990528687865856000 }, { target := 57, numerator := 101434552789987470029619200 }, { target := 58, numerator := 131590771187010771930316800 }, { target := 59, numerator := 1762768039025998465649868800 }, { target := 60, numerator := 3188334726885281828228300800 }, { target := 61, numerator := 95951603990528687865856000 }, { target := 62, numerator := 1762768039025998465649868800 }, { target := 63, numerator := 104176027189716861111500800 }, { target := 64, numerator := 104176027189716861111500800 }, { target := 65, numerator := 101434552789987470029619200 }, { target := 66, numerator := 101434552789987470029619200 }, { target := 67, numerator := 3188334726885281828228300800 }, { target := 68, numerator := 101434552789987470029619200 }, { target := 69, numerator := 128849296787281380848435200 }, { target := 70, numerator := 131590771187010771930316800 }, { target := 76, numerator := 21692084872957067467776065536 }, { target := 77, numerator := 531805951724108750822897090560 }, { target := 78, numerator := 393256506406511997319037059072 }, { target := 79, numerator := 438739910172389719428890099712 }, { target := 80, numerator := 21692084872957067467776065536 }, { target := 81, numerator := 438040165499068523704123129856 }, { target := 82, numerator := 445737356905601676676559798272 }, { target := 83, numerator := 21692084872957067467776065536 }, { target := 84, numerator := 531805951724108750822897090560 }, { target := 85, numerator := 21692084872957067467776065536 }, { target := 305, numerator := 2039613778794162447714353152 }, { target := 306, numerator := 50003434576889143879448657920 }, { target := 307, numerator := 36976223989752235342434402304 }, { target := 308, numerator := 41252833525933543700545142784 }, { target := 309, numerator := 2039613778794162447714353152 }, { target := 310, numerator := 41187039533069215879651131392 }, { target := 311, numerator := 41910773454576821909485256704 }, { target := 312, numerator := 2039613778794162447714353152 }, { target := 313, numerator := 50003434576889143879448657920 }, { target := 314, numerator := 2039613778794162447714353152 }, { target := 643, numerator := 6331798786440619318312960 }, { target := 644, numerator := 155231196054673247803801600 }, { target := 645, numerator := 114789384450955743770705920 }, { target := 646, numerator := 128065736745105429438136320 }, { target := 647, numerator := 6331798786440619318312960 }, { target := 648, numerator := 127861485171349280427868160 }, { target := 649, numerator := 130108252482666919540817920 }, { target := 650, numerator := 6331798786440619318312960 }, { target := 651, numerator := 155231196054673247803801600 }, { target := 652, numerator := 6331798786440619318312960 }]

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
    Slot13.Left1.expected,
    Slot13.Left6.expected,
    Slot13.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 100, numerator := 22598956111967747103627673600 }, { target := 101, numerator := 16829009870614279758020608000 }, { target := 102, numerator := 17790667577506524315621785600 }, { target := 103, numerator := 23079784965413869382428262400 }, { target := 104, numerator := 309172952765856625268778598400 }, { target := 105, numerator := 559203956557840210245084774400 }, { target := 106, numerator := 16829009870614279758020608000 }, { target := 107, numerator := 309172952765856625268778598400 }, { target := 108, numerator := 18271496430952646594422374400 }, { target := 109, numerator := 18271496430952646594422374400 }, { target := 110, numerator := 17790667577506524315621785600 }, { target := 111, numerator := 17790667577506524315621785600 }, { target := 112, numerator := 559203956557840210245084774400 }, { target := 113, numerator := 17790667577506524315621785600 }, { target := 114, numerator := 22598956111967747103627673600 }, { target := 115, numerator := 23079784965413869382428262400 }, { target := 315, numerator := 22598958821333282929718067200 }, { target := 316, numerator := 16829011888226912820002816000 }, { target := 317, numerator := 17790669710411307838288691200 }, { target := 318, numerator := 23079787732425480438861004800 }, { target := 319, numerator := 309172989832282998378908876800 }, { target := 320, numerator := 559204023600225703133236428800 }, { target := 321, numerator := 16829011888226912820002816000 }, { target := 322, numerator := 309172989832282998378908876800 }, { target := 323, numerator := 18271498621503505347431628800 }, { target := 324, numerator := 18271498621503505347431628800 }, { target := 325, numerator := 17790669710411307838288691200 }, { target := 326, numerator := 17790669710411307838288691200 }, { target := 327, numerator := 559204023600225703133236428800 }, { target := 328, numerator := 17790669710411307838288691200 }, { target := 329, numerator := 22598958821333282929718067200 }, { target := 330, numerator := 23079787732425480438861004800 }, { target := 653, numerator := 128846587421745554758041600 }, { target := 654, numerator := 95949586377895625883648000 }, { target := 655, numerator := 101432419885203947362713600 }, { target := 656, numerator := 131588004175399715497574400 }, { target := 657, numerator := 1762730972599625355519590400 }, { target := 658, numerator := 3188267684499788940076646400 }, { target := 659, numerator := 95949586377895625883648000 }, { target := 660, numerator := 1762730972599625355519590400 }, { target := 661, numerator := 104173836638858108102246400 }, { target := 662, numerator := 104173836638858108102246400 }, { target := 663, numerator := 101432419885203947362713600 }, { target := 664, numerator := 101432419885203947362713600 }, { target := 665, numerator := 3188267684499788940076646400 }, { target := 666, numerator := 101432419885203947362713600 }, { target := 667, numerator := 128846587421745554758041600 }, { target := 668, numerator := 131588004175399715497574400 }]

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
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 142, numerator := 5270160994882524058484736 }, { target := 143, numerator := 76417334425796598848028672 }, { target := 144, numerator := 135267465535318117501108224 }, { target := 145, numerator := 4391800829068770048737280 }, { target := 146, numerator := 84322575918120384935755776 }, { target := 147, numerator := 4391800829068770048737280 }, { target := 148, numerator := 134389105369504363491360768 }, { target := 149, numerator := 140537626530200641559592960 }, { target := 150, numerator := 84322575918120384935755776 }, { target := 151, numerator := 2152860766409511077891014656 }, { target := 152, numerator := 137902546032759379530350592 }, { target := 153, numerator := 76417334425796598848028672 }, { target := 154, numerator := 134389105369504363491360768 }, { target := 155, numerator := 4391800829068770048737280 }, { target := 156, numerator := 137902546032759379530350592 }, { target := 157, numerator := 4391800829068770048737280 }, { target := 158, numerator := 134389105369504363491360768 }, { target := 159, numerator := 140537626530200641559592960 }, { target := 160, numerator := 5270160994882524058484736 }, { target := 282, numerator := 127673900230863727997485056 }, { target := 283, numerator := 1851271553347524055963533312 }, { target := 284, numerator := 3276963439258835685268783104 }, { target := 285, numerator := 106394916859053106664570880 }, { target := 286, numerator := 2042782403693819647959760896 }, { target := 287, numerator := 106394916859053106664570880 }, { target := 288, numerator := 3255684455887025063935868928 }, { target := 289, numerator := 3404637339489699413266268160 }, { target := 290, numerator := 2042782403693819647959760896 }, { target := 291, numerator := 52154788244307832886972645376 }, { target := 292, numerator := 3340800389374267549267525632 }, { target := 293, numerator := 1851271553347524055963533312 }, { target := 294, numerator := 3255684455887025063935868928 }, { target := 295, numerator := 106394916859053106664570880 }, { target := 296, numerator := 3340800389374267549267525632 }, { target := 297, numerator := 106394916859053106664570880 }, { target := 298, numerator := 3255684455887025063935868928 }, { target := 299, numerator := 3404637339489699413266268160 }, { target := 300, numerator := 127673900230863727997485056 }, { target := 357, numerator := 96732955035101812557348864 }, { target := 358, numerator := 1402627848008976282081558528 }, { target := 359, numerator := 2482812512567613188971954176 }, { target := 360, numerator := 80610795862584843797790720 }, { target := 361, numerator := 1547727280561629000917581824 }, { target := 362, numerator := 80610795862584843797790720 }, { target := 363, numerator := 2466690353395096220212396032 }, { target := 364, numerator := 2579545467602715001529303040 }, { target := 365, numerator := 1547727280561629000917581824 }, { target := 366, numerator := 39515412131839090429677010944 }, { target := 367, numerator := 2531178990085164095250628608 }, { target := 368, numerator := 1402627848008976282081558528 }, { target := 369, numerator := 2466690353395096220212396032 }, { target := 370, numerator := 80610795862584843797790720 }, { target := 371, numerator := 2531178990085164095250628608 }, { target := 372, numerator := 80610795862584843797790720 }, { target := 373, numerator := 2466690353395096220212396032 }, { target := 374, numerator := 2579545467602715001529303040 }, { target := 375, numerator := 96732955035101812557348864 }]

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
    Slot14.Left3.expected,
    Slot14.Left4.expected,
    Slot14.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 392, numerator := 107783292605016782357397504 }, { target := 393, numerator := 1562857742772743344182263808 }, { target := 394, numerator := 2766437843528764080506535936 }, { target := 395, numerator := 89819410504180651964497920 }, { target := 396, numerator := 1724532681680268517718360064 }, { target := 397, numerator := 89819410504180651964497920 }, { target := 398, numerator := 2748473961427927950113636352 }, { target := 399, numerator := 2874221136133780862863933440 }, { target := 400, numerator := 1724532681680268517718360064 }, { target := 401, numerator := 44029475029149355592996880384 }, { target := 402, numerator := 2820329489831272471685234688 }, { target := 403, numerator := 1562857742772743344182263808 }, { target := 404, numerator := 2748473961427927950113636352 }, { target := 405, numerator := 89819410504180651964497920 }, { target := 406, numerator := 2820329489831272471685234688 }, { target := 407, numerator := 89819410504180651964497920 }, { target := 408, numerator := 2748473961427927950113636352 }, { target := 409, numerator := 2874221136133780862863933440 }, { target := 410, numerator := 107783292605016782357397504 }, { target := 498, numerator := 5270160994882524058484736 }, { target := 499, numerator := 76417334425796598848028672 }, { target := 500, numerator := 135267465535318117501108224 }, { target := 501, numerator := 4391800829068770048737280 }, { target := 502, numerator := 84322575918120384935755776 }, { target := 503, numerator := 4391800829068770048737280 }, { target := 504, numerator := 134389105369504363491360768 }, { target := 505, numerator := 140537626530200641559592960 }, { target := 506, numerator := 84322575918120384935755776 }, { target := 507, numerator := 2152860766409511077891014656 }, { target := 508, numerator := 137902546032759379530350592 }, { target := 509, numerator := 76417334425796598848028672 }, { target := 510, numerator := 134389105369504363491360768 }, { target := 511, numerator := 4391800829068770048737280 }, { target := 512, numerator := 137902546032759379530350592 }, { target := 513, numerator := 4391800829068770048737280 }, { target := 514, numerator := 134389105369504363491360768 }, { target := 515, numerator := 140537626530200641559592960 }, { target := 516, numerator := 5270160994882524058484736 }, { target := 573, numerator := 107783292605016782357397504 }, { target := 574, numerator := 1562857742772743344182263808 }, { target := 575, numerator := 2766437843528764080506535936 }, { target := 576, numerator := 89819410504180651964497920 }, { target := 577, numerator := 1724532681680268517718360064 }, { target := 578, numerator := 89819410504180651964497920 }, { target := 579, numerator := 2748473961427927950113636352 }, { target := 580, numerator := 2874221136133780862863933440 }, { target := 581, numerator := 1724532681680268517718360064 }, { target := 582, numerator := 44029475029149355592996880384 }, { target := 583, numerator := 2820329489831272471685234688 }, { target := 584, numerator := 1562857742772743344182263808 }, { target := 585, numerator := 2748473961427927950113636352 }, { target := 586, numerator := 89819410504180651964497920 }, { target := 587, numerator := 2820329489831272471685234688 }, { target := 588, numerator := 89819410504180651964497920 }, { target := 589, numerator := 2748473961427927950113636352 }, { target := 590, numerator := 2874221136133780862863933440 }, { target := 591, numerator := 107783292605016782357397504 }]

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
    Slot14.Left6.expected,
    Slot14.Left7.expected,
    Slot14.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 608, numerator := 107613287411633475129704448 }, { target := 609, numerator := 1560392667468685389380714496 }, { target := 610, numerator := 2762074376898592528329080832 }, { target := 611, numerator := 89677739509694562608087040 }, { target := 612, numerator := 1721812598586135602075271168 }, { target := 613, numerator := 89677739509694562608087040 }, { target := 614, numerator := 2744138828996653615807463424 }, { target := 615, numerator := 2869687664310226003458785280 }, { target := 616, numerator := 1721812598586135602075271168 }, { target := 617, numerator := 43960027907652274590484267008 }, { target := 618, numerator := 2815881020604409265893933056 }, { target := 619, numerator := 1560392667468685389380714496 }, { target := 620, numerator := 2744138828996653615807463424 }, { target := 621, numerator := 89677739509694562608087040 }, { target := 622, numerator := 2815881020604409265893933056 }, { target := 623, numerator := 89677739509694562608087040 }, { target := 624, numerator := 2744138828996653615807463424 }, { target := 625, numerator := 2869687664310226003458785280 }, { target := 626, numerator := 107613287411633475129704448 }, { target := 669, numerator := 5270160994882524058484736 }, { target := 670, numerator := 76417334425796598848028672 }, { target := 671, numerator := 135267465535318117501108224 }, { target := 672, numerator := 4391800829068770048737280 }, { target := 673, numerator := 84322575918120384935755776 }, { target := 674, numerator := 4391800829068770048737280 }, { target := 675, numerator := 134389105369504363491360768 }, { target := 676, numerator := 140537626530200641559592960 }, { target := 677, numerator := 84322575918120384935755776 }, { target := 678, numerator := 2152860766409511077891014656 }, { target := 679, numerator := 137902546032759379530350592 }, { target := 680, numerator := 76417334425796598848028672 }, { target := 681, numerator := 134389105369504363491360768 }, { target := 682, numerator := 4391800829068770048737280 }, { target := 683, numerator := 137902546032759379530350592 }, { target := 684, numerator := 4391800829068770048737280 }, { target := 685, numerator := 134389105369504363491360768 }, { target := 686, numerator := 140537626530200641559592960 }, { target := 687, numerator := 5270160994882524058484736 }, { target := 704, numerator := 127673900230863727997485056 }, { target := 705, numerator := 1851271553347524055963533312 }, { target := 706, numerator := 3276963439258835685268783104 }, { target := 707, numerator := 106394916859053106664570880 }, { target := 708, numerator := 2042782403693819647959760896 }, { target := 709, numerator := 106394916859053106664570880 }, { target := 710, numerator := 3255684455887025063935868928 }, { target := 711, numerator := 3404637339489699413266268160 }, { target := 712, numerator := 2042782403693819647959760896 }, { target := 713, numerator := 52154788244307832886972645376 }, { target := 714, numerator := 3340800389374267549267525632 }, { target := 715, numerator := 1851271553347524055963533312 }, { target := 716, numerator := 3255684455887025063935868928 }, { target := 717, numerator := 106394916859053106664570880 }, { target := 718, numerator := 3340800389374267549267525632 }, { target := 719, numerator := 106394916859053106664570880 }, { target := 720, numerator := 3255684455887025063935868928 }, { target := 721, numerator := 3404637339489699413266268160 }, { target := 722, numerator := 127673900230863727997485056 }]

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
    Slot14.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 739, numerator := 5270160994882524058484736 }, { target := 740, numerator := 76417334425796598848028672 }, { target := 741, numerator := 135267465535318117501108224 }, { target := 742, numerator := 4391800829068770048737280 }, { target := 743, numerator := 84322575918120384935755776 }, { target := 744, numerator := 4391800829068770048737280 }, { target := 745, numerator := 134389105369504363491360768 }, { target := 746, numerator := 140537626530200641559592960 }, { target := 747, numerator := 84322575918120384935755776 }, { target := 748, numerator := 2152860766409511077891014656 }, { target := 749, numerator := 137902546032759379530350592 }, { target := 750, numerator := 76417334425796598848028672 }, { target := 751, numerator := 134389105369504363491360768 }, { target := 752, numerator := 4391800829068770048737280 }, { target := 753, numerator := 137902546032759379530350592 }, { target := 754, numerator := 4391800829068770048737280 }, { target := 755, numerator := 134389105369504363491360768 }, { target := 756, numerator := 140537626530200641559592960 }, { target := 757, numerator := 5270160994882524058484736 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5.Parent1
