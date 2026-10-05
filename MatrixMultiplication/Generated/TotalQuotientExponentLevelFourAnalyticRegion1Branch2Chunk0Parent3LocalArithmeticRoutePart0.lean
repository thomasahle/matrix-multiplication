import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk0Parent3LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 4; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk0.Parent3

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
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected,
    Slot2.Left7.expected,
    Slot2.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 142, numerator := 10090484300469585418649600 }, { target := 143, numerator := 1057969080038285812065894400 }, { target := 145, numerator := 11403849243961282736947200000 }, { target := 153, numerator := 1057969887083339036858777600 }, { target := 160, numerator := 10090484300469585418649600 }, { target := 282, numerator := 202213305381410491789737984 }, { target := 283, numerator := 21201700363967247673800523776 }, { target := 285, numerator := 228533138848984106048421888000 }, { target := 293, numerator := 21201716537150114298649903104 }, { target := 300, numerator := 202213305381410491789737984 }, { target := 357, numerator := 339443891867796853483372544 }, { target := 358, numerator := 35590079852487934717896687616 }, { target := 360, numerator := 383625488566857551270903808000 }, { target := 368, numerator := 35590107001483525199929278464 }, { target := 375, numerator := 339443891867796853483372544 }, { target := 392, numerator := 325720833219158217314009088 }, { target := 393, numerator := 34151241903635866013487071232 }, { target := 395, numerator := 368116253595070206748655616000 }, { target := 403, numerator := 34151267955050184109801340928 }, { target := 410, numerator := 325720833219158217314009088 }, { target := 411, numerator := 1437377849859303436766412800 }, { target := 413, numerator := 50304641061516775594026598400 }, { target := 416, numerator := 50304665734036974180551884800 }, { target := 423, numerator := 1437365513599204143503769600 }, { target := 498, numerator := 10090484300469585418649600 }, { target := 499, numerator := 1057969080038285812065894400 }, { target := 501, numerator := 11403849243961282736947200000 }, { target := 509, numerator := 1057969887083339036858777600 }, { target := 516, numerator := 10090484300469585418649600 }, { target := 573, numerator := 325720833219158217314009088 }, { target := 574, numerator := 34151241903635866013487071232 }, { target := 576, numerator := 368116253595070206748655616000 }, { target := 584, numerator := 34151267955050184109801340928 }, { target := 591, numerator := 325720833219158217314009088 }, { target := 608, numerator := 217550841518124261626085376 }, { target := 609, numerator := 22809813365625442108140683264 }, { target := 611, numerator := 245866989699805255808581632000 }, { target := 619, numerator := 22809830765516789634675245056 }, { target := 626, numerator := 217550841518124261626085376 }, { target := 627, numerator := 1313790221647101645941637120 }, { target := 629, numerator := 45979382203891034141082255360 }, { target := 632, numerator := 45979404755035664251009105920 }, { target := 639, numerator := 1313778946074786590978211840 }, { target := 669, numerator := 10494103672488368835395584 }, { target := 670, numerator := 1100287843239817244548530176 }, { target := 672, numerator := 11860003213719734046425088000 }, { target := 680, numerator := 1100288682566672598333128704 }, { target := 687, numerator := 10494103672488368835395584 }, { target := 704, numerator := 202213305381410491789737984 }, { target := 705, numerator := 21201700363967247673800523776 }, { target := 707, numerator := 228533138848984106048421888000 }, { target := 715, numerator := 21201716537150114298649903104 }, { target := 722, numerator := 202213305381410491789737984 }, { target := 723, numerator := 1437377849859303436766412800 }, { target := 725, numerator := 50304641061516775594026598400 }, { target := 728, numerator := 50304665734036974180551884800 }, { target := 735, numerator := 1437365513599204143503769600 }, { target := 758, numerator := 1313790221647101645941637120 }, { target := 760, numerator := 45979382203891034141082255360 }, { target := 763, numerator := 45979404755035664251009105920 }, { target := 770, numerator := 1313778946074786590978211840 }, { target := 774, numerator := 14620257736305106795794268160 }, { target := 777, numerator := 49987651764020606871600627712 }, { target := 779, numerator := 14620253013938623926149054464 }]

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
    Slot2.Left9.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
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
  [{ target := 55, numerator := 207743888285753610443161600 }, { target := 56, numerator := 17394216045303247173278760960 }, { target := 61, numerator := 17394222340254662326663249920 }, { target := 69, numerator := 207737593334338457058672640 }, { target := 100, numerator := 213679427951060856455823360 }, { target := 101, numerator := 17891193646597625663943868416 }, { target := 106, numerator := 17891200121404795535996485632 }, { target := 114, numerator := 213672953143890984403206144 }, { target := 126, numerator := 207743888285753610443161600 }, { target := 127, numerator := 17394216045303247173278760960 }, { target := 132, numerator := 17394222340254662326663249920 }, { target := 140, numerator := 207737593334338457058672640 }, { target := 195, numerator := 184001729624524626392514560 }, { target := 196, numerator := 15406305640125733210618331136 }, { target := 201, numerator := 15406311215654129489330307072 }, { target := 209, numerator := 183996154096128347680538624 }, { target := 240, numerator := 8612468054360813964372213760 }, { target := 241, numerator := 721114499478143189955070918656 }, { target := 246, numerator := 721114760448843286742525018112 }, { target := 254, numerator := 8612207083660717176918114304 }, { target := 266, numerator := 2344538167796362175001395200 }, { target := 267, numerator := 196306152511279503812717445120 }, { target := 272, numerator := 196306223554302617686628106240 }, { target := 280, numerator := 2344467124773248301090734080 }, { target := 315, numerator := 213679427951060856455823360 }, { target := 316, numerator := 17891193646597625663943868416 }, { target := 321, numerator := 17891200121404795535996485632 }, { target := 329, numerator := 213672953143890984403206144 }, { target := 341, numerator := 8612468054360813964372213760 }, { target := 342, numerator := 721114499478143189955070918656 }, { target := 347, numerator := 721114760448843286742525018112 }, { target := 355, numerator := 8612207083660717176918114304 }, { target := 376, numerator := 207743888285753610443161600 }, { target := 377, numerator := 17394216045303247173278760960 }, { target := 382, numerator := 17394222340254662326663249920 }, { target := 390, numerator := 207737593334338457058672640 }, { target := 456, numerator := 207743888285753610443161600 }, { target := 457, numerator := 17394216045303247173278760960 }, { target := 462, numerator := 17394222340254662326663249920 }, { target := 470, numerator := 207737593334338457058672640 }, { target := 482, numerator := 178066189959217380379852800 }, { target := 483, numerator := 14909328038831354719953223680 }, { target := 488, numerator := 14909333434503996279997071360 }, { target := 496, numerator := 178060794286575820336005120 }, { target := 531, numerator := 207743888285753610443161600 }, { target := 532, numerator := 17394216045303247173278760960 }, { target := 537, numerator := 17394222340254662326663249920 }, { target := 545, numerator := 207737593334338457058672640 }, { target := 557, numerator := 2344538167796362175001395200 }, { target := 558, numerator := 196306152511279503812717445120 }, { target := 563, numerator := 196306223554302617686628106240 }, { target := 571, numerator := 2344467124773248301090734080 }, { target := 592, numerator := 178066189959217380379852800 }, { target := 593, numerator := 14909328038831354719953223680 }, { target := 598, numerator := 14909333434503996279997071360 }, { target := 606, numerator := 178060794286575820336005120 }, { target := 739, numerator := 9686864928450802001903616 }, { target := 740, numerator := 1015650316836754379583258624 }, { target := 742, numerator := 10947695274202831427469312000 }, { target := 750, numerator := 1015651091600005475384426496 }, { target := 757, numerator := 9686864928450802001903616 }]

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
    Slot4.Left12.expected,
    Slot4.Left13.expected,
    Slot4.Left14.expected,
    Slot4.Left15.expected,
    Slot4.Left16.expected,
    Slot4.Left17.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 11, numerator := 89380915256647511426727936 }, { target := 13, numerator := 865750077633744584092680192 }, { target := 18, numerator := 89380915256647511426727936 }, { target := 31, numerator := 2383491073510600304712744960 }, { target := 33, numerator := 23086668736899855575804805120 }, { target := 38, numerator := 2383491073510600304712744960 }, { target := 45, numerator := 2279213339044511541381562368 }, { target := 47, numerator := 22076626979660486894363344896 }, { target := 52, numerator := 2279213339044511541381562368 }, { target := 76, numerator := 74484096047206259522273280 }, { target := 78, numerator := 721458398028120486743900160 }, { target := 83, numerator := 74484096047206259522273280 }, { target := 90, numerator := 2338800615882276548999380992 }, { target := 92, numerator := 22653793698082983283758465024 }, { target := 97, numerator := 2338800615882276548999380992 }, { target := 116, numerator := 74484096047206259522273280 }, { target := 118, numerator := 721458398028120486743900160 }, { target := 123, numerator := 74484096047206259522273280 }, { target := 171, numerator := 2279213339044511541381562368 }, { target := 173, numerator := 22076626979660486894363344896 }, { target := 178, numerator := 2279213339044511541381562368 }, { target := 185, numerator := 1296023271221388915687555072 }, { target := 187, numerator := 12553376125689296469343862784 }, { target := 192, numerator := 1296023271221388915687555072 }, { target := 216, numerator := 2338800615882276548999380992 }, { target := 218, numerator := 22653793698082983283758465024 }, { target := 223, numerator := 2338800615882276548999380992 }, { target := 230, numerator := 36512103882340508417818361856 }, { target := 232, numerator := 353658906713384662601859858432 }, { target := 237, numerator := 36512103882340508417818361856 }, { target := 256, numerator := 1430094644106360182827646976 }, { target := 258, numerator := 13852001242139913345482883072 }, { target := 263, numerator := 1430094644106360182827646976 }, { target := 305, numerator := 2383491073510600304712744960 }, { target := 307, numerator := 23086668736899855575804805120 }, { target := 312, numerator := 2383491073510600304712744960 }, { target := 331, numerator := 2279213339044511541381562368 }, { target := 333, numerator := 22076626979660486894363344896 }, { target := 338, numerator := 2279213339044511541381562368 }, { target := 432, numerator := 74484096047206259522273280 }, { target := 434, numerator := 721458398028120486743900160 }, { target := 439, numerator := 74484096047206259522273280 }, { target := 446, numerator := 1430094644106360182827646976 }, { target := 448, numerator := 13852001242139913345482883072 }, { target := 453, numerator := 1430094644106360182827646976 }, { target := 472, numerator := 74484096047206259522273280 }, { target := 474, numerator := 721458398028120486743900160 }, { target := 479, numerator := 74484096047206259522273280 }, { target := 521, numerator := 2294110158253952793286017024 }, { target := 523, numerator := 22220918659266110991712124928 }, { target := 528, numerator := 2294110158253952793286017024 }, { target := 547, numerator := 1296023271221388915687555072 }, { target := 549, numerator := 12553376125689296469343862784 }, { target := 554, numerator := 1296023271221388915687555072 }, { target := 653, numerator := 207743888285753610443161600 }, { target := 654, numerator := 17394216045303247173278760960 }, { target := 659, numerator := 17394222340254662326663249920 }, { target := 667, numerator := 207737593334338457058672640 }, { target := 688, numerator := 184001729624524626392514560 }, { target := 689, numerator := 15406305640125733210618331136 }, { target := 694, numerator := 15406311215654129489330307072 }, { target := 702, numerator := 183996154096128347680538624 }]

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
    Slot5.Left12.expected,
    Slot5.Left13.expected,
    Slot5.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 2, numerator := 232113757366008801543585792 }, { target := 3, numerator := 232113757366008801543585792 }, { target := 4, numerator := 232113757366008801543585792 }, { target := 5, numerator := 232113757366008801543585792 }, { target := 7, numerator := 227278054087550284844761088 }, { target := 8, numerator := 227278054087550284844761088 }, { target := 9, numerator := 227278054087550284844761088 }, { target := 10, numerator := 227278054087550284844761088 }, { target := 22, numerator := 178921021302965117856514048 }, { target := 23, numerator := 178921021302965117856514048 }, { target := 24, numerator := 178921021302965117856514048 }, { target := 25, numerator := 178921021302965117856514048 }, { target := 27, numerator := 5623922912847254920733130752 }, { target := 28, numerator := 5623922912847254920733130752 }, { target := 29, numerator := 5623922912847254920733130752 }, { target := 30, numerator := 5623922912847254920733130752 }, { target := 41, numerator := 178921021302965117856514048 }, { target := 42, numerator := 178921021302965117856514048 }, { target := 43, numerator := 178921021302965117856514048 }, { target := 44, numerator := 178921021302965117856514048 }, { target := 72, numerator := 178921021302965117856514048 }, { target := 73, numerator := 178921021302965117856514048 }, { target := 74, numerator := 178921021302965117856514048 }, { target := 75, numerator := 178921021302965117856514048 }, { target := 86, numerator := 183756724581423634555338752 }, { target := 87, numerator := 183756724581423634555338752 }, { target := 88, numerator := 183756724581423634555338752 }, { target := 89, numerator := 183756724581423634555338752 }, { target := 162, numerator := 183756724581423634555338752 }, { target := 163, numerator := 183756724581423634555338752 }, { target := 164, numerator := 183756724581423634555338752 }, { target := 165, numerator := 183756724581423634555338752 }, { target := 167, numerator := 3109357208048826237344284672 }, { target := 168, numerator := 3109357208048826237344284672 }, { target := 169, numerator := 3109357208048826237344284672 }, { target := 170, numerator := 3109357208048826237344284672 }, { target := 181, numerator := 169249614746048084458864640 }, { target := 182, numerator := 169249614746048084458864640 }, { target := 183, numerator := 169249614746048084458864640 }, { target := 184, numerator := 169249614746048084458864640 }, { target := 212, numerator := 5623922912847254920733130752 }, { target := 213, numerator := 5623922912847254920733130752 }, { target := 214, numerator := 5623922912847254920733130752 }, { target := 215, numerator := 5623922912847254920733130752 }, { target := 226, numerator := 3109357208048826237344284672 }, { target := 227, numerator := 3109357208048826237344284672 }, { target := 228, numerator := 3109357208048826237344284672 }, { target := 229, numerator := 3109357208048826237344284672 }, { target := 301, numerator := 232113757366008801543585792 }, { target := 302, numerator := 232113757366008801543585792 }, { target := 303, numerator := 232113757366008801543585792 }, { target := 304, numerator := 232113757366008801543585792 }, { target := 428, numerator := 178921021302965117856514048 }, { target := 429, numerator := 178921021302965117856514048 }, { target := 430, numerator := 178921021302965117856514048 }, { target := 431, numerator := 178921021302965117856514048 }, { target := 442, numerator := 169249614746048084458864640 }, { target := 443, numerator := 169249614746048084458864640 }, { target := 444, numerator := 169249614746048084458864640 }, { target := 445, numerator := 169249614746048084458864640 }, { target := 643, numerator := 89380915256647511426727936 }, { target := 645, numerator := 865750077633744584092680192 }, { target := 650, numerator := 89380915256647511426727936 }]

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
    Slot5.Left15.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 142, numerator := 99312128062941679363031040 }, { target := 143, numerator := 2648323415011778116347494400 }, { target := 144, numerator := 2532459265605012823757291520 }, { target := 145, numerator := 82760106719118066135859200 }, { target := 146, numerator := 2598667350980307276665978880 }, { target := 147, numerator := 82760106719118066135859200 }, { target := 148, numerator := 2532459265605012823757291520 }, { target := 149, numerator := 1440025856912654350763950080 }, { target := 150, numerator := 2598667350980307276665978880 }, { target := 151, numerator := 40569004313711676019798179840 }, { target := 152, numerator := 1588994049007066869808496640 }, { target := 153, numerator := 2648323415011778116347494400 }, { target := 154, numerator := 2532459265605012823757291520 }, { target := 155, numerator := 82760106719118066135859200 }, { target := 156, numerator := 1588994049007066869808496640 }, { target := 157, numerator := 82760106719118066135859200 }, { target := 158, numerator := 2549011286948836436984463360 }, { target := 159, numerator := 1440025856912654350763950080 }, { target := 160, numerator := 99312128062941679363031040 }, { target := 357, numerator := 961944530704160648991866880 }, { target := 358, numerator := 25651854152110950639783116800 }, { target := 359, numerator := 24529585532956096549292605440 }, { target := 360, numerator := 801620442253467207493222400 }, { target := 361, numerator := 25170881886758870315287183360 }, { target := 362, numerator := 801620442253467207493222400 }, { target := 363, numerator := 24529585532956096549292605440 }, { target := 364, numerator := 13948195695210329410382069760 }, { target := 365, numerator := 25170881886758870315287183360 }, { target := 366, numerator := 392954340792649625113177620480 }, { target := 367, numerator := 15391112491266570383869870080 }, { target := 368, numerator := 25651854152110950639783116800 }, { target := 369, numerator := 24529585532956096549292605440 }, { target := 370, numerator := 801620442253467207493222400 }, { target := 371, numerator := 15391112491266570383869870080 }, { target := 372, numerator := 801620442253467207493222400 }, { target := 373, numerator := 24689909621406789990791249920 }, { target := 374, numerator := 13948195695210329410382069760 }, { target := 375, numerator := 961944530704160648991866880 }, { target := 517, numerator := 227278054087550284844761088 }, { target := 518, numerator := 227278054087550284844761088 }, { target := 519, numerator := 227278054087550284844761088 }, { target := 520, numerator := 227278054087550284844761088 }, { target := 669, numerator := 99312128062941679363031040 }, { target := 670, numerator := 2648323415011778116347494400 }, { target := 671, numerator := 2532459265605012823757291520 }, { target := 672, numerator := 82760106719118066135859200 }, { target := 673, numerator := 2598667350980307276665978880 }, { target := 674, numerator := 82760106719118066135859200 }, { target := 675, numerator := 2532459265605012823757291520 }, { target := 676, numerator := 1440025856912654350763950080 }, { target := 677, numerator := 2598667350980307276665978880 }, { target := 678, numerator := 40569004313711676019798179840 }, { target := 679, numerator := 1588994049007066869808496640 }, { target := 680, numerator := 2648323415011778116347494400 }, { target := 681, numerator := 2532459265605012823757291520 }, { target := 682, numerator := 82760106719118066135859200 }, { target := 683, numerator := 1588994049007066869808496640 }, { target := 684, numerator := 82760106719118066135859200 }, { target := 685, numerator := 2549011286948836436984463360 }, { target := 686, numerator := 1440025856912654350763950080 }, { target := 687, numerator := 99312128062941679363031040 }]

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
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left6.expected,
    Slot8.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 55, numerator := 207743888285753610443161600 }, { target := 56, numerator := 213679427951060856455823360 }, { target := 57, numerator := 207743888285753610443161600 }, { target := 58, numerator := 184001729624524626392514560 }, { target := 59, numerator := 8612468054360813964372213760 }, { target := 60, numerator := 2344538167796362175001395200 }, { target := 61, numerator := 213679427951060856455823360 }, { target := 62, numerator := 8612468054360813964372213760 }, { target := 63, numerator := 207743888285753610443161600 }, { target := 64, numerator := 207743888285753610443161600 }, { target := 65, numerator := 178066189959217380379852800 }, { target := 66, numerator := 207743888285753610443161600 }, { target := 67, numerator := 2344538167796362175001395200 }, { target := 68, numerator := 178066189959217380379852800 }, { target := 69, numerator := 207743888285753610443161600 }, { target := 70, numerator := 184001729624524626392514560 }, { target := 100, numerator := 17394216045303247173278760960 }, { target := 101, numerator := 17891193646597625663943868416 }, { target := 102, numerator := 17394216045303247173278760960 }, { target := 103, numerator := 15406305640125733210618331136 }, { target := 104, numerator := 721114499478143189955070918656 }, { target := 105, numerator := 196306152511279503812717445120 }, { target := 106, numerator := 17891193646597625663943868416 }, { target := 107, numerator := 721114499478143189955070918656 }, { target := 108, numerator := 17394216045303247173278760960 }, { target := 109, numerator := 17394216045303247173278760960 }, { target := 110, numerator := 14909328038831354719953223680 }, { target := 111, numerator := 17394216045303247173278760960 }, { target := 112, numerator := 196306152511279503812717445120 }, { target := 113, numerator := 14909328038831354719953223680 }, { target := 114, numerator := 17394216045303247173278760960 }, { target := 115, numerator := 15406305640125733210618331136 }, { target := 315, numerator := 17394222340254662326663249920 }, { target := 316, numerator := 17891200121404795535996485632 }, { target := 317, numerator := 17394222340254662326663249920 }, { target := 318, numerator := 15406311215654129489330307072 }, { target := 319, numerator := 721114760448843286742525018112 }, { target := 320, numerator := 196306223554302617686628106240 }, { target := 321, numerator := 17891200121404795535996485632 }, { target := 322, numerator := 721114760448843286742525018112 }, { target := 323, numerator := 17394222340254662326663249920 }, { target := 324, numerator := 17394222340254662326663249920 }, { target := 325, numerator := 14909333434503996279997071360 }, { target := 326, numerator := 17394222340254662326663249920 }, { target := 327, numerator := 196306223554302617686628106240 }, { target := 328, numerator := 14909333434503996279997071360 }, { target := 329, numerator := 17394222340254662326663249920 }, { target := 330, numerator := 15406311215654129489330307072 }, { target := 653, numerator := 207737593334338457058672640 }, { target := 654, numerator := 213672953143890984403206144 }, { target := 655, numerator := 207737593334338457058672640 }, { target := 656, numerator := 183996154096128347680538624 }, { target := 657, numerator := 8612207083660717176918114304 }, { target := 658, numerator := 2344467124773248301090734080 }, { target := 659, numerator := 213672953143890984403206144 }, { target := 660, numerator := 8612207083660717176918114304 }, { target := 661, numerator := 207737593334338457058672640 }, { target := 662, numerator := 207737593334338457058672640 }, { target := 663, numerator := 178060794286575820336005120 }, { target := 664, numerator := 207737593334338457058672640 }, { target := 665, numerator := 2344467124773248301090734080 }, { target := 666, numerator := 178060794286575820336005120 }, { target := 667, numerator := 207737593334338457058672640 }, { target := 668, numerator := 183996154096128347680538624 }]

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
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected,
    Slot10.Left2.expected,
    Slot10.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 2, numerator := 1437377849859303436766412800 }, { target := 3, numerator := 1313790221647101645941637120 }, { target := 4, numerator := 1437377849859303436766412800 }, { target := 5, numerator := 1313790221647101645941637120 }, { target := 11, numerator := 10450858739772070612172800 }, { target := 12, numerator := 209435209145032295067942912 }, { target := 13, numerator := 351566888005932455393492992 }, { target := 14, numerator := 337353720119842439360937984 }, { target := 15, numerator := 10450858739772070612172800 }, { target := 16, numerator := 337353720119842439360937984 }, { target := 17, numerator := 225320514429485842398445568 }, { target := 18, numerator := 10868893089362953436659712 }, { target := 19, numerator := 209435209145032295067942912 }, { target := 20, numerator := 10032824390181187787685888 }, { target := 22, numerator := 50304641061516775594026598400 }, { target := 23, numerator := 45979382203891034141082255360 }, { target := 24, numerator := 50304641061516775594026598400 }, { target := 25, numerator := 45979382203891034141082255360 }, { target := 31, numerator := 1095753690039653162496819200 }, { target := 32, numerator := 21958903948394649376436256768 }, { target := 33, numerator := 36861154132933932386392997888 }, { target := 34, numerator := 35370929114480004085397323776 }, { target := 35, numerator := 1095753690039653162496819200 }, { target := 36, numerator := 35370929114480004085397323776 }, { target := 37, numerator := 23624449557254922183431421952 }, { target := 38, numerator := 1139583837641239288996691968 }, { target := 39, numerator := 21958903948394649376436256768 }, { target := 40, numerator := 1051923542438067035996946432 }, { target := 72, numerator := 50304665734036974180551884800 }, { target := 73, numerator := 45979404755035664251009105920 }, { target := 74, numerator := 50304665734036974180551884800 }, { target := 75, numerator := 45979404755035664251009105920 }, { target := 76, numerator := 11811129574102757120409600000 }, { target := 77, numerator := 236695036665019252693008384000 }, { target := 78, numerator := 397326398872816749530578944000 }, { target := 79, numerator := 381263262652036999846821888000 }, { target := 80, numerator := 11811129574102757120409600000 }, { target := 81, numerator := 381263262652036999846821888000 }, { target := 82, numerator := 254647953617655443516030976000 }, { target := 83, numerator := 12283574757066867405225984000 }, { target := 84, numerator := 236695036665019252693008384000 }, { target := 85, numerator := 11338684391138646835593216000 }, { target := 305, numerator := 1095754525907744002460876800 }, { target := 306, numerator := 21958920699191189809315971072 }, { target := 307, numerator := 36861182251536508242783895552 }, { target := 308, numerator := 35370956096301976399437103104 }, { target := 309, numerator := 1095754525907744002460876800 }, { target := 310, numerator := 35370956096301976399437103104 }, { target := 311, numerator := 23624467578570960693056503808 }, { target := 312, numerator := 1139584706944053762559311872 }, { target := 313, numerator := 21958920699191189809315971072 }, { target := 314, numerator := 1051924344871434242362441728 }, { target := 643, numerator := 10450858739772070612172800 }, { target := 644, numerator := 209435209145032295067942912 }, { target := 645, numerator := 351566888005932455393492992 }, { target := 646, numerator := 337353720119842439360937984 }, { target := 647, numerator := 10450858739772070612172800 }, { target := 648, numerator := 337353720119842439360937984 }, { target := 649, numerator := 225320514429485842398445568 }, { target := 650, numerator := 10868893089362953436659712 }, { target := 651, numerator := 209435209145032295067942912 }, { target := 652, numerator := 10032824390181187787685888 }]

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
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 14620257736305106795794268160 }, { target := 21, numerator := 49987651764020606871600627712 }, { target := 71, numerator := 14620253013938623926149054464 }, { target := 301, numerator := 1437365513599204143503769600 }, { target := 302, numerator := 1313778946074786590978211840 }, { target := 303, numerator := 1437365513599204143503769600 }, { target := 304, numerator := 1313778946074786590978211840 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk0.Parent3
