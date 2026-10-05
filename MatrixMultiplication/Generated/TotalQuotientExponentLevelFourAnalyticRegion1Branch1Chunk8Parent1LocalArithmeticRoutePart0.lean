import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk8Parent1LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 1,
parent 35; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent1

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
    Slot0.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 77522368182788095828033536 }, { target := 35, numerator := 58141776137091071871025152 }, { target := 36, numerator := 61371874811373909197193216 }, { target := 37, numerator := 79137417519929514491117568 }, { target := 38, numerator := 1059472365164770642983124992 }, { target := 39, numerator := 1852461589701207206557384704 }, { target := 40, numerator := 56526726799949653207941120 }, { target := 41, numerator := 1059472365164770642983124992 }, { target := 42, numerator := 59756825474232490534109184 }, { target := 43, numerator := 61371874811373909197193216 }, { target := 44, numerator := 61371874811373909197193216 }, { target := 45, numerator := 59756825474232490534109184 }, { target := 46, numerator := 1852461589701207206557384704 }, { target := 47, numerator := 59756825474232490534109184 }, { target := 48, numerator := 77522368182788095828033536 }, { target := 49, numerator := 79137417519929514491117568 }, { target := 79, numerator := 1124074338650427389506486272 }, { target := 80, numerator := 843055753987820542129864704 }, { target := 81, numerator := 889892184764921683359301632 }, { target := 82, numerator := 1147492554038977960121204736 }, { target := 83, numerator := 15362349294889174323255312384 }, { target := 84, numerator := 26860693050667504495082078208 }, { target := 85, numerator := 819637538599269971515146240 }, { target := 86, numerator := 15362349294889174323255312384 }, { target := 87, numerator := 866473969376371112744583168 }, { target := 88, numerator := 889892184764921683359301632 }, { target := 89, numerator := 889892184764921683359301632 }, { target := 90, numerator := 866473969376371112744583168 }, { target := 91, numerator := 26860693050667504495082078208 }, { target := 92, numerator := 866473969376371112744583168 }, { target := 93, numerator := 1124074338650427389506486272 }, { target := 94, numerator := 1147492554038977960121204736 }, { target := 105, numerator := 1989740783358227792919527424 }, { target := 106, numerator := 1492305587518670844689645568 }, { target := 107, numerator := 1575211453491930336061292544 }, { target := 108, numerator := 2031193716344857538605350912 }, { target := 109, numerator := 27193124039229113169900208128 }, { target := 110, numerator := 47546514135664318301639540736 }, { target := 111, numerator := 1450852654532041099003822080 }, { target := 112, numerator := 27193124039229113169900208128 }, { target := 113, numerator := 1533758520505300590375469056 }, { target := 114, numerator := 1575211453491930336061292544 }, { target := 115, numerator := 1575211453491930336061292544 }, { target := 116, numerator := 1533758520505300590375469056 }, { target := 117, numerator := 47546514135664318301639540736 }, { target := 118, numerator := 1533758520505300590375469056 }, { target := 119, numerator := 1989740783358227792919527424 }, { target := 120, numerator := 2031193716344857538605350912 }, { target := 154, numerator := 64601973485656746523361280 }, { target := 155, numerator := 48451480114242559892520960 }, { target := 156, numerator := 51143229009478257664327680 }, { target := 157, numerator := 65947847933274595409264640 }, { target := 158, numerator := 882893637637308869152604160 }, { target := 159, numerator := 1543717991417672672131153920 }, { target := 160, numerator := 47105605666624711006617600 }, { target := 161, numerator := 882893637637308869152604160 }, { target := 162, numerator := 49797354561860408778424320 }, { target := 163, numerator := 51143229009478257664327680 }, { target := 164, numerator := 51143229009478257664327680 }, { target := 165, numerator := 49797354561860408778424320 }, { target := 166, numerator := 1543717991417672672131153920 }, { target := 167, numerator := 49797354561860408778424320 }, { target := 168, numerator := 64601973485656746523361280 }, { target := 169, numerator := 65947847933274595409264640 }]

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
    Slot0.Left4.expected,
    Slot0.Left5.expected,
    Slot0.Left6.expected,
    Slot0.Left7.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 180, numerator := 1240357890924609533248536576 }, { target := 181, numerator := 930268418193457149936402432 }, { target := 182, numerator := 981949996981982547155091456 }, { target := 183, numerator := 1266198680318872231857881088 }, { target := 184, numerator := 16951557842636330287729999872 }, { target := 185, numerator := 29639385435219315304918155264 }, { target := 186, numerator := 904427628799194451327057920 }, { target := 187, numerator := 16951557842636330287729999872 }, { target := 188, numerator := 956109207587719848545746944 }, { target := 189, numerator := 981949996981982547155091456 }, { target := 190, numerator := 981949996981982547155091456 }, { target := 191, numerator := 956109207587719848545746944 }, { target := 192, numerator := 29639385435219315304918155264 }, { target := 193, numerator := 956109207587719848545746944 }, { target := 194, numerator := 1240357890924609533248536576 }, { target := 195, numerator := 1266198680318872231857881088 }, { target := 215, numerator := 64601973485656746523361280 }, { target := 216, numerator := 48451480114242559892520960 }, { target := 217, numerator := 51143229009478257664327680 }, { target := 218, numerator := 65947847933274595409264640 }, { target := 219, numerator := 882893637637308869152604160 }, { target := 220, numerator := 1543717991417672672131153920 }, { target := 221, numerator := 47105605666624711006617600 }, { target := 222, numerator := 882893637637308869152604160 }, { target := 223, numerator := 49797354561860408778424320 }, { target := 224, numerator := 51143229009478257664327680 }, { target := 225, numerator := 51143229009478257664327680 }, { target := 226, numerator := 49797354561860408778424320 }, { target := 227, numerator := 1543717991417672672131153920 }, { target := 228, numerator := 49797354561860408778424320 }, { target := 229, numerator := 64601973485656746523361280 }, { target := 230, numerator := 65947847933274595409264640 }, { target := 295, numerator := 1976820388661096443614855168 }, { target := 296, numerator := 1482615291495822332711141376 }, { target := 297, numerator := 1564982807690034684528427008 }, { target := 298, numerator := 2018004146758202619523497984 }, { target := 299, numerator := 27016545311701651396069687296 }, { target := 300, numerator := 47237770537380783767213309952 }, { target := 301, numerator := 1441431533398716156802498560 }, { target := 302, numerator := 27016545311701651396069687296 }, { target := 303, numerator := 1523799049592928508619784192 }, { target := 304, numerator := 1564982807690034684528427008 }, { target := 305, numerator := 1564982807690034684528427008 }, { target := 306, numerator := 1523799049592928508619784192 }, { target := 307, numerator := 47237770537380783767213309952 }, { target := 308, numerator := 1523799049592928508619784192 }, { target := 309, numerator := 1976820388661096443614855168 }, { target := 310, numerator := 2018004146758202619523497984 }, { target := 321, numerator := 2067263151541015888747560960 }, { target := 322, numerator := 1550447363655761916560670720 }, { target := 323, numerator := 1636583328303304245258485760 }, { target := 324, numerator := 2110331133864787053096468480 }, { target := 325, numerator := 28252596404393883812883333120 }, { target := 326, numerator := 49398975725365525508196925440 }, { target := 327, numerator := 1507379381331990752211763200 }, { target := 328, numerator := 28252596404393883812883333120 }, { target := 329, numerator := 1593515345979533080909578240 }, { target := 330, numerator := 1636583328303304245258485760 }, { target := 331, numerator := 1636583328303304245258485760 }, { target := 332, numerator := 1593515345979533080909578240 }, { target := 333, numerator := 49398975725365525508196925440 }, { target := 334, numerator := 1593515345979533080909578240 }, { target := 335, numerator := 2067263151541015888747560960 }, { target := 336, numerator := 2110331133864787053096468480 }]

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
    Slot0.Left8.expected,
    Slot0.Left9.expected,
    Slot0.Left10.expected,
    Slot0.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 370, numerator := 1240357890924609533248536576 }, { target := 371, numerator := 930268418193457149936402432 }, { target := 372, numerator := 981949996981982547155091456 }, { target := 373, numerator := 1266198680318872231857881088 }, { target := 374, numerator := 16951557842636330287729999872 }, { target := 375, numerator := 29639385435219315304918155264 }, { target := 376, numerator := 904427628799194451327057920 }, { target := 377, numerator := 16951557842636330287729999872 }, { target := 378, numerator := 956109207587719848545746944 }, { target := 379, numerator := 981949996981982547155091456 }, { target := 380, numerator := 981949996981982547155091456 }, { target := 381, numerator := 956109207587719848545746944 }, { target := 382, numerator := 29639385435219315304918155264 }, { target := 383, numerator := 956109207587719848545746944 }, { target := 384, numerator := 1240357890924609533248536576 }, { target := 385, numerator := 1266198680318872231857881088 }, { target := 396, numerator := 31667887402668937145751699456 }, { target := 397, numerator := 23750915552001702859313774592 }, { target := 398, numerator := 25070410860446241907053428736 }, { target := 399, numerator := 32327635056891206669621526528 }, { target := 400, numerator := 432794461169808807658606559232 }, { target := 401, numerator := 756730559392943143878691651584 }, { target := 402, numerator := 23091167897779433335443947520 }, { target := 403, numerator := 432794461169808807658606559232 }, { target := 404, numerator := 24410663206223972383183601664 }, { target := 405, numerator := 25070410860446241907053428736 }, { target := 406, numerator := 25070410860446241907053428736 }, { target := 407, numerator := 24410663206223972383183601664 }, { target := 408, numerator := 756730559392943143878691651584 }, { target := 409, numerator := 24410663206223972383183601664 }, { target := 410, numerator := 31667887402668937145751699456 }, { target := 411, numerator := 32327635056891206669621526528 }, { target := 431, numerator := 2028501967449621840833544192 }, { target := 432, numerator := 1521376475587216380625158144 }, { target := 433, numerator := 1605897390897617290659889152 }, { target := 434, numerator := 2070762425104822295850909696 }, { target := 435, numerator := 27722860221811498491391770624 }, { target := 436, numerator := 48472744930514921904918233088 }, { target := 437, numerator := 1479116017932015925607792640 }, { target := 438, numerator := 27722860221811498491391770624 }, { target := 439, numerator := 1563636933242416835642523648 }, { target := 440, numerator := 1605897390897617290659889152 }, { target := 441, numerator := 1605897390897617290659889152 }, { target := 442, numerator := 1563636933242416835642523648 }, { target := 443, numerator := 48472744930514921904918233088 }, { target := 444, numerator := 1563636933242416835642523648 }, { target := 445, numerator := 2028501967449621840833544192 }, { target := 446, numerator := 2070762425104822295850909696 }, { target := 492, numerator := 1124074338650427389506486272 }, { target := 493, numerator := 843055753987820542129864704 }, { target := 494, numerator := 889892184764921683359301632 }, { target := 495, numerator := 1147492554038977960121204736 }, { target := 496, numerator := 15362349294889174323255312384 }, { target := 497, numerator := 26860693050667504495082078208 }, { target := 498, numerator := 819637538599269971515146240 }, { target := 499, numerator := 15362349294889174323255312384 }, { target := 500, numerator := 866473969376371112744583168 }, { target := 501, numerator := 889892184764921683359301632 }, { target := 502, numerator := 889892184764921683359301632 }, { target := 503, numerator := 866473969376371112744583168 }, { target := 504, numerator := 26860693050667504495082078208 }, { target := 505, numerator := 866473969376371112744583168 }, { target := 506, numerator := 1124074338650427389506486272 }, { target := 507, numerator := 1147492554038977960121204736 }]

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
    Slot0.Left12.expected,
    Slot0.Left13.expected,
    Slot0.Left14.expected,
    Slot0.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 527, numerator := 1976820388661096443614855168 }, { target := 528, numerator := 1482615291495822332711141376 }, { target := 529, numerator := 1564982807690034684528427008 }, { target := 530, numerator := 2018004146758202619523497984 }, { target := 531, numerator := 27016545311701651396069687296 }, { target := 532, numerator := 47237770537380783767213309952 }, { target := 533, numerator := 1441431533398716156802498560 }, { target := 534, numerator := 27016545311701651396069687296 }, { target := 535, numerator := 1523799049592928508619784192 }, { target := 536, numerator := 1564982807690034684528427008 }, { target := 537, numerator := 1564982807690034684528427008 }, { target := 538, numerator := 1523799049592928508619784192 }, { target := 539, numerator := 47237770537380783767213309952 }, { target := 540, numerator := 1523799049592928508619784192 }, { target := 541, numerator := 1976820388661096443614855168 }, { target := 542, numerator := 2018004146758202619523497984 }, { target := 637, numerator := 64601973485656746523361280 }, { target := 638, numerator := 48451480114242559892520960 }, { target := 639, numerator := 51143229009478257664327680 }, { target := 640, numerator := 65947847933274595409264640 }, { target := 641, numerator := 882893637637308869152604160 }, { target := 642, numerator := 1543717991417672672131153920 }, { target := 643, numerator := 47105605666624711006617600 }, { target := 644, numerator := 882893637637308869152604160 }, { target := 645, numerator := 49797354561860408778424320 }, { target := 646, numerator := 51143229009478257664327680 }, { target := 647, numerator := 51143229009478257664327680 }, { target := 648, numerator := 49797354561860408778424320 }, { target := 649, numerator := 1543717991417672672131153920 }, { target := 650, numerator := 49797354561860408778424320 }, { target := 651, numerator := 64601973485656746523361280 }, { target := 652, numerator := 65947847933274595409264640 }, { target := 663, numerator := 2028501967449621840833544192 }, { target := 664, numerator := 1521376475587216380625158144 }, { target := 665, numerator := 1605897390897617290659889152 }, { target := 666, numerator := 2070762425104822295850909696 }, { target := 667, numerator := 27722860221811498491391770624 }, { target := 668, numerator := 48472744930514921904918233088 }, { target := 669, numerator := 1479116017932015925607792640 }, { target := 670, numerator := 27722860221811498491391770624 }, { target := 671, numerator := 1563636933242416835642523648 }, { target := 672, numerator := 1605897390897617290659889152 }, { target := 673, numerator := 1605897390897617290659889152 }, { target := 674, numerator := 1563636933242416835642523648 }, { target := 675, numerator := 48472744930514921904918233088 }, { target := 676, numerator := 1563636933242416835642523648 }, { target := 677, numerator := 2028501967449621840833544192 }, { target := 678, numerator := 2070762425104822295850909696 }, { target := 698, numerator := 64601973485656746523361280 }, { target := 699, numerator := 48451480114242559892520960 }, { target := 700, numerator := 51143229009478257664327680 }, { target := 701, numerator := 65947847933274595409264640 }, { target := 702, numerator := 882893637637308869152604160 }, { target := 703, numerator := 1543717991417672672131153920 }, { target := 704, numerator := 47105605666624711006617600 }, { target := 705, numerator := 882893637637308869152604160 }, { target := 706, numerator := 49797354561860408778424320 }, { target := 707, numerator := 51143229009478257664327680 }, { target := 708, numerator := 51143229009478257664327680 }, { target := 709, numerator := 49797354561860408778424320 }, { target := 710, numerator := 1543717991417672672131153920 }, { target := 711, numerator := 49797354561860408778424320 }, { target := 712, numerator := 64601973485656746523361280 }, { target := 713, numerator := 65947847933274595409264640 }]

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
    Slot0.Left16.expected,
    Slot0.Left17.expected,
    Slot0.Left18.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 121, numerator := 175135122229741411740155904 }, { target := 122, numerator := 20699847039183142753564360704 }, { target := 124, numerator := 196437422163851522457986924544 }, { target := 132, numerator := 20699861236258550482278023168 }, { target := 139, numerator := 175135122229741411740155904 }, { target := 196, numerator := 130419771873211689593733120 }, { target := 197, numerator := 15414779710029999922867077120 }, { target := 199, numerator := 146283186717761772043181752320 }, { target := 207, numerator := 15414790282320197167653847040 }, { target := 214, numerator := 130419771873211689593733120 }, { target := 231, numerator := 137872330265966643284803584 }, { target := 232, numerator := 16295624264888857061316624384 }, { target := 234, numerator := 154642225958776730445649281024 }, { target := 242, numerator := 16295635441309922720091209728 }, { target := 249, numerator := 137872330265966643284803584 }, { target := 759, numerator := 1976820388661096443614855168 }, { target := 760, numerator := 1482615291495822332711141376 }, { target := 761, numerator := 1564982807690034684528427008 }, { target := 762, numerator := 2018004146758202619523497984 }, { target := 763, numerator := 27016545311701651396069687296 }, { target := 764, numerator := 47237770537380783767213309952 }, { target := 765, numerator := 1441431533398716156802498560 }, { target := 766, numerator := 27016545311701651396069687296 }, { target := 767, numerator := 1523799049592928508619784192 }, { target := 768, numerator := 1564982807690034684528427008 }, { target := 769, numerator := 1564982807690034684528427008 }, { target := 770, numerator := 1523799049592928508619784192 }, { target := 771, numerator := 47237770537380783767213309952 }, { target := 772, numerator := 1523799049592928508619784192 }, { target := 773, numerator := 1976820388661096443614855168 }, { target := 774, numerator := 2018004146758202619523497984 }, { target := 794, numerator := 2067263151541015888747560960 }, { target := 795, numerator := 1550447363655761916560670720 }, { target := 796, numerator := 1636583328303304245258485760 }, { target := 797, numerator := 2110331133864787053096468480 }, { target := 798, numerator := 28252596404393883812883333120 }, { target := 799, numerator := 49398975725365525508196925440 }, { target := 800, numerator := 1507379381331990752211763200 }, { target := 801, numerator := 28252596404393883812883333120 }, { target := 802, numerator := 1593515345979533080909578240 }, { target := 803, numerator := 1636583328303304245258485760 }, { target := 804, numerator := 1636583328303304245258485760 }, { target := 805, numerator := 1593515345979533080909578240 }, { target := 806, numerator := 49398975725365525508196925440 }, { target := 807, numerator := 1593515345979533080909578240 }, { target := 808, numerator := 2067263151541015888747560960 }, { target := 809, numerator := 2110331133864787053096468480 }, { target := 890, numerator := 77522368182788095828033536 }, { target := 891, numerator := 58141776137091071871025152 }, { target := 892, numerator := 61371874811373909197193216 }, { target := 893, numerator := 79137417519929514491117568 }, { target := 894, numerator := 1059472365164770642983124992 }, { target := 895, numerator := 1852461589701207206557384704 }, { target := 896, numerator := 56526726799949653207941120 }, { target := 897, numerator := 1059472365164770642983124992 }, { target := 898, numerator := 59756825474232490534109184 }, { target := 899, numerator := 61371874811373909197193216 }, { target := 900, numerator := 61371874811373909197193216 }, { target := 901, numerator := 59756825474232490534109184 }, { target := 902, numerator := 1852461589701207206557384704 }, { target := 903, numerator := 59756825474232490534109184 }, { target := 904, numerator := 77522368182788095828033536 }, { target := 905, numerator := 79137417519929514491117568 }]

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
    Slot1.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 337, numerator := 178861401426118888585691136 }, { target := 338, numerator := 21140269316612571322789134336 }, { target := 340, numerator := 200616941784359001659220688896 }, { target := 348, numerator := 21140283815753413258496704512 }, { target := 355, numerator := 178861401426118888585691136 }, { target := 412, numerator := 2395997523270717611679154176 }, { target := 413, numerator := 283191524387122570011529445376 }, { target := 415, numerator := 2687431115986309126393310478336 }, { target := 423, numerator := 283191718615196765108612104192 }, { target := 430, numerator := 2395997523270717611679154176 }, { target := 447, numerator := 4333662705387005571357474816 }, { target := 448, numerator := 512211108650425426008411734016 }, { target := 450, numerator := 4860781318650198311034867941376 }, { target := 458, numerator := 512211459952525408742326403072 }, { target := 465, numerator := 4333662705387005571357474816 }, { target := 508, numerator := 130419771873211689593733120 }, { target := 509, numerator := 15414779710029999922867077120 }, { target := 511, numerator := 146283186717761772043181752320 }, { target := 519, numerator := 15414790282320197167653847040 }, { target := 526, numerator := 130419771873211689593733120 }, { target := 543, numerator := 2395997523270717611679154176 }, { target := 544, numerator := 283191524387122570011529445376 }, { target := 546, numerator := 2687431115986309126393310478336 }, { target := 554, numerator := 283191718615196765108612104192 }, { target := 561, numerator := 2395997523270717611679154176 }, { target := 578, numerator := 141598609462344120130338816 }, { target := 579, numerator := 16736046542318285630541398016 }, { target := 581, numerator := 158821745579284209646883045376 }, { target := 589, numerator := 16736058020804785496309891072 }, { target := 596, numerator := 141598609462344120130338816 }, { target := 679, numerator := 141598609462344120130338816 }, { target := 680, numerator := 16736046542318285630541398016 }, { target := 682, numerator := 158821745579284209646883045376 }, { target := 690, numerator := 16736058020804785496309891072 }, { target := 697, numerator := 141598609462344120130338816 }, { target := 714, numerator := 137872330265966643284803584 }, { target := 715, numerator := 16295624264888857061316624384 }, { target := 717, numerator := 154642225958776730445649281024 }, { target := 725, numerator := 16295635441309922720091209728 }, { target := 732, numerator := 137872330265966643284803584 }, { target := 775, numerator := 137872330265966643284803584 }, { target := 776, numerator := 16295624264888857061316624384 }, { target := 778, numerator := 154642225958776730445649281024 }, { target := 786, numerator := 16295635441309922720091209728 }, { target := 793, numerator := 137872330265966643284803584 }, { target := 810, numerator := 4333662705387005571357474816 }, { target := 811, numerator := 512211108650425426008411734016 }, { target := 813, numerator := 4860781318650198311034867941376 }, { target := 821, numerator := 512211459952525408742326403072 }, { target := 828, numerator := 4333662705387005571357474816 }, { target := 845, numerator := 137872330265966643284803584 }, { target := 846, numerator := 16295624264888857061316624384 }, { target := 848, numerator := 154642225958776730445649281024 }, { target := 856, numerator := 16295635441309922720091209728 }, { target := 863, numerator := 137872330265966643284803584 }, { target := 906, numerator := 175135122229741411740155904 }, { target := 907, numerator := 20699847039183142753564360704 }, { target := 909, numerator := 196437422163851522457986924544 }, { target := 917, numerator := 20699861236258550482278023168 }, { target := 924, numerator := 175135122229741411740155904 }]

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
    Slot2.Left9.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected,
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot4.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 250, numerator := 545319915883035846644858880 }, { target := 252, numerator := 21341073122420210732235751424 }, { target := 255, numerator := 21341073122420210732235751424 }, { target := 262, numerator := 545319915883035846644858880 }, { target := 466, numerator := 13369133421648620756454604800 }, { target := 468, numerator := 523200502356108392145134551040 }, { target := 471, numerator := 523200502356108392145134551040 }, { target := 478, numerator := 13369133421648620756454604800 }, { target := 562, numerator := 9886122346008585348851957760 }, { target := 564, numerator := 386893003058069626823112654848 }, { target := 567, numerator := 386893003058069626823112654848 }, { target := 574, numerator := 9886122346008585348851957760 }, { target := 597, numerator := 11029535072860112124075048960 }, { target := 599, numerator := 431640414443789423519736004608 }, { target := 602, numerator := 431640414443789423519736004608 }, { target := 609, numerator := 11029535072860112124075048960 }, { target := 613, numerator := 48714638764207185962828038144 }, { target := 616, numerator := 180962743184895395868641853440 }, { target := 618, numerator := 48704384385197307486470668288 }, { target := 733, numerator := 545319915883035846644858880 }, { target := 735, numerator := 21341073122420210732235751424 }, { target := 738, numerator := 21341073122420210732235751424 }, { target := 745, numerator := 545319915883035846644858880 }, { target := 829, numerator := 11011944107831627096763924480 }, { target := 831, numerator := 430951992730162965109018722304 }, { target := 834, numerator := 430951992730162965109018722304 }, { target := 841, numerator := 11011944107831627096763924480 }, { target := 864, numerator := 11205444723144962397186293760 }, { target := 866, numerator := 438524631580054007626908827648 }, { target := 869, numerator := 438524631580054007626908827648 }, { target := 876, numerator := 11205444723144962397186293760 }, { target := 880, numerator := 48572475421510083280057139200 }, { target := 883, numerator := 180434641794277996853460992000 }, { target := 885, numerator := 48562250967730778379019878400 }, { target := 925, numerator := 545319915883035846644858880 }, { target := 927, numerator := 21341073122420210732235751424 }, { target := 930, numerator := 21341073122420210732235751424 }, { target := 937, numerator := 545319915883035846644858880 }, { target := 941, numerator := 178861401426118888585691136 }, { target := 942, numerator := 21140269316612571322789134336 }, { target := 944, numerator := 200616941784359001659220688896 }, { target := 952, numerator := 21140283815753413258496704512 }, { target := 959, numerator := 178861401426118888585691136 }, { target := 960, numerator := 13369133421648620756454604800 }, { target := 962, numerator := 523200502356108392145134551040 }, { target := 965, numerator := 523200502356108392145134551040 }, { target := 972, numerator := 13369133421648620756454604800 }, { target := 976, numerator := 48240760955216843686925041664 }, { target := 979, numerator := 179202405216170732484705648640 }, { target := 981, numerator := 48230606326975543794968035328 }, { target := 986, numerator := 545319915883035846644858880 }, { target := 988, numerator := 21341073122420210732235751424 }, { target := 991, numerator := 21341073122420210732235751424 }, { target := 998, numerator := 545319915883035846644858880 }, { target := 1002, numerator := 48572475421510083280057139200 }, { target := 1005, numerator := 180434641794277996853460992000 }, { target := 1007, numerator := 48562250967730778379019878400 }, { target := 1012, numerator := 118842229604297057781380284416 }, { target := 1014, numerator := 118842257938495954999251566592 }]

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
    Slot5.Left0.expected,
    Slot5.Left2.expected,
    Slot5.Left5.expected,
    Slot5.Left12.expected,
    Slot6.Left0.expected,
    Slot6.Left1.expected,
    Slot6.Left3.expected,
    Slot6.Left11.expected,
    Slot6.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 190219373041108103364345856 }, { target := 11, numerator := 4608217714641038246020120576 }, { target := 12, numerator := 3491445911625500348848799744 }, { target := 13, numerator := 3890292984131049597838557184 }, { target := 14, numerator := 190219373041108103364345856 }, { target := 15, numerator := 3890292984131049597838557184 }, { target := 16, numerator := 3884156875323271917084868608 }, { target := 17, numerator := 190219373041108103364345856 }, { target := 18, numerator := 4608217714641038246020120576 }, { target := 19, numerator := 190219373041108103364345856 }, { target := 34, numerator := 55895503889591970994061312 }, { target := 35, numerator := 9803546241642344959774294016 }, { target := 40, numerator := 9803547416979390811951071232 }, { target := 48, numerator := 55894328552546118817284096 }, { target := 55, numerator := 7604935241088753528259739648 }, { target := 56, numerator := 184235689227666254829776273408 }, { target := 57, numerator := 139587359747725830889670705152 }, { target := 58, numerator := 155533191704847410868279836672 }, { target := 59, numerator := 7604935241088753528259739648 }, { target := 60, numerator := 155533191704847410868279836672 }, { target := 61, numerator := 155287871213199386560916619264 }, { target := 62, numerator := 7604935241088753528259739648 }, { target := 63, numerator := 184235689227666254829776273408 }, { target := 64, numerator := 7604935241088753528259739648 }, { target := 79, numerator := 9160196571547991245523517440 }, { target := 80, numerator := 1606612418220386986699438161920 }, { target := 85, numerator := 1606612610835492471654150307840 }, { target := 93, numerator := 9160003956442506290811371520 }, { target := 144, numerator := 7604933382579288102022414336 }, { target := 145, numerator := 184235644203775656923188166656 }, { target := 146, numerator := 139587325635084352582282379264 }, { target := 147, numerator := 155533153695331246989748731904 }, { target := 148, numerator := 7604933382579288102022414336 }, { target := 149, numerator := 155533153695331246989748731904 }, { target := 150, numerator := 155287833263635140921941557248 }, { target := 151, numerator := 7604933382579288102022414336 }, { target := 152, numerator := 184235644203775656923188166656 }, { target := 153, numerator := 7604933382579288102022414336 }, { target := 154, numerator := 94307770427692355715690659840 }, { target := 155, numerator := 16540696907577722550512380805120 }, { target := 160, numerator := 16540698890624811889460500234240 }, { target := 168, numerator := 94305787380603016767571230720 }, { target := 482, numerator := 190219373041108103364345856 }, { target := 483, numerator := 4608217714641038246020120576 }, { target := 484, numerator := 3491445911625500348848799744 }, { target := 485, numerator := 3890292984131049597838557184 }, { target := 486, numerator := 190219373041108103364345856 }, { target := 487, numerator := 3890292984131049597838557184 }, { target := 488, numerator := 3884156875323271917084868608 }, { target := 489, numerator := 190219373041108103364345856 }, { target := 490, numerator := 4608217714641038246020120576 }, { target := 491, numerator := 190219373041108103364345856 }, { target := 492, numerator := 9160196571547991245523517440 }, { target := 493, numerator := 1606612418220386986699438161920 }, { target := 498, numerator := 1606612610835492471654150307840 }, { target := 506, numerator := 9160003956442506290811371520 }, { target := 890, numerator := 55895503889591970994061312 }, { target := 891, numerator := 9803546241642344959774294016 }, { target := 896, numerator := 9803547416979390811951071232 }, { target := 904, numerator := 55894328552546118817284096 }]

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
    Slot7.Left0.expected,
    Slot7.Left1.expected,
    Slot7.Left6.expected,
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
    Slot11.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 1, numerator := 28373366204826792119578394624 }, { target := 2, numerator := 28373366204826792119578394624 }, { target := 3, numerator := 28373366204826792119578394624 }, { target := 4, numerator := 28373366204826792119578394624 }, { target := 10, numerator := 1860929517917183584373833728 }, { target := 12, numerator := 84110628731071461124397334528 }, { target := 17, numerator := 1870861861337527504884203520 }, { target := 51, numerator := 101701347366996000547387998208 }, { target := 52, numerator := 101701347366996000547387998208 }, { target := 53, numerator := 101701347366996000547387998208 }, { target := 54, numerator := 101701347366996000547387998208 }, { target := 55, numerator := 72829519749310600581461573632 }, { target := 57, numerator := 3291761798239750696085154168832 }, { target := 62, numerator := 73218232913524627837162618880 }, { target := 121, numerator := 38358908958295641670287360 }, { target := 122, numerator := 12356223891969048030656593920 }, { target := 124, numerator := 131413637233588307553027096576 }, { target := 132, numerator := 12356261133628230841959186432 }, { target := 139, numerator := 38358908958295641670287360 }, { target := 140, numerator := 28381611456705882520121507840 }, { target := 141, numerator := 28381611456705882520121507840 }, { target := 142, numerator := 28381611456705882520121507840 }, { target := 143, numerator := 28381611456705882520121507840 }, { target := 196, numerator := 7607908005444919102537728000 }, { target := 197, numerator := 2450669667559749984888815616000 }, { target := 199, numerator := 26063902490579940800300109004800 }, { target := 207, numerator := 2450677053878201873159788953600 }, { target := 214, numerator := 7607908005444919102537728000 }, { target := 250, numerator := 1777292236213040501930065920 }, { target := 252, numerator := 69556282906644955611508244480 }, { target := 255, numerator := 69556308417528520706537553920 }, { target := 262, numerator := 1777317747096605596959375360 }, { target := 508, numerator := 7607908005444919102537728000 }, { target := 509, numerator := 2450669667559749984888815616000 }, { target := 511, numerator := 26063902490579940800300109004800 }, { target := 519, numerator := 2450677053878201873159788953600 }, { target := 526, numerator := 7607908005444919102537728000 }, { target := 562, numerator := 80330375754394092085098577920 }, { target := 564, numerator := 3143817447757065271542001172480 }, { target := 567, numerator := 3143818600802591975252342865920 }, { target := 574, numerator := 80331528799920795795440271360 }, { target := 613, numerator := 28373366204826792119578394624 }, { target := 616, numerator := 101701347366996000547387998208 }, { target := 618, numerator := 28381611456705882520121507840 }, { target := 880, numerator := 28373366204826792119578394624 }, { target := 883, numerator := 101701347366996000547387998208 }, { target := 885, numerator := 28381611456705882520121507840 }, { target := 906, numerator := 38358908958295641670287360 }, { target := 907, numerator := 12356223891969048030656593920 }, { target := 909, numerator := 131413637233588307553027096576 }, { target := 917, numerator := 12356261133628230841959186432 }, { target := 924, numerator := 38358908958295641670287360 }, { target := 925, numerator := 1786778182176290313653452800 }, { target := 927, numerator := 69927525816287565911896883200 }, { target := 930, numerator := 69927551463330428866055372800 }, { target := 937, numerator := 1786803829219153267811942400 }, { target := 976, numerator := 28373366204826792119578394624 }, { target := 979, numerator := 101701347366996000547387998208 }, { target := 981, numerator := 28381611456705882520121507840 }, { target := 1002, numerator := 28373366204826792119578394624 }, { target := 1005, numerator := 101701347366996000547387998208 }, { target := 1007, numerator := 28381611456705882520121507840 }]

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
    Slot14.Left0.expected,
    Slot14.Left1.expected,
    Slot14.Left2.expected,
    Slot14.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 38358908958295641670287360 }, { target := 35, numerator := 7607908005444919102537728000 }, { target := 40, numerator := 7607908005444919102537728000 }, { target := 48, numerator := 38358908958295641670287360 }, { target := 79, numerator := 12356223891969048030656593920 }, { target := 80, numerator := 2450669667559749984888815616000 }, { target := 85, numerator := 2450669667559749984888815616000 }, { target := 93, numerator := 12356223891969048030656593920 }, { target := 121, numerator := 55784158264313899338694656 }, { target := 122, numerator := 9141949168019011183281438720 }, { target := 124, numerator := 94119906343175040266057809920 }, { target := 132, numerator := 9141949168019011183281438720 }, { target := 139, numerator := 55784158264313899338694656 }, { target := 144, numerator := 72829546460706333445668732928 }, { target := 146, numerator := 3291763005546243362323041353728 }, { target := 151, numerator := 73218259767487154930340331520 }, { target := 154, numerator := 131413637233588307553027096576 }, { target := 155, numerator := 26063902490579940800300109004800 }, { target := 160, numerator := 26063902490579940800300109004800 }, { target := 168, numerator := 131413637233588307553027096576 }, { target := 196, numerator := 9784017265065368176985899008 }, { target := 197, numerator := 1603411995076521673976929320960 }, { target := 199, numerator := 16507747312144300792443631042560 }, { target := 207, numerator := 1603411995076521673976929320960 }, { target := 214, numerator := 9784017265065368176985899008 }, { target := 250, numerator := 197535502773458415032205312 }, { target := 252, numerator := 7897432750361397894731268096 }, { target := 255, numerator := 7897430820370799182869430272 }, { target := 262, numerator := 197535502773458415032205312 }, { target := 466, numerator := 4785456857511847409328586752 }, { target := 468, numerator := 191321677274884187707844591616 }, { target := 471, numerator := 191321630519305489881772326912 }, { target := 478, numerator := 4785456857511847409328586752 }, { target := 482, numerator := 1860956229312916448580993024 }, { target := 484, numerator := 84111836037564127362284519424 }, { target := 489, numerator := 1870888715300054598061916160 }, { target := 492, numerator := 12356261133628230841959186432 }, { target := 493, numerator := 2450677053878201873159788953600 }, { target := 498, numerator := 2450677053878201873159788953600 }, { target := 506, numerator := 12356261133628230841959186432 }, { target := 508, numerator := 9784018438061105172883439616 }, { target := 509, numerator := 1603412187307931729678743633920 }, { target := 511, numerator := 16507749291241097124740459397120 }, { target := 519, numerator := 1603412187307931729678743633920 }, { target := 526, numerator := 9784018438061105172883439616 }, { target := 562, numerator := 3625732292841865746881445888 }, { target := 564, numerator := 144956104353407593616196501504 }, { target := 567, numerator := 144956068928741443066216316928 }, { target := 574, numerator := 3625732292841865746881445888 }, { target := 597, numerator := 4039919637366859197755424768 }, { target := 599, numerator := 161515237539649234363213676544 }, { target := 602, numerator := 161515198068228602643200606208 }, { target := 609, numerator := 4039919637366859197755424768 }, { target := 890, numerator := 38358908958295641670287360 }, { target := 891, numerator := 7607908005444919102537728000 }, { target := 896, numerator := 7607908005444919102537728000 }, { target := 904, numerator := 38358908958295641670287360 }, { target := 906, numerator := 55782985268576903441154048 }, { target := 907, numerator := 9141756936608955481467125760 }, { target := 909, numerator := 94117927246378707969229455360 }, { target := 917, numerator := 9141756936608955481467125760 }, { target := 924, numerator := 55782985268576903441154048 }]

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
    Slot14.Left4.expected,
    Slot14.Left5.expected,
    Slot14.Left6.expected,
    Slot14.Left7.expected,
    Slot14.Left8.expected,
    Slot14.Left9.expected,
    Slot15.Left0.expected,
    Slot15.Left2.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 118842229604297057781380284416 }, { target := 1, numerator := 45235021709620958394054606848 }, { target := 2, numerator := 45103012891402220188624486400 }, { target := 3, numerator := 44794992315558497709287538688 }, { target := 4, numerator := 45103012891402220188624486400 }, { target := 10, numerator := 560260187551064226004992000 }, { target := 11, numerator := 13735411049638993927864320000 }, { target := 12, numerator := 10156975013022519194025984000 }, { target := 13, numerator := 11331714115952169990488064000 }, { target := 14, numerator := 560260187551064226004992000 }, { target := 15, numerator := 11313641206676329209004032000 }, { target := 16, numerator := 11512443208710577805328384000 }, { target := 17, numerator := 560260187551064226004992000 }, { target := 18, numerator := 13735411049638993927864320000 }, { target := 19, numerator := 560260187551064226004992000 }, { target := 50, numerator := 118842257938495954999251566592 }, { target := 51, numerator := 168036832957402867592310292480 }, { target := 52, numerator := 167546453094686711363928064000 }, { target := 53, numerator := 166402233415015680164369530880 }, { target := 54, numerator := 167546453094686711363928064000 }, { target := 55, numerator := 21925760057281038423529881600 }, { target := 56, numerator := 537534762694631909738151936000 }, { target := 57, numerator := 397492811361030438516896563200 }, { target := 58, numerator := 443466179223071325533975347200 }, { target := 59, numerator := 21925760057281038423529881600 }, { target := 60, numerator := 442758896640578388810635673600 }, { target := 61, numerator := 450539005048000692767372083200 }, { target := 62, numerator := 21925760057281038423529881600 }, { target := 63, numerator := 537534762694631909738151936000 }, { target := 64, numerator := 21925760057281038423529881600 }, { target := 140, numerator := 45225499786254642666008477696 }, { target := 141, numerator := 45093518755750008494804172800 }, { target := 142, numerator := 44785563017905862095327461376 }, { target := 143, numerator := 45093518755750008494804172800 }, { target := 733, numerator := 197535502773458415032205312 }, { target := 735, numerator := 7897432750361397894731268096 }, { target := 738, numerator := 7897430820370799182869430272 }, { target := 745, numerator := 197535502773458415032205312 }, { target := 829, numerator := 4039919637366859197755424768 }, { target := 831, numerator := 161515237539649234363213676544 }, { target := 834, numerator := 161515198068228602643200606208 }, { target := 841, numerator := 4039919637366859197755424768 }, { target := 864, numerator := 4033547524374166990818902016 }, { target := 866, numerator := 161260481644476286044028796928 }, { target := 869, numerator := 161260442235313415572785463296 }, { target := 876, numerator := 4033547524374166990818902016 }, { target := 925, numerator := 197535502773458415032205312 }, { target := 927, numerator := 7897432750361397894731268096 }, { target := 930, numerator := 7897430820370799182869430272 }, { target := 937, numerator := 197535502773458415032205312 }, { target := 960, numerator := 4785456857511847409328586752 }, { target := 962, numerator := 191321677274884187707844591616 }, { target := 965, numerator := 191321630519305489881772326912 }, { target := 972, numerator := 4785456857511847409328586752 }, { target := 986, numerator := 197535502773458415032205312 }, { target := 988, numerator := 7897432750361397894731268096 }, { target := 991, numerator := 7897430820370799182869430272 }, { target := 998, numerator := 197535502773458415032205312 }]

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
    Slot17.Left5.expected,
    Slot17.Left12.expected,
    Slot18.Left0.expected,
    Slot18.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 175135122229741411740155904 }, { target := 35, numerator := 130419771873211689593733120 }, { target := 36, numerator := 137872330265966643284803584 }, { target := 37, numerator := 178861401426118888585691136 }, { target := 38, numerator := 2395997523270717611679154176 }, { target := 39, numerator := 4333662705387005571357474816 }, { target := 40, numerator := 130419771873211689593733120 }, { target := 41, numerator := 2395997523270717611679154176 }, { target := 42, numerator := 141598609462344120130338816 }, { target := 43, numerator := 141598609462344120130338816 }, { target := 44, numerator := 137872330265966643284803584 }, { target := 45, numerator := 137872330265966643284803584 }, { target := 46, numerator := 4333662705387005571357474816 }, { target := 47, numerator := 137872330265966643284803584 }, { target := 48, numerator := 175135122229741411740155904 }, { target := 49, numerator := 178861401426118888585691136 }, { target := 79, numerator := 20699847039183142753564360704 }, { target := 80, numerator := 15414779710029999922867077120 }, { target := 81, numerator := 16295624264888857061316624384 }, { target := 82, numerator := 21140269316612571322789134336 }, { target := 83, numerator := 283191524387122570011529445376 }, { target := 84, numerator := 512211108650425426008411734016 }, { target := 85, numerator := 15414779710029999922867077120 }, { target := 86, numerator := 283191524387122570011529445376 }, { target := 87, numerator := 16736046542318285630541398016 }, { target := 88, numerator := 16736046542318285630541398016 }, { target := 89, numerator := 16295624264888857061316624384 }, { target := 90, numerator := 16295624264888857061316624384 }, { target := 91, numerator := 512211108650425426008411734016 }, { target := 92, numerator := 16295624264888857061316624384 }, { target := 93, numerator := 20699847039183142753564360704 }, { target := 94, numerator := 21140269316612571322789134336 }, { target := 144, numerator := 21925760057281038423529881600 }, { target := 145, numerator := 537534762694631909738151936000 }, { target := 146, numerator := 397492811361030438516896563200 }, { target := 147, numerator := 443466179223071325533975347200 }, { target := 148, numerator := 21925760057281038423529881600 }, { target := 149, numerator := 442758896640578388810635673600 }, { target := 150, numerator := 450539005048000692767372083200 }, { target := 151, numerator := 21925760057281038423529881600 }, { target := 152, numerator := 537534762694631909738151936000 }, { target := 153, numerator := 21925760057281038423529881600 }, { target := 482, numerator := 560260187551064226004992000 }, { target := 483, numerator := 13735411049638993927864320000 }, { target := 484, numerator := 10156975013022519194025984000 }, { target := 485, numerator := 11331714115952169990488064000 }, { target := 486, numerator := 560260187551064226004992000 }, { target := 487, numerator := 11313641206676329209004032000 }, { target := 488, numerator := 11512443208710577805328384000 }, { target := 489, numerator := 560260187551064226004992000 }, { target := 490, numerator := 13735411049638993927864320000 }, { target := 491, numerator := 560260187551064226004992000 }]

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
    Slot18.Left3.expected,
    Slot18.Left11.expected,
    Slot18.Left18.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 154, numerator := 196437422163851522457986924544 }, { target := 155, numerator := 146283186717761772043181752320 }, { target := 156, numerator := 154642225958776730445649281024 }, { target := 157, numerator := 200616941784359001659220688896 }, { target := 158, numerator := 2687431115986309126393310478336 }, { target := 159, numerator := 4860781318650198311034867941376 }, { target := 160, numerator := 146283186717761772043181752320 }, { target := 161, numerator := 2687431115986309126393310478336 }, { target := 162, numerator := 158821745579284209646883045376 }, { target := 163, numerator := 158821745579284209646883045376 }, { target := 164, numerator := 154642225958776730445649281024 }, { target := 165, numerator := 154642225958776730445649281024 }, { target := 166, numerator := 4860781318650198311034867941376 }, { target := 167, numerator := 154642225958776730445649281024 }, { target := 168, numerator := 196437422163851522457986924544 }, { target := 169, numerator := 200616941784359001659220688896 }, { target := 492, numerator := 20699861236258550482278023168 }, { target := 493, numerator := 15414790282320197167653847040 }, { target := 494, numerator := 16295635441309922720091209728 }, { target := 495, numerator := 21140283815753413258496704512 }, { target := 496, numerator := 283191718615196765108612104192 }, { target := 497, numerator := 512211459952525408742326403072 }, { target := 498, numerator := 15414790282320197167653847040 }, { target := 499, numerator := 283191718615196765108612104192 }, { target := 500, numerator := 16736058020804785496309891072 }, { target := 501, numerator := 16736058020804785496309891072 }, { target := 502, numerator := 16295635441309922720091209728 }, { target := 503, numerator := 16295635441309922720091209728 }, { target := 504, numerator := 512211459952525408742326403072 }, { target := 505, numerator := 16295635441309922720091209728 }, { target := 506, numerator := 20699861236258550482278023168 }, { target := 507, numerator := 21140283815753413258496704512 }, { target := 890, numerator := 175135122229741411740155904 }, { target := 891, numerator := 130419771873211689593733120 }, { target := 892, numerator := 137872330265966643284803584 }, { target := 893, numerator := 178861401426118888585691136 }, { target := 894, numerator := 2395997523270717611679154176 }, { target := 895, numerator := 4333662705387005571357474816 }, { target := 896, numerator := 130419771873211689593733120 }, { target := 897, numerator := 2395997523270717611679154176 }, { target := 898, numerator := 141598609462344120130338816 }, { target := 899, numerator := 141598609462344120130338816 }, { target := 900, numerator := 137872330265966643284803584 }, { target := 901, numerator := 137872330265966643284803584 }, { target := 902, numerator := 4333662705387005571357474816 }, { target := 903, numerator := 137872330265966643284803584 }, { target := 904, numerator := 175135122229741411740155904 }, { target := 905, numerator := 178861401426118888585691136 }]

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

namespace RouteChunk13

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot19.Left0.expected,
    Slot19.Left1.expected,
    Slot19.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 121, numerator := 74802285088655180184944640 }, { target := 122, numerator := 1084633133785500112681697280 }, { target := 123, numerator := 1919925317275482958080245760 }, { target := 124, numerator := 62335237573879316820787200 }, { target := 125, numerator := 1196836561418482882959114240 }, { target := 126, numerator := 62335237573879316820787200 }, { target := 127, numerator := 1907458269760707094716088320 }, { target := 128, numerator := 1994727602364138138265190400 }, { target := 129, numerator := 1196836561418482882959114240 }, { target := 130, numerator := 30556733458715641105549885440 }, { target := 131, numerator := 1957326459819810548172718080 }, { target := 132, numerator := 1084633133785500112681697280 }, { target := 133, numerator := 1907458269760707094716088320 }, { target := 134, numerator := 62335237573879316820787200 }, { target := 135, numerator := 1957326459819810548172718080 }, { target := 136, numerator := 62335237573879316820787200 }, { target := 137, numerator := 1907458269760707094716088320 }, { target := 138, numerator := 1994727602364138138265190400 }, { target := 139, numerator := 74802285088655180184944640 }, { target := 196, numerator := 56101713816491385138708480 }, { target := 197, numerator := 813474850339125084511272960 }, { target := 198, numerator := 1439943987956612218560184320 }, { target := 199, numerator := 46751428180409487615590400 }, { target := 200, numerator := 897627421063862162219335680 }, { target := 201, numerator := 46751428180409487615590400 }, { target := 202, numerator := 1430593702320530321037066240 }, { target := 203, numerator := 1496045701773103603698892800 }, { target := 204, numerator := 897627421063862162219335680 }, { target := 205, numerator := 22917550094036730829162414080 }, { target := 206, numerator := 1467994844864857911129538560 }, { target := 207, numerator := 813474850339125084511272960 }, { target := 208, numerator := 1430593702320530321037066240 }, { target := 209, numerator := 46751428180409487615590400 }, { target := 210, numerator := 1467994844864857911129538560 }, { target := 211, numerator := 46751428180409487615590400 }, { target := 212, numerator := 1430593702320530321037066240 }, { target := 213, numerator := 1496045701773103603698892800 }, { target := 214, numerator := 56101713816491385138708480 }, { target := 231, numerator := 59218475695185350979747840 }, { target := 232, numerator := 858667897580187589206343680 }, { target := 233, numerator := 1519940876176424008480194560 }, { target := 234, numerator := 49348729745987792483123200 }, { target := 235, numerator := 947495611122965615675965440 }, { target := 236, numerator := 49348729745987792483123200 }, { target := 237, numerator := 1510071130227226449983569920 }, { target := 238, numerator := 1579159351871609359459942400 }, { target := 239, numerator := 947495611122965615675965440 }, { target := 240, numerator := 24190747321483215875226992640 }, { target := 241, numerator := 1549550114024016683970068480 }, { target := 242, numerator := 858667897580187589206343680 }, { target := 243, numerator := 1510071130227226449983569920 }, { target := 244, numerator := 49348729745987792483123200 }, { target := 245, numerator := 1549550114024016683970068480 }, { target := 246, numerator := 49348729745987792483123200 }, { target := 247, numerator := 1510071130227226449983569920 }, { target := 248, numerator := 1579159351871609359459942400 }, { target := 249, numerator := 59218475695185350979747840 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk13

namespace RouteChunk14

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot19.Left3.expected,
    Slot19.Left4.expected,
    Slot19.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 337, numerator := 76360666028002163105464320 }, { target := 338, numerator := 1107229657406031365029232640 }, { target := 339, numerator := 1959923761385388853040250880 }, { target := 340, numerator := 63633888356668469254553600 }, { target := 341, numerator := 1221770656448034609687429120 }, { target := 342, numerator := 63633888356668469254553600 }, { target := 343, numerator := 1947196983714055159189340160 }, { target := 344, numerator := 2036284427413391016145715200 }, { target := 345, numerator := 1221770656448034609687429120 }, { target := 346, numerator := 31193332072438883628582174720 }, { target := 347, numerator := 1998104094399389934592983040 }, { target := 348, numerator := 1107229657406031365029232640 }, { target := 349, numerator := 1947196983714055159189340160 }, { target := 350, numerator := 63633888356668469254553600 }, { target := 351, numerator := 1998104094399389934592983040 }, { target := 352, numerator := 63633888356668469254553600 }, { target := 353, numerator := 1947196983714055159189340160 }, { target := 354, numerator := 2036284427413391016145715200 }, { target := 355, numerator := 76360666028002163105464320 }, { target := 412, numerator := 1022297896211620795860910080 }, { target := 413, numerator := 14823319495068501539983196160 }, { target := 414, numerator := 26238979336098267093763358720 }, { target := 415, numerator := 851914913509683996550758400 }, { target := 416, numerator := 16356766339385932733774561280 }, { target := 417, numerator := 851914913509683996550758400 }, { target := 418, numerator := 26068596353396330294453207040 }, { target := 419, numerator := 27261277232309887889624268800 }, { target := 420, numerator := 16356766339385932733774561280 }, { target := 421, numerator := 417608690602447095109181767680 }, { target := 422, numerator := 26750128284204077491693813760 }, { target := 423, numerator := 14823319495068501539983196160 }, { target := 424, numerator := 26068596353396330294453207040 }, { target := 425, numerator := 851914913509683996550758400 }, { target := 426, numerator := 26750128284204077491693813760 }, { target := 427, numerator := 851914913509683996550758400 }, { target := 428, numerator := 26068596353396330294453207040 }, { target := 429, numerator := 27261277232309887889624268800 }, { target := 430, numerator := 1022297896211620795860910080 }, { target := 447, numerator := 1787462937430989409836072960 }, { target := 448, numerator := 25918212592749346442623057920 }, { target := 449, numerator := 45878215394062061519125872640 }, { target := 450, numerator := 1489552447859157841530060800 }, { target := 451, numerator := 28599406998895830557377167360 }, { target := 452, numerator := 1489552447859157841530060800 }, { target := 453, numerator := 45580304904490229950819860480 }, { target := 454, numerator := 47665678331493050928961945600 }, { target := 455, numerator := 28599406998895830557377167360 }, { target := 456, numerator := 730178609940559173918035804160 }, { target := 457, numerator := 46771946862777556224043909120 }, { target := 458, numerator := 25918212592749346442623057920 }, { target := 459, numerator := 45580304904490229950819860480 }, { target := 460, numerator := 1489552447859157841530060800 }, { target := 461, numerator := 46771946862777556224043909120 }, { target := 462, numerator := 1489552447859157841530060800 }, { target := 463, numerator := 45580304904490229950819860480 }, { target := 464, numerator := 47665678331493050928961945600 }, { target := 465, numerator := 1787462937430989409836072960 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk14

namespace RouteChunk15

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot19.Left6.expected,
    Slot19.Left7.expected,
    Slot19.Left8.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 508, numerator := 54543332877144402218188800 }, { target := 509, numerator := 790878326718593832163737600 }, { target := 510, numerator := 1399945543846706323600179200 }, { target := 511, numerator := 45452777397620335181824000 }, { target := 512, numerator := 872693326034310435491020800 }, { target := 513, numerator := 45452777397620335181824000 }, { target := 514, numerator := 1390854988367182256563814400 }, { target := 515, numerator := 1454488876723850725818368000 }, { target := 516, numerator := 872693326034310435491020800 }, { target := 517, numerator := 22280951480313488306130124800 }, { target := 518, numerator := 1427217210285278524709273600 }, { target := 519, numerator := 790878326718593832163737600 }, { target := 520, numerator := 1390854988367182256563814400 }, { target := 521, numerator := 45452777397620335181824000 }, { target := 522, numerator := 1427217210285278524709273600 }, { target := 523, numerator := 45452777397620335181824000 }, { target := 524, numerator := 1390854988367182256563814400 }, { target := 525, numerator := 1454488876723850725818368000 }, { target := 526, numerator := 54543332877144402218188800 }, { target := 543, numerator := 1022297896211620795860910080 }, { target := 544, numerator := 14823319495068501539983196160 }, { target := 545, numerator := 26238979336098267093763358720 }, { target := 546, numerator := 851914913509683996550758400 }, { target := 547, numerator := 16356766339385932733774561280 }, { target := 548, numerator := 851914913509683996550758400 }, { target := 549, numerator := 26068596353396330294453207040 }, { target := 550, numerator := 27261277232309887889624268800 }, { target := 551, numerator := 16356766339385932733774561280 }, { target := 552, numerator := 417608690602447095109181767680 }, { target := 553, numerator := 26750128284204077491693813760 }, { target := 554, numerator := 14823319495068501539983196160 }, { target := 555, numerator := 26068596353396330294453207040 }, { target := 556, numerator := 851914913509683996550758400 }, { target := 557, numerator := 26750128284204077491693813760 }, { target := 558, numerator := 851914913509683996550758400 }, { target := 559, numerator := 26068596353396330294453207040 }, { target := 560, numerator := 27261277232309887889624268800 }, { target := 561, numerator := 1022297896211620795860910080 }, { target := 578, numerator := 57660094755838368059228160 }, { target := 579, numerator := 836071373959656336858808320 }, { target := 580, numerator := 1479942432066518113520189440 }, { target := 581, numerator := 48050078963198640049356800 }, { target := 582, numerator := 922561516093413888947650560 }, { target := 583, numerator := 48050078963198640049356800 }, { target := 584, numerator := 1470332416273878385510318080 }, { target := 585, numerator := 1537602526822356481579417600 }, { target := 586, numerator := 922561516093413888947650560 }, { target := 587, numerator := 23554148707759973352194703360 }, { target := 588, numerator := 1508772479444437297549803520 }, { target := 589, numerator := 836071373959656336858808320 }, { target := 590, numerator := 1470332416273878385510318080 }, { target := 591, numerator := 48050078963198640049356800 }, { target := 592, numerator := 1508772479444437297549803520 }, { target := 593, numerator := 48050078963198640049356800 }, { target := 594, numerator := 1470332416273878385510318080 }, { target := 595, numerator := 1537602526822356481579417600 }, { target := 596, numerator := 57660094755838368059228160 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk15

namespace RouteChunk16

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot19.Left9.expected,
    Slot19.Left10.expected,
    Slot19.Left11.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 679, numerator := 59218475695185350979747840 }, { target := 680, numerator := 858667897580187589206343680 }, { target := 681, numerator := 1519940876176424008480194560 }, { target := 682, numerator := 49348729745987792483123200 }, { target := 683, numerator := 947495611122965615675965440 }, { target := 684, numerator := 49348729745987792483123200 }, { target := 685, numerator := 1510071130227226449983569920 }, { target := 686, numerator := 1579159351871609359459942400 }, { target := 687, numerator := 947495611122965615675965440 }, { target := 688, numerator := 24190747321483215875226992640 }, { target := 689, numerator := 1549550114024016683970068480 }, { target := 690, numerator := 858667897580187589206343680 }, { target := 691, numerator := 1510071130227226449983569920 }, { target := 692, numerator := 49348729745987792483123200 }, { target := 693, numerator := 1549550114024016683970068480 }, { target := 694, numerator := 49348729745987792483123200 }, { target := 695, numerator := 1510071130227226449983569920 }, { target := 696, numerator := 1579159351871609359459942400 }, { target := 697, numerator := 59218475695185350979747840 }, { target := 714, numerator := 59218475695185350979747840 }, { target := 715, numerator := 858667897580187589206343680 }, { target := 716, numerator := 1519940876176424008480194560 }, { target := 717, numerator := 49348729745987792483123200 }, { target := 718, numerator := 947495611122965615675965440 }, { target := 719, numerator := 49348729745987792483123200 }, { target := 720, numerator := 1510071130227226449983569920 }, { target := 721, numerator := 1579159351871609359459942400 }, { target := 722, numerator := 947495611122965615675965440 }, { target := 723, numerator := 24190747321483215875226992640 }, { target := 724, numerator := 1549550114024016683970068480 }, { target := 725, numerator := 858667897580187589206343680 }, { target := 726, numerator := 1510071130227226449983569920 }, { target := 727, numerator := 49348729745987792483123200 }, { target := 728, numerator := 1549550114024016683970068480 }, { target := 729, numerator := 49348729745987792483123200 }, { target := 730, numerator := 1510071130227226449983569920 }, { target := 731, numerator := 1579159351871609359459942400 }, { target := 732, numerator := 59218475695185350979747840 }, { target := 775, numerator := 57660094755838368059228160 }, { target := 776, numerator := 836071373959656336858808320 }, { target := 777, numerator := 1479942432066518113520189440 }, { target := 778, numerator := 48050078963198640049356800 }, { target := 779, numerator := 922561516093413888947650560 }, { target := 780, numerator := 48050078963198640049356800 }, { target := 781, numerator := 1470332416273878385510318080 }, { target := 782, numerator := 1537602526822356481579417600 }, { target := 783, numerator := 922561516093413888947650560 }, { target := 784, numerator := 23554148707759973352194703360 }, { target := 785, numerator := 1508772479444437297549803520 }, { target := 786, numerator := 836071373959656336858808320 }, { target := 787, numerator := 1470332416273878385510318080 }, { target := 788, numerator := 48050078963198640049356800 }, { target := 789, numerator := 1508772479444437297549803520 }, { target := 790, numerator := 48050078963198640049356800 }, { target := 791, numerator := 1470332416273878385510318080 }, { target := 792, numerator := 1537602526822356481579417600 }, { target := 793, numerator := 57660094755838368059228160 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk16

namespace RouteChunk17

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot19.Left12.expected,
    Slot19.Left13.expected,
    Slot19.Left14.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 810, numerator := 1787462937430989409836072960 }, { target := 811, numerator := 25918212592749346442623057920 }, { target := 812, numerator := 45878215394062061519125872640 }, { target := 813, numerator := 1489552447859157841530060800 }, { target := 814, numerator := 28599406998895830557377167360 }, { target := 815, numerator := 1489552447859157841530060800 }, { target := 816, numerator := 45580304904490229950819860480 }, { target := 817, numerator := 47665678331493050928961945600 }, { target := 818, numerator := 28599406998895830557377167360 }, { target := 819, numerator := 730178609940559173918035804160 }, { target := 820, numerator := 46771946862777556224043909120 }, { target := 821, numerator := 25918212592749346442623057920 }, { target := 822, numerator := 45580304904490229950819860480 }, { target := 823, numerator := 1489552447859157841530060800 }, { target := 824, numerator := 46771946862777556224043909120 }, { target := 825, numerator := 1489552447859157841530060800 }, { target := 826, numerator := 45580304904490229950819860480 }, { target := 827, numerator := 47665678331493050928961945600 }, { target := 828, numerator := 1787462937430989409836072960 }, { target := 845, numerator := 57660094755838368059228160 }, { target := 846, numerator := 836071373959656336858808320 }, { target := 847, numerator := 1479942432066518113520189440 }, { target := 848, numerator := 48050078963198640049356800 }, { target := 849, numerator := 922561516093413888947650560 }, { target := 850, numerator := 48050078963198640049356800 }, { target := 851, numerator := 1470332416273878385510318080 }, { target := 852, numerator := 1537602526822356481579417600 }, { target := 853, numerator := 922561516093413888947650560 }, { target := 854, numerator := 23554148707759973352194703360 }, { target := 855, numerator := 1508772479444437297549803520 }, { target := 856, numerator := 836071373959656336858808320 }, { target := 857, numerator := 1470332416273878385510318080 }, { target := 858, numerator := 48050078963198640049356800 }, { target := 859, numerator := 1508772479444437297549803520 }, { target := 860, numerator := 48050078963198640049356800 }, { target := 861, numerator := 1470332416273878385510318080 }, { target := 862, numerator := 1537602526822356481579417600 }, { target := 863, numerator := 57660094755838368059228160 }, { target := 906, numerator := 74802285088655180184944640 }, { target := 907, numerator := 1084633133785500112681697280 }, { target := 908, numerator := 1919925317275482958080245760 }, { target := 909, numerator := 62335237573879316820787200 }, { target := 910, numerator := 1196836561418482882959114240 }, { target := 911, numerator := 62335237573879316820787200 }, { target := 912, numerator := 1907458269760707094716088320 }, { target := 913, numerator := 1994727602364138138265190400 }, { target := 914, numerator := 1196836561418482882959114240 }, { target := 915, numerator := 30556733458715641105549885440 }, { target := 916, numerator := 1957326459819810548172718080 }, { target := 917, numerator := 1084633133785500112681697280 }, { target := 918, numerator := 1907458269760707094716088320 }, { target := 919, numerator := 62335237573879316820787200 }, { target := 920, numerator := 1957326459819810548172718080 }, { target := 921, numerator := 62335237573879316820787200 }, { target := 922, numerator := 1907458269760707094716088320 }, { target := 923, numerator := 1994727602364138138265190400 }, { target := 924, numerator := 74802285088655180184944640 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk17

namespace RouteChunk18

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot19.Left15.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 941, numerator := 76360666028002163105464320 }, { target := 942, numerator := 1107229657406031365029232640 }, { target := 943, numerator := 1959923761385388853040250880 }, { target := 944, numerator := 63633888356668469254553600 }, { target := 945, numerator := 1221770656448034609687429120 }, { target := 946, numerator := 63633888356668469254553600 }, { target := 947, numerator := 1947196983714055159189340160 }, { target := 948, numerator := 2036284427413391016145715200 }, { target := 949, numerator := 1221770656448034609687429120 }, { target := 950, numerator := 31193332072438883628582174720 }, { target := 951, numerator := 1998104094399389934592983040 }, { target := 952, numerator := 1107229657406031365029232640 }, { target := 953, numerator := 1947196983714055159189340160 }, { target := 954, numerator := 63633888356668469254553600 }, { target := 955, numerator := 1998104094399389934592983040 }, { target := 956, numerator := 63633888356668469254553600 }, { target := 957, numerator := 1947196983714055159189340160 }, { target := 958, numerator := 2036284427413391016145715200 }, { target := 959, numerator := 76360666028002163105464320 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk18

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent1
