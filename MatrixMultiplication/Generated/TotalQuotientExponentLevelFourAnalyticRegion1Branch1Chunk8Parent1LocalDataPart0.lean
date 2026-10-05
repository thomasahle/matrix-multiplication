import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk8Parent1LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 1,
parent 35; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 57, #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416], #[3298534883328, 2473901162496, 2611340115968, 3367254360064, 45079976738816, 78821239816192, 2405181685760, 45079976738816, 2542620639232, 2611340115968, 2611340115968, 2542620639232, 78821239816192, 2542620639232, 3298534883328, 3367254360064, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 34, numerator := 77522368182788095828033536 }, some { target := 35, numerator := 58141776137091071871025152 }, some { target := 36, numerator := 61371874811373909197193216 }, some { target := 37, numerator := 79137417519929514491117568 }, some { target := 38, numerator := 1059472365164770642983124992 }, some { target := 39, numerator := 1852461589701207206557384704 }, some { target := 40, numerator := 56526726799949653207941120 }, some { target := 41, numerator := 1059472365164770642983124992 }, some { target := 42, numerator := 59756825474232490534109184 }, some { target := 43, numerator := 61371874811373909197193216 }, some { target := 44, numerator := 61371874811373909197193216 }, some { target := 45, numerator := 59756825474232490534109184 }, some { target := 46, numerator := 1852461589701207206557384704 }, some { target := 47, numerator := 59756825474232490534109184 }, some { target := 48, numerator := 77522368182788095828033536 }, some { target := 49, numerator := 79137417519929514491117568 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 79, numerator := 1124074338650427389506486272 }, some { target := 80, numerator := 843055753987820542129864704 }, some { target := 81, numerator := 889892184764921683359301632 }, some { target := 82, numerator := 1147492554038977960121204736 }, some { target := 83, numerator := 15362349294889174323255312384 }, some { target := 84, numerator := 26860693050667504495082078208 }, some { target := 85, numerator := 819637538599269971515146240 }, some { target := 86, numerator := 15362349294889174323255312384 }, some { target := 87, numerator := 866473969376371112744583168 }, some { target := 88, numerator := 889892184764921683359301632 }, some { target := 89, numerator := 889892184764921683359301632 }, some { target := 90, numerator := 866473969376371112744583168 }, some { target := 91, numerator := 26860693050667504495082078208 }, some { target := 92, numerator := 866473969376371112744583168 }, some { target := 93, numerator := 1124074338650427389506486272 }, some { target := 94, numerator := 1147492554038977960121204736 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 105, numerator := 1989740783358227792919527424 }, some { target := 106, numerator := 1492305587518670844689645568 }, some { target := 107, numerator := 1575211453491930336061292544 }, some { target := 108, numerator := 2031193716344857538605350912 }, some { target := 109, numerator := 27193124039229113169900208128 }, some { target := 110, numerator := 47546514135664318301639540736 }, some { target := 111, numerator := 1450852654532041099003822080 }, some { target := 112, numerator := 27193124039229113169900208128 }, some { target := 113, numerator := 1533758520505300590375469056 }, some { target := 114, numerator := 1575211453491930336061292544 }, some { target := 115, numerator := 1575211453491930336061292544 }, some { target := 116, numerator := 1533758520505300590375469056 }, some { target := 117, numerator := 47546514135664318301639540736 }, some { target := 118, numerator := 1533758520505300590375469056 }, some { target := 119, numerator := 1989740783358227792919527424 }, some { target := 120, numerator := 2031193716344857538605350912 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 154, numerator := 64601973485656746523361280 }, some { target := 155, numerator := 48451480114242559892520960 }, some { target := 156, numerator := 51143229009478257664327680 }, some { target := 157, numerator := 65947847933274595409264640 }, some { target := 158, numerator := 882893637637308869152604160 }, some { target := 159, numerator := 1543717991417672672131153920 }, some { target := 160, numerator := 47105605666624711006617600 }, some { target := 161, numerator := 882893637637308869152604160 }, some { target := 162, numerator := 49797354561860408778424320 }, some { target := 163, numerator := 51143229009478257664327680 }, some { target := 164, numerator := 51143229009478257664327680 }, some { target := 165, numerator := 49797354561860408778424320 }, some { target := 166, numerator := 1543717991417672672131153920 }, some { target := 167, numerator := 49797354561860408778424320 }, some { target := 168, numerator := 64601973485656746523361280 }, some { target := 169, numerator := 65947847933274595409264640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 180, numerator := 1240357890924609533248536576 }, some { target := 181, numerator := 930268418193457149936402432 }, some { target := 182, numerator := 981949996981982547155091456 }, some { target := 183, numerator := 1266198680318872231857881088 }, some { target := 184, numerator := 16951557842636330287729999872 }, some { target := 185, numerator := 29639385435219315304918155264 }, some { target := 186, numerator := 904427628799194451327057920 }, some { target := 187, numerator := 16951557842636330287729999872 }, some { target := 188, numerator := 956109207587719848545746944 }, some { target := 189, numerator := 981949996981982547155091456 }, some { target := 190, numerator := 981949996981982547155091456 }, some { target := 191, numerator := 956109207587719848545746944 }, some { target := 192, numerator := 29639385435219315304918155264 }, some { target := 193, numerator := 956109207587719848545746944 }, some { target := 194, numerator := 1240357890924609533248536576 }, some { target := 195, numerator := 1266198680318872231857881088 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 215, numerator := 64601973485656746523361280 }, some { target := 216, numerator := 48451480114242559892520960 }, some { target := 217, numerator := 51143229009478257664327680 }, some { target := 218, numerator := 65947847933274595409264640 }, some { target := 219, numerator := 882893637637308869152604160 }, some { target := 220, numerator := 1543717991417672672131153920 }, some { target := 221, numerator := 47105605666624711006617600 }, some { target := 222, numerator := 882893637637308869152604160 }, some { target := 223, numerator := 49797354561860408778424320 }, some { target := 224, numerator := 51143229009478257664327680 }, some { target := 225, numerator := 51143229009478257664327680 }, some { target := 226, numerator := 49797354561860408778424320 }, some { target := 227, numerator := 1543717991417672672131153920 }, some { target := 228, numerator := 49797354561860408778424320 }, some { target := 229, numerator := 64601973485656746523361280 }, some { target := 230, numerator := 65947847933274595409264640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 295, numerator := 1976820388661096443614855168 }, some { target := 296, numerator := 1482615291495822332711141376 }, some { target := 297, numerator := 1564982807690034684528427008 }, some { target := 298, numerator := 2018004146758202619523497984 }, some { target := 299, numerator := 27016545311701651396069687296 }, some { target := 300, numerator := 47237770537380783767213309952 }, some { target := 301, numerator := 1441431533398716156802498560 }, some { target := 302, numerator := 27016545311701651396069687296 }, some { target := 303, numerator := 1523799049592928508619784192 }, some { target := 304, numerator := 1564982807690034684528427008 }, some { target := 305, numerator := 1564982807690034684528427008 }, some { target := 306, numerator := 1523799049592928508619784192 }, some { target := 307, numerator := 47237770537380783767213309952 }, some { target := 308, numerator := 1523799049592928508619784192 }, some { target := 309, numerator := 1976820388661096443614855168 }, some { target := 310, numerator := 2018004146758202619523497984 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 321, numerator := 2067263151541015888747560960 }, some { target := 322, numerator := 1550447363655761916560670720 }, some { target := 323, numerator := 1636583328303304245258485760 }, some { target := 324, numerator := 2110331133864787053096468480 }, some { target := 325, numerator := 28252596404393883812883333120 }, some { target := 326, numerator := 49398975725365525508196925440 }, some { target := 327, numerator := 1507379381331990752211763200 }, some { target := 328, numerator := 28252596404393883812883333120 }, some { target := 329, numerator := 1593515345979533080909578240 }, some { target := 330, numerator := 1636583328303304245258485760 }, some { target := 331, numerator := 1636583328303304245258485760 }, some { target := 332, numerator := 1593515345979533080909578240 }, some { target := 333, numerator := 49398975725365525508196925440 }, some { target := 334, numerator := 1593515345979533080909578240 }, some { target := 335, numerator := 2067263151541015888747560960 }, some { target := 336, numerator := 2110331133864787053096468480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 370, numerator := 1240357890924609533248536576 }, some { target := 371, numerator := 930268418193457149936402432 }, some { target := 372, numerator := 981949996981982547155091456 }, some { target := 373, numerator := 1266198680318872231857881088 }, some { target := 374, numerator := 16951557842636330287729999872 }, some { target := 375, numerator := 29639385435219315304918155264 }, some { target := 376, numerator := 904427628799194451327057920 }, some { target := 377, numerator := 16951557842636330287729999872 }, some { target := 378, numerator := 956109207587719848545746944 }, some { target := 379, numerator := 981949996981982547155091456 }, some { target := 380, numerator := 981949996981982547155091456 }, some { target := 381, numerator := 956109207587719848545746944 }, some { target := 382, numerator := 29639385435219315304918155264 }, some { target := 383, numerator := 956109207587719848545746944 }, some { target := 384, numerator := 1240357890924609533248536576 }, some { target := 385, numerator := 1266198680318872231857881088 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 396, numerator := 31667887402668937145751699456 }, some { target := 397, numerator := 23750915552001702859313774592 }, some { target := 398, numerator := 25070410860446241907053428736 }, some { target := 399, numerator := 32327635056891206669621526528 }, some { target := 400, numerator := 432794461169808807658606559232 }, some { target := 401, numerator := 756730559392943143878691651584 }, some { target := 402, numerator := 23091167897779433335443947520 }, some { target := 403, numerator := 432794461169808807658606559232 }, some { target := 404, numerator := 24410663206223972383183601664 }, some { target := 405, numerator := 25070410860446241907053428736 }, some { target := 406, numerator := 25070410860446241907053428736 }, some { target := 407, numerator := 24410663206223972383183601664 }, some { target := 408, numerator := 756730559392943143878691651584 }, some { target := 409, numerator := 24410663206223972383183601664 }, some { target := 410, numerator := 31667887402668937145751699456 }, some { target := 411, numerator := 32327635056891206669621526528 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 431, numerator := 2028501967449621840833544192 }, some { target := 432, numerator := 1521376475587216380625158144 }, some { target := 433, numerator := 1605897390897617290659889152 }, some { target := 434, numerator := 2070762425104822295850909696 }, some { target := 435, numerator := 27722860221811498491391770624 }, some { target := 436, numerator := 48472744930514921904918233088 }, some { target := 437, numerator := 1479116017932015925607792640 }, some { target := 438, numerator := 27722860221811498491391770624 }, some { target := 439, numerator := 1563636933242416835642523648 }, some { target := 440, numerator := 1605897390897617290659889152 }, some { target := 441, numerator := 1605897390897617290659889152 }, some { target := 442, numerator := 1563636933242416835642523648 }, some { target := 443, numerator := 48472744930514921904918233088 }, some { target := 444, numerator := 1563636933242416835642523648 }, some { target := 445, numerator := 2028501967449621840833544192 }, some { target := 446, numerator := 2070762425104822295850909696 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 492, numerator := 1124074338650427389506486272 }, some { target := 493, numerator := 843055753987820542129864704 }, some { target := 494, numerator := 889892184764921683359301632 }, some { target := 495, numerator := 1147492554038977960121204736 }, some { target := 496, numerator := 15362349294889174323255312384 }, some { target := 497, numerator := 26860693050667504495082078208 }, some { target := 498, numerator := 819637538599269971515146240 }, some { target := 499, numerator := 15362349294889174323255312384 }, some { target := 500, numerator := 866473969376371112744583168 }, some { target := 501, numerator := 889892184764921683359301632 }, some { target := 502, numerator := 889892184764921683359301632 }, some { target := 503, numerator := 866473969376371112744583168 }, some { target := 504, numerator := 26860693050667504495082078208 }, some { target := 505, numerator := 866473969376371112744583168 }, some { target := 506, numerator := 1124074338650427389506486272 }, some { target := 507, numerator := 1147492554038977960121204736 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 527, numerator := 1976820388661096443614855168 }, some { target := 528, numerator := 1482615291495822332711141376 }, some { target := 529, numerator := 1564982807690034684528427008 }, some { target := 530, numerator := 2018004146758202619523497984 }, some { target := 531, numerator := 27016545311701651396069687296 }, some { target := 532, numerator := 47237770537380783767213309952 }, some { target := 533, numerator := 1441431533398716156802498560 }, some { target := 534, numerator := 27016545311701651396069687296 }, some { target := 535, numerator := 1523799049592928508619784192 }, some { target := 536, numerator := 1564982807690034684528427008 }, some { target := 537, numerator := 1564982807690034684528427008 }, some { target := 538, numerator := 1523799049592928508619784192 }, some { target := 539, numerator := 47237770537380783767213309952 }, some { target := 540, numerator := 1523799049592928508619784192 }, some { target := 541, numerator := 1976820388661096443614855168 }, some { target := 542, numerator := 2018004146758202619523497984 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 637, numerator := 64601973485656746523361280 }, some { target := 638, numerator := 48451480114242559892520960 }, some { target := 639, numerator := 51143229009478257664327680 }, some { target := 640, numerator := 65947847933274595409264640 }, some { target := 641, numerator := 882893637637308869152604160 }, some { target := 642, numerator := 1543717991417672672131153920 }, some { target := 643, numerator := 47105605666624711006617600 }, some { target := 644, numerator := 882893637637308869152604160 }, some { target := 645, numerator := 49797354561860408778424320 }, some { target := 646, numerator := 51143229009478257664327680 }, some { target := 647, numerator := 51143229009478257664327680 }, some { target := 648, numerator := 49797354561860408778424320 }, some { target := 649, numerator := 1543717991417672672131153920 }, some { target := 650, numerator := 49797354561860408778424320 }, some { target := 651, numerator := 64601973485656746523361280 }, some { target := 652, numerator := 65947847933274595409264640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 663, numerator := 2028501967449621840833544192 }, some { target := 664, numerator := 1521376475587216380625158144 }, some { target := 665, numerator := 1605897390897617290659889152 }, some { target := 666, numerator := 2070762425104822295850909696 }, some { target := 667, numerator := 27722860221811498491391770624 }, some { target := 668, numerator := 48472744930514921904918233088 }, some { target := 669, numerator := 1479116017932015925607792640 }, some { target := 670, numerator := 27722860221811498491391770624 }, some { target := 671, numerator := 1563636933242416835642523648 }, some { target := 672, numerator := 1605897390897617290659889152 }, some { target := 673, numerator := 1605897390897617290659889152 }, some { target := 674, numerator := 1563636933242416835642523648 }, some { target := 675, numerator := 48472744930514921904918233088 }, some { target := 676, numerator := 1563636933242416835642523648 }, some { target := 677, numerator := 2028501967449621840833544192 }, some { target := 678, numerator := 2070762425104822295850909696 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 698, numerator := 64601973485656746523361280 }, some { target := 699, numerator := 48451480114242559892520960 }, some { target := 700, numerator := 51143229009478257664327680 }, some { target := 701, numerator := 65947847933274595409264640 }, some { target := 702, numerator := 882893637637308869152604160 }, some { target := 703, numerator := 1543717991417672672131153920 }, some { target := 704, numerator := 47105605666624711006617600 }, some { target := 705, numerator := 882893637637308869152604160 }, some { target := 706, numerator := 49797354561860408778424320 }, some { target := 707, numerator := 51143229009478257664327680 }, some { target := 708, numerator := 51143229009478257664327680 }, some { target := 709, numerator := 49797354561860408778424320 }, some { target := 710, numerator := 1543717991417672672131153920 }, some { target := 711, numerator := 49797354561860408778424320 }, some { target := 712, numerator := 64601973485656746523361280 }, some { target := 713, numerator := 65947847933274595409264640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 759, numerator := 1976820388661096443614855168 }, some { target := 760, numerator := 1482615291495822332711141376 }, some { target := 761, numerator := 1564982807690034684528427008 }, some { target := 762, numerator := 2018004146758202619523497984 }, some { target := 763, numerator := 27016545311701651396069687296 }, some { target := 764, numerator := 47237770537380783767213309952 }, some { target := 765, numerator := 1441431533398716156802498560 }, some { target := 766, numerator := 27016545311701651396069687296 }, some { target := 767, numerator := 1523799049592928508619784192 }, some { target := 768, numerator := 1564982807690034684528427008 }, some { target := 769, numerator := 1564982807690034684528427008 }, some { target := 770, numerator := 1523799049592928508619784192 }, some { target := 771, numerator := 47237770537380783767213309952 }, some { target := 772, numerator := 1523799049592928508619784192 }, some { target := 773, numerator := 1976820388661096443614855168 }, some { target := 774, numerator := 2018004146758202619523497984 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 794, numerator := 2067263151541015888747560960 }, some { target := 795, numerator := 1550447363655761916560670720 }, some { target := 796, numerator := 1636583328303304245258485760 }, some { target := 797, numerator := 2110331133864787053096468480 }, some { target := 798, numerator := 28252596404393883812883333120 }, some { target := 799, numerator := 49398975725365525508196925440 }, some { target := 800, numerator := 1507379381331990752211763200 }, some { target := 801, numerator := 28252596404393883812883333120 }, some { target := 802, numerator := 1593515345979533080909578240 }, some { target := 803, numerator := 1636583328303304245258485760 }, some { target := 804, numerator := 1636583328303304245258485760 }, some { target := 805, numerator := 1593515345979533080909578240 }, some { target := 806, numerator := 49398975725365525508196925440 }, some { target := 807, numerator := 1593515345979533080909578240 }, some { target := 808, numerator := 2067263151541015888747560960 }, some { target := 809, numerator := 2110331133864787053096468480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 890, numerator := 77522368182788095828033536 }, some { target := 891, numerator := 58141776137091071871025152 }, some { target := 892, numerator := 61371874811373909197193216 }, some { target := 893, numerator := 79137417519929514491117568 }, some { target := 894, numerator := 1059472365164770642983124992 }, some { target := 895, numerator := 1852461589701207206557384704 }, some { target := 896, numerator := 56526726799949653207941120 }, some { target := 897, numerator := 1059472365164770642983124992 }, some { target := 898, numerator := 59756825474232490534109184 }, some { target := 899, numerator := 61371874811373909197193216 }, some { target := 900, numerator := 61371874811373909197193216 }, some { target := 901, numerator := 59756825474232490534109184 }, some { target := 902, numerator := 1852461589701207206557384704 }, some { target := 903, numerator := 59756825474232490534109184 }, some { target := 904, numerator := 77522368182788095828033536 }, some { target := 905, numerator := 79137417519929514491117568 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 18 = expected := by
  rfl

end Left18

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected ++ Left4.expected ++ Left5.expected ++ Left6.expected ++ Left7.expected ++ Left8.expected ++ Left9.expected ++ Left10.expected ++ Left11.expected ++ Left12.expected ++ Left13.expected ++ Left14.expected ++ Left15.expected ++ Left16.expected ++ Left17.expected ++ Left18.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq, Left4.routed_eq, Left5.routed_eq, Left6.routed_eq, Left7.routed_eq, Left8.routed_eq, Left9.routed_eq, Left10.routed_eq, Left11.routed_eq, Left12.routed_eq, Left13.routed_eq, Left14.routed_eq, Left15.routed_eq, Left16.routed_eq, Left17.routed_eq, Left18.routed_eq]
  rfl

end Slot0

namespace Slot1

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨1, 262, #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0], #[206963736576, 24461784907776, 0, 232137462644736, 0, 0, 0, 0, 0, 0, 0, 24461801684992, 0, 0, 0, 0, 0, 0, 206963736576]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 121, numerator := 175135122229741411740155904 }, some { target := 122, numerator := 20699847039183142753564360704 }, some { target := 124, numerator := 196437422163851522457986924544 }, some { target := 132, numerator := 20699861236258550482278023168 }, some { target := 139, numerator := 175135122229741411740155904 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 196, numerator := 130419771873211689593733120 }, some { target := 197, numerator := 15414779710029999922867077120 }, some { target := 199, numerator := 146283186717761772043181752320 }, some { target := 207, numerator := 15414790282320197167653847040 }, some { target := 214, numerator := 130419771873211689593733120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 231, numerator := 137872330265966643284803584 }, some { target := 232, numerator := 16295624264888857061316624384 }, some { target := 234, numerator := 154642225958776730445649281024 }, some { target := 242, numerator := 16295635441309922720091209728 }, some { target := 249, numerator := 137872330265966643284803584 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 337, numerator := 178861401426118888585691136 }, some { target := 338, numerator := 21140269316612571322789134336 }, some { target := 340, numerator := 200616941784359001659220688896 }, some { target := 348, numerator := 21140283815753413258496704512 }, some { target := 355, numerator := 178861401426118888585691136 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 412, numerator := 2395997523270717611679154176 }, some { target := 413, numerator := 283191524387122570011529445376 }, some { target := 415, numerator := 2687431115986309126393310478336 }, some { target := 423, numerator := 283191718615196765108612104192 }, some { target := 430, numerator := 2395997523270717611679154176 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 447, numerator := 4333662705387005571357474816 }, some { target := 448, numerator := 512211108650425426008411734016 }, some { target := 450, numerator := 4860781318650198311034867941376 }, some { target := 458, numerator := 512211459952525408742326403072 }, some { target := 465, numerator := 4333662705387005571357474816 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 508, numerator := 130419771873211689593733120 }, some { target := 509, numerator := 15414779710029999922867077120 }, some { target := 511, numerator := 146283186717761772043181752320 }, some { target := 519, numerator := 15414790282320197167653847040 }, some { target := 526, numerator := 130419771873211689593733120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 543, numerator := 2395997523270717611679154176 }, some { target := 544, numerator := 283191524387122570011529445376 }, some { target := 546, numerator := 2687431115986309126393310478336 }, some { target := 554, numerator := 283191718615196765108612104192 }, some { target := 561, numerator := 2395997523270717611679154176 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 578, numerator := 141598609462344120130338816 }, some { target := 579, numerator := 16736046542318285630541398016 }, some { target := 581, numerator := 158821745579284209646883045376 }, some { target := 589, numerator := 16736058020804785496309891072 }, some { target := 596, numerator := 141598609462344120130338816 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 679, numerator := 141598609462344120130338816 }, some { target := 680, numerator := 16736046542318285630541398016 }, some { target := 682, numerator := 158821745579284209646883045376 }, some { target := 690, numerator := 16736058020804785496309891072 }, some { target := 697, numerator := 141598609462344120130338816 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 714, numerator := 137872330265966643284803584 }, some { target := 715, numerator := 16295624264888857061316624384 }, some { target := 717, numerator := 154642225958776730445649281024 }, some { target := 725, numerator := 16295635441309922720091209728 }, some { target := 732, numerator := 137872330265966643284803584 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 775, numerator := 137872330265966643284803584 }, some { target := 776, numerator := 16295624264888857061316624384 }, some { target := 778, numerator := 154642225958776730445649281024 }, some { target := 786, numerator := 16295635441309922720091209728 }, some { target := 793, numerator := 137872330265966643284803584 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 810, numerator := 4333662705387005571357474816 }, some { target := 811, numerator := 512211108650425426008411734016 }, some { target := 813, numerator := 4860781318650198311034867941376 }, some { target := 821, numerator := 512211459952525408742326403072 }, some { target := 828, numerator := 4333662705387005571357474816 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 845, numerator := 137872330265966643284803584 }, some { target := 846, numerator := 16295624264888857061316624384 }, some { target := 848, numerator := 154642225958776730445649281024 }, some { target := 856, numerator := 16295635441309922720091209728 }, some { target := 863, numerator := 137872330265966643284803584 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 906, numerator := 175135122229741411740155904 }, some { target := 907, numerator := 20699847039183142753564360704 }, some { target := 909, numerator := 196437422163851522457986924544 }, some { target := 917, numerator := 20699861236258550482278023168 }, some { target := 924, numerator := 175135122229741411740155904 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 941, numerator := 178861401426118888585691136 }, some { target := 942, numerator := 21140269316612571322789134336 }, some { target := 944, numerator := 200616941784359001659220688896 }, some { target := 952, numerator := 21140283815753413258496704512 }, some { target := 959, numerator := 178861401426118888585691136 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected ++ Left4.expected ++ Left5.expected ++ Left6.expected ++ Left7.expected ++ Left8.expected ++ Left9.expected ++ Left10.expected ++ Left11.expected ++ Left12.expected ++ Left13.expected ++ Left14.expected ++ Left15.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq, Left4.routed_eq, Left5.routed_eq, Left6.routed_eq, Left7.routed_eq, Left8.routed_eq, Left9.routed_eq, Left10.routed_eq, Left11.routed_eq, Left12.routed_eq, Left13.routed_eq, Left14.routed_eq, Left15.routed_eq]
  rfl

end Slot1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent1
