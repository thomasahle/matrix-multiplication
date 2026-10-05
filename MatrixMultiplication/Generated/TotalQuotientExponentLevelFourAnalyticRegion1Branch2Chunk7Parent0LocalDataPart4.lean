import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk7Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 4, for region 1, branch 2,
parent 30; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot14

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨14, 6, #[52224319291392, 0, 0, 177026338127872, 0, 52224319291392, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 3, 5]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        2 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1, numerator := 22049758584411639085403209728 }, some { target := 2, numerator := 22049758584411639085403209728 }, some { target := 3, numerator := 22049758584411639085403209728 }, some { target := 4, numerator := 22049758584411639085403209728 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 51, numerator := 74742726602573228219509506048 }, some { target := 52, numerator := 74742726602573228219509506048 }, some { target := 53, numerator := 74742726602573228219509506048 }, some { target := 54, numerator := 74742726602573228219509506048 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 140, numerator := 22049758584411639085403209728 }, some { target := 141, numerator := 22049758584411639085403209728 }, some { target := 142, numerator := 22049758584411639085403209728 }, some { target := 143, numerator := 22049758584411639085403209728 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left3.expected ++ Left5.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left3.routed_eq, Left5.routed_eq]
  rfl

end Slot14

namespace Slot15

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨15, 57, #[3092376453120, 2405181685760, 2748779069440, 3229815406592, 38139309588480, 85761906966528, 2405181685760, 38139309588480, 2748779069440, 2680059592704, 2680059592704, 2680059592704, 85761906966528, 2680059592704, 3092376453120, 3229815406592, 0, 0, 0], #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416]⟩

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
  [some { target := 121, numerator := 72677220171363839838781440 }, some { target := 122, numerator := 1938059204569702395700838400 }, some { target := 123, numerator := 1853269114369777915888926720 }, some { target := 124, numerator := 60564350142803199865651200 }, some { target := 125, numerator := 1901720594484020475781447680 }, some { target := 126, numerator := 60564350142803199865651200 }, some { target := 127, numerator := 1853269114369777915888926720 }, some { target := 128, numerator := 1053819692484775677662330880 }, some { target := 129, numerator := 1901720594484020475781447680 }, some { target := 130, numerator := 29688644440002128574142218240 }, some { target := 131, numerator := 1162835522741821437420503040 }, some { target := 132, numerator := 1938059204569702395700838400 }, some { target := 133, numerator := 1853269114369777915888926720 }, some { target := 134, numerator := 60564350142803199865651200 }, some { target := 135, numerator := 1162835522741821437420503040 }, some { target := 136, numerator := 60564350142803199865651200 }, some { target := 137, numerator := 1865381984398338555862056960 }, some { target := 138, numerator := 1053819692484775677662330880 }, some { target := 139, numerator := 72677220171363839838781440 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 196, numerator := 56526726799949653207941120 }, some { target := 197, numerator := 1507379381331990752211763200 }, some { target := 198, numerator := 1441431533398716156802498560 }, some { target := 199, numerator := 47105605666624711006617600 }, some { target := 200, numerator := 1479116017932015925607792640 }, some { target := 201, numerator := 47105605666624711006617600 }, some { target := 202, numerator := 1441431533398716156802498560 }, some { target := 203, numerator := 819637538599269971515146240 }, some { target := 204, numerator := 1479116017932015925607792640 }, some { target := 205, numerator := 23091167897779433335443947520 }, some { target := 206, numerator := 904427628799194451327057920 }, some { target := 207, numerator := 1507379381331990752211763200 }, some { target := 208, numerator := 1441431533398716156802498560 }, some { target := 209, numerator := 47105605666624711006617600 }, some { target := 210, numerator := 904427628799194451327057920 }, some { target := 211, numerator := 47105605666624711006617600 }, some { target := 212, numerator := 1450852654532041099003822080 }, some { target := 213, numerator := 819637538599269971515146240 }, some { target := 214, numerator := 56526726799949653207941120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 231, numerator := 64601973485656746523361280 }, some { target := 232, numerator := 1722719292950846573956300800 }, some { target := 233, numerator := 1647350323884247036345712640 }, some { target := 234, numerator := 53834977904713955436134400 }, some { target := 235, numerator := 1690418306208018200694620160 }, some { target := 236, numerator := 53834977904713955436134400 }, some { target := 237, numerator := 1647350323884247036345712640 }, some { target := 238, numerator := 936728615542022824588738560 }, some { target := 239, numerator := 1690418306208018200694620160 }, some { target := 240, numerator := 26389906168890780954793082880 }, some { target := 241, numerator := 1033631575770507944373780480 }, some { target := 242, numerator := 1722719292950846573956300800 }, some { target := 243, numerator := 1647350323884247036345712640 }, some { target := 244, numerator := 53834977904713955436134400 }, some { target := 245, numerator := 1033631575770507944373780480 }, some { target := 246, numerator := 53834977904713955436134400 }, some { target := 247, numerator := 1658117319465189827432939520 }, some { target := 248, numerator := 936728615542022824588738560 }, some { target := 249, numerator := 64601973485656746523361280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 337, numerator := 75907318845646677164949504 }, some { target := 338, numerator := 2024195169217244724398653440 }, some { target := 339, numerator := 1935636630563990267706212352 }, some { target := 340, numerator := 63256099038038897637457920 }, some { target := 341, numerator := 1986241509794421385816178688 }, some { target := 342, numerator := 63256099038038897637457920 }, some { target := 343, numerator := 1935636630563990267706212352 }, some { target := 344, numerator := 1100656123261876818891767808 }, some { target := 345, numerator := 1986241509794421385816178688 }, some { target := 346, numerator := 31008139748446667621881872384 }, some { target := 347, numerator := 1214517101530346834639192064 }, some { target := 348, numerator := 2024195169217244724398653440 }, some { target := 349, numerator := 1935636630563990267706212352 }, some { target := 350, numerator := 63256099038038897637457920 }, some { target := 351, numerator := 1214517101530346834639192064 }, some { target := 352, numerator := 63256099038038897637457920 }, some { target := 353, numerator := 1948287850371598047233703936 }, some { target := 354, numerator := 1100656123261876818891767808 }, some { target := 355, numerator := 75907318845646677164949504 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 412, numerator := 896352382113487358011637760 }, some { target := 413, numerator := 23902730189692996213643673600 }, some { target := 414, numerator := 22856985743893927629296762880 }, some { target := 415, numerator := 746960318427906131676364800 }, some { target := 416, numerator := 23454553998636252534637854720 }, some { target := 417, numerator := 746960318427906131676364800 }, some { target := 418, numerator := 22856985743893927629296762880 }, some { target := 419, numerator := 12997109540645566691168747520 }, some { target := 420, numerator := 23454553998636252534637854720 }, some { target := 421, numerator := 366159948093359585747754024960 }, some { target := 422, numerator := 14341638113815797728186204160 }, some { target := 423, numerator := 23902730189692996213643673600 }, some { target := 424, numerator := 22856985743893927629296762880 }, some { target := 425, numerator := 746960318427906131676364800 }, some { target := 426, numerator := 14341638113815797728186204160 }, some { target := 427, numerator := 746960318427906131676364800 }, some { target := 428, numerator := 23006377807579508855632035840 }, some { target := 429, numerator := 12997109540645566691168747520 }, some { target := 430, numerator := 896352382113487358011637760 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 447, numerator := 2015581572752490491528871936 }, some { target := 448, numerator := 53748841940066413107436584960 }, some { target := 449, numerator := 51397330105188507533986234368 }, some { target := 450, numerator := 1679651310627075409607393280 }, some { target := 451, numerator := 52741051153690167861672148992 }, some { target := 452, numerator := 1679651310627075409607393280 }, some { target := 453, numerator := 51397330105188507533986234368 }, some { target := 454, numerator := 29225932804911112127168643072 }, some { target := 455, numerator := 52741051153690167861672148992 }, some { target := 456, numerator := 823365072469392365789544185856 }, some { target := 457, numerator := 32249305164039847864461950976 }, some { target := 458, numerator := 53748841940066413107436584960 }, some { target := 459, numerator := 51397330105188507533986234368 }, some { target := 460, numerator := 1679651310627075409607393280 }, some { target := 461, numerator := 32249305164039847864461950976 }, some { target := 462, numerator := 1679651310627075409607393280 }, some { target := 463, numerator := 51733260367313922615907713024 }, some { target := 464, numerator := 29225932804911112127168643072 }, some { target := 465, numerator := 2015581572752490491528871936 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 508, numerator := 56526726799949653207941120 }, some { target := 509, numerator := 1507379381331990752211763200 }, some { target := 510, numerator := 1441431533398716156802498560 }, some { target := 511, numerator := 47105605666624711006617600 }, some { target := 512, numerator := 1479116017932015925607792640 }, some { target := 513, numerator := 47105605666624711006617600 }, some { target := 514, numerator := 1441431533398716156802498560 }, some { target := 515, numerator := 819637538599269971515146240 }, some { target := 516, numerator := 1479116017932015925607792640 }, some { target := 517, numerator := 23091167897779433335443947520 }, some { target := 518, numerator := 904427628799194451327057920 }, some { target := 519, numerator := 1507379381331990752211763200 }, some { target := 520, numerator := 1441431533398716156802498560 }, some { target := 521, numerator := 47105605666624711006617600 }, some { target := 522, numerator := 904427628799194451327057920 }, some { target := 523, numerator := 47105605666624711006617600 }, some { target := 524, numerator := 1450852654532041099003822080 }, some { target := 525, numerator := 819637538599269971515146240 }, some { target := 526, numerator := 56526726799949653207941120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 543, numerator := 896352382113487358011637760 }, some { target := 544, numerator := 23902730189692996213643673600 }, some { target := 545, numerator := 22856985743893927629296762880 }, some { target := 546, numerator := 746960318427906131676364800 }, some { target := 547, numerator := 23454553998636252534637854720 }, some { target := 548, numerator := 746960318427906131676364800 }, some { target := 549, numerator := 22856985743893927629296762880 }, some { target := 550, numerator := 12997109540645566691168747520 }, some { target := 551, numerator := 23454553998636252534637854720 }, some { target := 552, numerator := 366159948093359585747754024960 }, some { target := 553, numerator := 14341638113815797728186204160 }, some { target := 554, numerator := 23902730189692996213643673600 }, some { target := 555, numerator := 22856985743893927629296762880 }, some { target := 556, numerator := 746960318427906131676364800 }, some { target := 557, numerator := 14341638113815797728186204160 }, some { target := 558, numerator := 746960318427906131676364800 }, some { target := 559, numerator := 23006377807579508855632035840 }, some { target := 560, numerator := 12997109540645566691168747520 }, some { target := 561, numerator := 896352382113487358011637760 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 578, numerator := 64601973485656746523361280 }, some { target := 579, numerator := 1722719292950846573956300800 }, some { target := 580, numerator := 1647350323884247036345712640 }, some { target := 581, numerator := 53834977904713955436134400 }, some { target := 582, numerator := 1690418306208018200694620160 }, some { target := 583, numerator := 53834977904713955436134400 }, some { target := 584, numerator := 1647350323884247036345712640 }, some { target := 585, numerator := 936728615542022824588738560 }, some { target := 586, numerator := 1690418306208018200694620160 }, some { target := 587, numerator := 26389906168890780954793082880 }, some { target := 588, numerator := 1033631575770507944373780480 }, some { target := 589, numerator := 1722719292950846573956300800 }, some { target := 590, numerator := 1647350323884247036345712640 }, some { target := 591, numerator := 53834977904713955436134400 }, some { target := 592, numerator := 1033631575770507944373780480 }, some { target := 593, numerator := 53834977904713955436134400 }, some { target := 594, numerator := 1658117319465189827432939520 }, some { target := 595, numerator := 936728615542022824588738560 }, some { target := 596, numerator := 64601973485656746523361280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 679, numerator := 62986924148515327860277248 }, some { target := 680, numerator := 1679651310627075409607393280 }, some { target := 681, numerator := 1606166565787140860437069824 }, some { target := 682, numerator := 52489103457096106550231040 }, some { target := 683, numerator := 1648157848552817745677254656 }, some { target := 684, numerator := 52489103457096106550231040 }, some { target := 685, numerator := 1606166565787140860437069824 }, some { target := 686, numerator := 913310400153472253974020096 }, some { target := 687, numerator := 1648157848552817745677254656 }, some { target := 688, numerator := 25730158514668511430923255808 }, some { target := 689, numerator := 1007790786376245245764435968 }, some { target := 690, numerator := 1679651310627075409607393280 }, some { target := 691, numerator := 1606166565787140860437069824 }, some { target := 692, numerator := 52489103457096106550231040 }, some { target := 693, numerator := 1007790786376245245764435968 }, some { target := 694, numerator := 52489103457096106550231040 }, some { target := 695, numerator := 1616664386478560081747116032 }, some { target := 696, numerator := 913310400153472253974020096 }, some { target := 697, numerator := 62986924148515327860277248 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 714, numerator := 62986924148515327860277248 }, some { target := 715, numerator := 1679651310627075409607393280 }, some { target := 716, numerator := 1606166565787140860437069824 }, some { target := 717, numerator := 52489103457096106550231040 }, some { target := 718, numerator := 1648157848552817745677254656 }, some { target := 719, numerator := 52489103457096106550231040 }, some { target := 720, numerator := 1606166565787140860437069824 }, some { target := 721, numerator := 913310400153472253974020096 }, some { target := 722, numerator := 1648157848552817745677254656 }, some { target := 723, numerator := 25730158514668511430923255808 }, some { target := 724, numerator := 1007790786376245245764435968 }, some { target := 725, numerator := 1679651310627075409607393280 }, some { target := 726, numerator := 1606166565787140860437069824 }, some { target := 727, numerator := 52489103457096106550231040 }, some { target := 728, numerator := 1007790786376245245764435968 }, some { target := 729, numerator := 52489103457096106550231040 }, some { target := 730, numerator := 1616664386478560081747116032 }, some { target := 731, numerator := 913310400153472253974020096 }, some { target := 732, numerator := 62986924148515327860277248 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 775, numerator := 62986924148515327860277248 }, some { target := 776, numerator := 1679651310627075409607393280 }, some { target := 777, numerator := 1606166565787140860437069824 }, some { target := 778, numerator := 52489103457096106550231040 }, some { target := 779, numerator := 1648157848552817745677254656 }, some { target := 780, numerator := 52489103457096106550231040 }, some { target := 781, numerator := 1606166565787140860437069824 }, some { target := 782, numerator := 913310400153472253974020096 }, some { target := 783, numerator := 1648157848552817745677254656 }, some { target := 784, numerator := 25730158514668511430923255808 }, some { target := 785, numerator := 1007790786376245245764435968 }, some { target := 786, numerator := 1679651310627075409607393280 }, some { target := 787, numerator := 1606166565787140860437069824 }, some { target := 788, numerator := 52489103457096106550231040 }, some { target := 789, numerator := 1007790786376245245764435968 }, some { target := 790, numerator := 52489103457096106550231040 }, some { target := 791, numerator := 1616664386478560081747116032 }, some { target := 792, numerator := 913310400153472253974020096 }, some { target := 793, numerator := 62986924148515327860277248 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 810, numerator := 2015581572752490491528871936 }, some { target := 811, numerator := 53748841940066413107436584960 }, some { target := 812, numerator := 51397330105188507533986234368 }, some { target := 813, numerator := 1679651310627075409607393280 }, some { target := 814, numerator := 52741051153690167861672148992 }, some { target := 815, numerator := 1679651310627075409607393280 }, some { target := 816, numerator := 51397330105188507533986234368 }, some { target := 817, numerator := 29225932804911112127168643072 }, some { target := 818, numerator := 52741051153690167861672148992 }, some { target := 819, numerator := 823365072469392365789544185856 }, some { target := 820, numerator := 32249305164039847864461950976 }, some { target := 821, numerator := 53748841940066413107436584960 }, some { target := 822, numerator := 51397330105188507533986234368 }, some { target := 823, numerator := 1679651310627075409607393280 }, some { target := 824, numerator := 32249305164039847864461950976 }, some { target := 825, numerator := 1679651310627075409607393280 }, some { target := 826, numerator := 51733260367313922615907713024 }, some { target := 827, numerator := 29225932804911112127168643072 }, some { target := 828, numerator := 2015581572752490491528871936 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 845, numerator := 62986924148515327860277248 }, some { target := 846, numerator := 1679651310627075409607393280 }, some { target := 847, numerator := 1606166565787140860437069824 }, some { target := 848, numerator := 52489103457096106550231040 }, some { target := 849, numerator := 1648157848552817745677254656 }, some { target := 850, numerator := 52489103457096106550231040 }, some { target := 851, numerator := 1606166565787140860437069824 }, some { target := 852, numerator := 913310400153472253974020096 }, some { target := 853, numerator := 1648157848552817745677254656 }, some { target := 854, numerator := 25730158514668511430923255808 }, some { target := 855, numerator := 1007790786376245245764435968 }, some { target := 856, numerator := 1679651310627075409607393280 }, some { target := 857, numerator := 1606166565787140860437069824 }, some { target := 858, numerator := 52489103457096106550231040 }, some { target := 859, numerator := 1007790786376245245764435968 }, some { target := 860, numerator := 52489103457096106550231040 }, some { target := 861, numerator := 1616664386478560081747116032 }, some { target := 862, numerator := 913310400153472253974020096 }, some { target := 863, numerator := 62986924148515327860277248 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 906, numerator := 72677220171363839838781440 }, some { target := 907, numerator := 1938059204569702395700838400 }, some { target := 908, numerator := 1853269114369777915888926720 }, some { target := 909, numerator := 60564350142803199865651200 }, some { target := 910, numerator := 1901720594484020475781447680 }, some { target := 911, numerator := 60564350142803199865651200 }, some { target := 912, numerator := 1853269114369777915888926720 }, some { target := 913, numerator := 1053819692484775677662330880 }, some { target := 914, numerator := 1901720594484020475781447680 }, some { target := 915, numerator := 29688644440002128574142218240 }, some { target := 916, numerator := 1162835522741821437420503040 }, some { target := 917, numerator := 1938059204569702395700838400 }, some { target := 918, numerator := 1853269114369777915888926720 }, some { target := 919, numerator := 60564350142803199865651200 }, some { target := 920, numerator := 1162835522741821437420503040 }, some { target := 921, numerator := 60564350142803199865651200 }, some { target := 922, numerator := 1865381984398338555862056960 }, some { target := 923, numerator := 1053819692484775677662330880 }, some { target := 924, numerator := 72677220171363839838781440 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 941, numerator := 75907318845646677164949504 }, some { target := 942, numerator := 2024195169217244724398653440 }, some { target := 943, numerator := 1935636630563990267706212352 }, some { target := 944, numerator := 63256099038038897637457920 }, some { target := 945, numerator := 1986241509794421385816178688 }, some { target := 946, numerator := 63256099038038897637457920 }, some { target := 947, numerator := 1935636630563990267706212352 }, some { target := 948, numerator := 1100656123261876818891767808 }, some { target := 949, numerator := 1986241509794421385816178688 }, some { target := 950, numerator := 31008139748446667621881872384 }, some { target := 951, numerator := 1214517101530346834639192064 }, some { target := 952, numerator := 2024195169217244724398653440 }, some { target := 953, numerator := 1935636630563990267706212352 }, some { target := 954, numerator := 63256099038038897637457920 }, some { target := 955, numerator := 1214517101530346834639192064 }, some { target := 956, numerator := 63256099038038897637457920 }, some { target := 957, numerator := 1948287850371598047233703936 }, some { target := 958, numerator := 1100656123261876818891767808 }, some { target := 959, numerator := 75907318845646677164949504 }]

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

end Slot15

namespace Slot16

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨16, 247, #[147035521024, 23473808211968, 0, 234233306021888, 0, 0, 0, 0, 0, 0, 0, 23473808211968, 0, 0, 0, 0, 0, 0, 147018743808], #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 3, 11, 18]

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
  [some { target := 34, numerator := 87350844153806747630305280 }, some { target := 35, numerator := 89846582558201226134028288 }, some { target := 36, numerator := 87350844153806747630305280 }, some { target := 37, numerator := 77367890536228833615413248 }, some { target := 38, numerator := 3621316424776388308902084608 }, some { target := 39, numerator := 985816669735819008970588160 }, some { target := 40, numerator := 89846582558201226134028288 }, some { target := 41, numerator := 3621316424776388308902084608 }, some { target := 42, numerator := 87350844153806747630305280 }, some { target := 43, numerator := 87350844153806747630305280 }, some { target := 44, numerator := 74872152131834355111690240 }, some { target := 45, numerator := 87350844153806747630305280 }, some { target := 46, numerator := 985816669735819008970588160 }, some { target := 47, numerator := 74872152131834355111690240 }, some { target := 48, numerator := 87350844153806747630305280 }, some { target := 49, numerator := 77367890536228833615413248 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 79, numerator := 13945317080797627034852392960 }, some { target := 80, numerator := 14343754711677559235848175616 }, some { target := 81, numerator := 13945317080797627034852392960 }, some { target := 82, numerator := 12351566557277898230869262336 }, some { target := 83, numerator := 578133002406781623644880633856 }, some { target := 84, numerator := 157382864197573219393334149120 }, some { target := 85, numerator := 14343754711677559235848175616 }, some { target := 86, numerator := 578133002406781623644880633856 }, some { target := 87, numerator := 13945317080797627034852392960 }, some { target := 88, numerator := 13945317080797627034852392960 }, some { target := 89, numerator := 11953128926397966029873479680 }, some { target := 90, numerator := 13945317080797627034852392960 }, some { target := 91, numerator := 157382864197573219393334149120 }, some { target := 92, numerator := 11953128926397966029873479680 }, some { target := 93, numerator := 13945317080797627034852392960 }, some { target := 94, numerator := 12351566557277898230869262336 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 154, numerator := 139153293486199047206584975360 }, some { target := 155, numerator := 143129101871519019983915974656 }, some { target := 156, numerator := 139153293486199047206584975360 }, some { target := 157, numerator := 123250059944919156097260978176 }, some { target := 158, numerator := 5768897967099280499907279978496 }, some { target := 159, numerator := 1570444312201389247045744721920 }, some { target := 160, numerator := 143129101871519019983915974656 }, some { target := 161, numerator := 5768897967099280499907279978496 }, some { target := 162, numerator := 139153293486199047206584975360 }, some { target := 163, numerator := 139153293486199047206584975360 }, some { target := 164, numerator := 119274251559599183319929978880 }, some { target := 165, numerator := 139153293486199047206584975360 }, some { target := 166, numerator := 1570444312201389247045744721920 }, some { target := 167, numerator := 119274251559599183319929978880 }, some { target := 168, numerator := 139153293486199047206584975360 }, some { target := 169, numerator := 123250059944919156097260978176 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 492, numerator := 13945317080797627034852392960 }, some { target := 493, numerator := 14343754711677559235848175616 }, some { target := 494, numerator := 13945317080797627034852392960 }, some { target := 495, numerator := 12351566557277898230869262336 }, some { target := 496, numerator := 578133002406781623644880633856 }, some { target := 497, numerator := 157382864197573219393334149120 }, some { target := 498, numerator := 14343754711677559235848175616 }, some { target := 499, numerator := 578133002406781623644880633856 }, some { target := 500, numerator := 13945317080797627034852392960 }, some { target := 501, numerator := 13945317080797627034852392960 }, some { target := 502, numerator := 11953128926397966029873479680 }, some { target := 503, numerator := 13945317080797627034852392960 }, some { target := 504, numerator := 157382864197573219393334149120 }, some { target := 505, numerator := 11953128926397966029873479680 }, some { target := 506, numerator := 13945317080797627034852392960 }, some { target := 507, numerator := 12351566557277898230869262336 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 890, numerator := 87340877147399421438197760 }, some { target := 891, numerator := 89836330780182262050717696 }, some { target := 892, numerator := 87340877147399421438197760 }, some { target := 893, numerator := 77359062616268058988118016 }, some { target := 894, numerator := 3620903221167901728766427136 }, some { target := 895, numerator := 985704184949222041945374720 }, some { target := 896, numerator := 89836330780182262050717696 }, some { target := 897, numerator := 3620903221167901728766427136 }, some { target := 898, numerator := 87340877147399421438197760 }, some { target := 899, numerator := 87340877147399421438197760 }, some { target := 900, numerator := 74863608983485218375598080 }, some { target := 901, numerator := 87340877147399421438197760 }, some { target := 902, numerator := 985704184949222041945374720 }, some { target := 903, numerator := 74863608983485218375598080 }, some { target := 904, numerator := 87340877147399421438197760 }, some { target := 905, numerator := 77359062616268058988118016 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 18 = expected := by
  rfl

end Left18

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left3.expected ++ Left11.expected ++ Left18.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left3.routed_eq, Left11.routed_eq, Left18.routed_eq]
  rfl

end Slot16

namespace Slot17

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨17, 81, #[3648641826816, 0, 137088846528512, 0, 0, 137078478209024, 0, 0, 0, 0, 0, 0, 3659010146304, 0, 0, 0, 0, 0, 0], #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 2, 5, 12]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- The semantic right support is the shared checked table. -/
theorem routedRightSupport_eq :
    data.routedRightSupport parent coordinate = rightSupport := by
  unfold BetaFourLocalSlotData.routedRightSupport rightSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).2 coordinate =
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 10, numerator := 507733833200154272228966400 }, some { target := 11, numerator := 10174986017331091615468486656 }, some { target := 12, numerator := 17080166148853189717782429696 }, some { target := 13, numerator := 16389648135700979907551035392 }, some { target := 14, numerator := 507733833200154272228966400 }, some { target := 15, numerator := 16389648135700979907551035392 }, some { target := 16, numerator := 10946741443795326109256515584 }, some { target := 17, numerator := 528043186528160443118125056 }, some { target := 18, numerator := 10174986017331091615468486656 }, some { target := 19, numerator := 487424479872148101339807744 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 55, numerator := 19076864444556838358011084800 }, some { target := 56, numerator := 382300363468919040694542139392 }, some { target := 57, numerator := 641745719914892042363492892672 }, some { target := 58, numerator := 615801184270294742196597817344 }, some { target := 59, numerator := 19076864444556838358011084800 }, some { target := 60, numerator := 615801184270294742196597817344 }, some { target := 61, numerator := 411297197424645434998718988288 }, some { target := 62, numerator := 19839939022339111892331528192 }, some { target := 63, numerator := 382300363468919040694542139392 }, some { target := 64, numerator := 18313789866774564823690641408 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 144, numerator := 19075421620939898119362969600 }, some { target := 145, numerator := 382271449283635558312033910784 }, some { target := 146, numerator := 641697183328418172735370297344 }, some { target := 147, numerator := 615754609923939911293036658688 }, some { target := 148, numerator := 19075421620939898119362969600 }, some { target := 149, numerator := 615754609923939911293036658688 }, some { target := 150, numerator := 411266090147464203453465624576 }, some { target := 151, numerator := 19838438485777494044137488384 }, some { target := 152, numerator := 382271449283635558312033910784 }, some { target := 153, numerator := 18312404756102302194588450816 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 482, numerator := 509176656817094510877081600 }, some { target := 483, numerator := 10203900202614573997976715264 }, some { target := 484, numerator := 17128702735327059345905025024 }, some { target := 485, numerator := 16436222482055810811112194048 }, some { target := 486, numerator := 509176656817094510877081600 }, some { target := 487, numerator := 16436222482055810811112194048 }, some { target := 488, numerator := 10977848720976557654509879296 }, some { target := 489, numerator := 529543723089778291312164864 }, some { target := 490, numerator := 10203900202614573997976715264 }, some { target := 491, numerator := 488809590544410730441998336 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left2.expected ++ Left5.expected ++ Left12.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left2.routed_eq, Left5.routed_eq, Left12.routed_eq]
  rfl

end Slot17

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent0
