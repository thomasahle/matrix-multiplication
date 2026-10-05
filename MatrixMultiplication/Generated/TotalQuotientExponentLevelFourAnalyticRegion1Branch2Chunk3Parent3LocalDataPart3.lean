import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk3Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 3, for region 1, branch 2,
parent 17; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot10

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨10, 6, #[2130303778816, 50989851738112, 38139309588480, 44255343017984, 2130303778816, 44186623541248, 44392781971456, 2130303778816, 50989851738112, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

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
  [some { target := 142, numerator := 5270160994882524058484736 }, some { target := 143, numerator := 140537626530200641559592960 }, some { target := 144, numerator := 134389105369504363491360768 }, some { target := 145, numerator := 4391800829068770048737280 }, some { target := 146, numerator := 137902546032759379530350592 }, some { target := 147, numerator := 4391800829068770048737280 }, some { target := 148, numerator := 134389105369504363491360768 }, some { target := 149, numerator := 76417334425796598848028672 }, some { target := 150, numerator := 137902546032759379530350592 }, some { target := 151, numerator := 2152860766409511077891014656 }, some { target := 152, numerator := 84322575918120384935755776 }, some { target := 153, numerator := 140537626530200641559592960 }, some { target := 154, numerator := 134389105369504363491360768 }, some { target := 155, numerator := 4391800829068770048737280 }, some { target := 156, numerator := 84322575918120384935755776 }, some { target := 157, numerator := 4391800829068770048737280 }, some { target := 158, numerator := 135267465535318117501108224 }, some { target := 159, numerator := 76417334425796598848028672 }, some { target := 160, numerator := 5270160994882524058484736 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 282, numerator := 126143853490413962948247552 }, some { target := 283, numerator := 3363836093077705678619934720 }, some { target := 284, numerator := 3216668264005556055180312576 }, some { target := 285, numerator := 105119877908678302456872960 }, some { target := 286, numerator := 3300764166332498697145810944 }, some { target := 287, numerator := 105119877908678302456872960 }, some { target := 288, numerator := 3216668264005556055180312576 }, some { target := 289, numerator := 1829085875611002462749589504 }, some { target := 290, numerator := 3300764166332498697145810944 }, some { target := 291, numerator := 51529764150834103864359124992 }, some { target := 292, numerator := 2018301655846623407171960832 }, some { target := 293, numerator := 3363836093077705678619934720 }, some { target := 294, numerator := 3216668264005556055180312576 }, some { target := 295, numerator := 105119877908678302456872960 }, some { target := 296, numerator := 2018301655846623407171960832 }, some { target := 297, numerator := 105119877908678302456872960 }, some { target := 298, numerator := 3237692239587291715671687168 }, some { target := 299, numerator := 1829085875611002462749589504 }, some { target := 300, numerator := 126143853490413962948247552 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 357, numerator := 94352882327735511369646080 }, some { target := 358, numerator := 2516076862072946969857228800 }, some { target := 359, numerator := 2405998499357255539925975040 }, some { target := 360, numerator := 78627401939779592808038400 }, some { target := 361, numerator := 2468900420909079214172405760 }, some { target := 362, numerator := 78627401939779592808038400 }, some { target := 363, numerator := 2405998499357255539925975040 }, some { target := 364, numerator := 1368116793752164914859868160 }, some { target := 365, numerator := 2468900420909079214172405760 }, some { target := 366, numerator := 38543152430879956394500423680 }, some { target := 367, numerator := 1509646117243768181914337280 }, some { target := 368, numerator := 2516076862072946969857228800 }, some { target := 369, numerator := 2405998499357255539925975040 }, some { target := 370, numerator := 78627401939779592808038400 }, some { target := 371, numerator := 1509646117243768181914337280 }, some { target := 372, numerator := 78627401939779592808038400 }, some { target := 373, numerator := 2421723979745211458487582720 }, some { target := 374, numerator := 1368116793752164914859868160 }, some { target := 375, numerator := 94352882327735511369646080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 392, numerator := 109483344538849854634328064 }, some { target := 393, numerator := 2919555854369329456915415040 }, some { target := 394, numerator := 2791825285740671293175365632 }, some { target := 395, numerator := 91236120449041545528606720 }, some { target := 396, numerator := 2864814182099904529598251008 }, some { target := 397, numerator := 91236120449041545528606720 }, some { target := 398, numerator := 2791825285740671293175365632 }, some { target := 399, numerator := 1587508495813322892197756928 }, some { target := 400, numerator := 2864814182099904529598251008 }, some { target := 401, numerator := 44723946244120165618123014144 }, some { target := 402, numerator := 1751733512621597674149249024 }, some { target := 403, numerator := 2919555854369329456915415040 }, some { target := 404, numerator := 2791825285740671293175365632 }, some { target := 405, numerator := 91236120449041545528606720 }, some { target := 406, numerator := 1751733512621597674149249024 }, some { target := 407, numerator := 91236120449041545528606720 }, some { target := 408, numerator := 2810072509830479602281086976 }, some { target := 409, numerator := 1587508495813322892197756928 }, some { target := 410, numerator := 109483344538849854634328064 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 498, numerator := 5270160994882524058484736 }, some { target := 499, numerator := 140537626530200641559592960 }, some { target := 500, numerator := 134389105369504363491360768 }, some { target := 501, numerator := 4391800829068770048737280 }, some { target := 502, numerator := 137902546032759379530350592 }, some { target := 503, numerator := 4391800829068770048737280 }, some { target := 504, numerator := 134389105369504363491360768 }, some { target := 505, numerator := 76417334425796598848028672 }, some { target := 506, numerator := 137902546032759379530350592 }, some { target := 507, numerator := 2152860766409511077891014656 }, some { target := 508, numerator := 84322575918120384935755776 }, some { target := 509, numerator := 140537626530200641559592960 }, some { target := 510, numerator := 134389105369504363491360768 }, some { target := 511, numerator := 4391800829068770048737280 }, some { target := 512, numerator := 84322575918120384935755776 }, some { target := 513, numerator := 4391800829068770048737280 }, some { target := 514, numerator := 135267465535318117501108224 }, some { target := 515, numerator := 76417334425796598848028672 }, some { target := 516, numerator := 5270160994882524058484736 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 573, numerator := 109313339345466547406635008 }, some { target := 574, numerator := 2915022382545774597510266880 }, some { target := 575, numerator := 2787490153309396958869192704 }, some { target := 576, numerator := 91094449454555456172195840 }, some { target := 577, numerator := 2860365712873041323806949376 }, some { target := 578, numerator := 91094449454555456172195840 }, some { target := 579, numerator := 2787490153309396958869192704 }, some { target := 580, numerator := 1585043420509264937396207616 }, some { target := 581, numerator := 2860365712873041323806949376 }, some { target := 582, numerator := 44654499122623084615610400768 }, some { target := 583, numerator := 1749013429527464758506160128 }, some { target := 584, numerator := 2915022382545774597510266880 }, some { target := 585, numerator := 2787490153309396958869192704 }, some { target := 586, numerator := 91094449454555456172195840 }, some { target := 587, numerator := 1749013429527464758506160128 }, some { target := 588, numerator := 91094449454555456172195840 }, some { target := 589, numerator := 2805709043200308050103631872 }, some { target := 590, numerator := 1585043420509264937396207616 }, some { target := 591, numerator := 109313339345466547406635008 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 608, numerator := 109823354925616469089714176 }, some { target := 609, numerator := 2928622798016439175725711360 }, some { target := 610, numerator := 2800495550603219961787711488 }, some { target := 611, numerator := 91519462438013724241428480 }, some { target := 612, numerator := 2873711120553630941180854272 }, some { target := 613, numerator := 91519462438013724241428480 }, some { target := 614, numerator := 2800495550603219961787711488 }, some { target := 615, numerator := 1592438646421438801800855552 }, some { target := 616, numerator := 2873711120553630941180854272 }, some { target := 617, numerator := 44862840487114327623148240896 }, some { target := 618, numerator := 1757173678809863505435426816 }, some { target := 619, numerator := 2928622798016439175725711360 }, some { target := 620, numerator := 2800495550603219961787711488 }, some { target := 621, numerator := 91519462438013724241428480 }, some { target := 622, numerator := 1757173678809863505435426816 }, some { target := 623, numerator := 91519462438013724241428480 }, some { target := 624, numerator := 2818799443090822706635997184 }, some { target := 625, numerator := 1592438646421438801800855552 }, some { target := 626, numerator := 109823354925616469089714176 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 669, numerator := 5270160994882524058484736 }, some { target := 670, numerator := 140537626530200641559592960 }, some { target := 671, numerator := 134389105369504363491360768 }, some { target := 672, numerator := 4391800829068770048737280 }, some { target := 673, numerator := 137902546032759379530350592 }, some { target := 674, numerator := 4391800829068770048737280 }, some { target := 675, numerator := 134389105369504363491360768 }, some { target := 676, numerator := 76417334425796598848028672 }, some { target := 677, numerator := 137902546032759379530350592 }, some { target := 678, numerator := 2152860766409511077891014656 }, some { target := 679, numerator := 84322575918120384935755776 }, some { target := 680, numerator := 140537626530200641559592960 }, some { target := 681, numerator := 134389105369504363491360768 }, some { target := 682, numerator := 4391800829068770048737280 }, some { target := 683, numerator := 84322575918120384935755776 }, some { target := 684, numerator := 4391800829068770048737280 }, some { target := 685, numerator := 135267465535318117501108224 }, some { target := 686, numerator := 76417334425796598848028672 }, some { target := 687, numerator := 5270160994882524058484736 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 704, numerator := 126143853490413962948247552 }, some { target := 705, numerator := 3363836093077705678619934720 }, some { target := 706, numerator := 3216668264005556055180312576 }, some { target := 707, numerator := 105119877908678302456872960 }, some { target := 708, numerator := 3300764166332498697145810944 }, some { target := 709, numerator := 105119877908678302456872960 }, some { target := 710, numerator := 3216668264005556055180312576 }, some { target := 711, numerator := 1829085875611002462749589504 }, some { target := 712, numerator := 3300764166332498697145810944 }, some { target := 713, numerator := 51529764150834103864359124992 }, some { target := 714, numerator := 2018301655846623407171960832 }, some { target := 715, numerator := 3363836093077705678619934720 }, some { target := 716, numerator := 3216668264005556055180312576 }, some { target := 717, numerator := 105119877908678302456872960 }, some { target := 718, numerator := 2018301655846623407171960832 }, some { target := 719, numerator := 105119877908678302456872960 }, some { target := 720, numerator := 3237692239587291715671687168 }, some { target := 721, numerator := 1829085875611002462749589504 }, some { target := 722, numerator := 126143853490413962948247552 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 739, numerator := 5270160994882524058484736 }, some { target := 740, numerator := 140537626530200641559592960 }, some { target := 741, numerator := 134389105369504363491360768 }, some { target := 742, numerator := 4391800829068770048737280 }, some { target := 743, numerator := 137902546032759379530350592 }, some { target := 744, numerator := 4391800829068770048737280 }, some { target := 745, numerator := 134389105369504363491360768 }, some { target := 746, numerator := 76417334425796598848028672 }, some { target := 747, numerator := 137902546032759379530350592 }, some { target := 748, numerator := 2152860766409511077891014656 }, some { target := 749, numerator := 84322575918120384935755776 }, some { target := 750, numerator := 140537626530200641559592960 }, some { target := 751, numerator := 134389105369504363491360768 }, some { target := 752, numerator := 4391800829068770048737280 }, some { target := 753, numerator := 84322575918120384935755776 }, some { target := 754, numerator := 4391800829068770048737280 }, some { target := 755, numerator := 135267465535318117501108224 }, some { target := 756, numerator := 76417334425796598848028672 }, some { target := 757, numerator := 5270160994882524058484736 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected ++ Left4.expected ++ Left5.expected ++ Left6.expected ++ Left7.expected ++ Left8.expected ++ Left9.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq, Left4.routed_eq, Left5.routed_eq, Left6.routed_eq, Left7.routed_eq, Left8.routed_eq, Left9.routed_eq]
  rfl

end Slot10

namespace Slot11

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨11, 50, #[1653998616576, 139083489738752, 0, 0, 0, 0, 139083456184320, 0, 0, 0, 0, 0, 0, 0, 1654032171008, 0, 0, 0, 0], #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 6, 14]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

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
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 55, numerator := 198908359043048577957888000 }, some { target := 56, numerator := 204591455015707108756684800 }, some { target := 57, numerator := 198908359043048577957888000 }, some { target := 58, numerator := 176175975152414454762700800 }, some { target := 59, numerator := 8246172256327528189054156800 }, some { target := 60, numerator := 2244822909200119665524736000 }, some { target := 61, numerator := 204591455015707108756684800 }, some { target := 62, numerator := 8246172256327528189054156800 }, some { target := 63, numerator := 198908359043048577957888000 }, some { target := 64, numerator := 198908359043048577957888000 }, some { target := 65, numerator := 170492879179755923963904000 }, some { target := 66, numerator := 198908359043048577957888000 }, some { target := 67, numerator := 2244822909200119665524736000 }, some { target := 68, numerator := 170492879179755923963904000 }, some { target := 69, numerator := 198908359043048577957888000 }, some { target := 70, numerator := 176175975152414454762700800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 100, numerator := 16726053115561759867928576000 }, some { target := 101, numerator := 17203940347434953007012249600 }, some { target := 102, numerator := 16726053115561759867928576000 }, some { target := 103, numerator := 14814504188068987311593881600 }, some { target := 104, numerator := 693414373448003244810410393600 }, some { target := 105, numerator := 188765456589911289938051072000 }, some { target := 106, numerator := 17203940347434953007012249600 }, some { target := 107, numerator := 693414373448003244810410393600 }, some { target := 108, numerator := 16726053115561759867928576000 }, some { target := 109, numerator := 16726053115561759867928576000 }, some { target := 110, numerator := 14336616956195794172510208000 }, some { target := 111, numerator := 16726053115561759867928576000 }, some { target := 112, numerator := 188765456589911289938051072000 }, some { target := 113, numerator := 14336616956195794172510208000 }, some { target := 114, numerator := 16726053115561759867928576000 }, some { target := 115, numerator := 14814504188068987311593881600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 315, numerator := 16726049080336493743964160000 }, some { target := 316, numerator := 17203936196917536422363136000 }, some { target := 317, numerator := 16726049080336493743964160000 }, some { target := 318, numerator := 14814500614012323030368256000 }, some { target := 319, numerator := 693414206159092926356914176000 }, some { target := 320, numerator := 188765411049511857967595520000 }, some { target := 321, numerator := 17203936196917536422363136000 }, some { target := 322, numerator := 693414206159092926356914176000 }, some { target := 323, numerator := 16726049080336493743964160000 }, some { target := 324, numerator := 16726049080336493743964160000 }, some { target := 325, numerator := 14336613497431280351969280000 }, some { target := 326, numerator := 16726049080336493743964160000 }, some { target := 327, numerator := 188765411049511857967595520000 }, some { target := 328, numerator := 14336613497431280351969280000 }, some { target := 329, numerator := 16726049080336493743964160000 }, some { target := 330, numerator := 14814500614012323030368256000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 653, numerator := 198912394268314701922304000 }, some { target := 654, numerator := 204595605533123693405798400 }, some { target := 655, numerator := 198912394268314701922304000 }, some { target := 656, numerator := 176179549209078735988326400 }, some { target := 657, numerator := 8246339545237846642550374400 }, some { target := 658, numerator := 2244868449599551635980288000 }, some { target := 659, numerator := 204595605533123693405798400 }, some { target := 660, numerator := 8246339545237846642550374400 }, some { target := 661, numerator := 198912394268314701922304000 }, some { target := 662, numerator := 198912394268314701922304000 }, some { target := 663, numerator := 170496337944269744504832000 }, some { target := 664, numerator := 198912394268314701922304000 }, some { target := 665, numerator := 2244868449599551635980288000 }, some { target := 666, numerator := 170496337944269744504832000 }, some { target := 667, numerator := 198912394268314701922304000 }, some { target := 668, numerator := 176179549209078735988326400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left6.expected ++ Left14.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left6.routed_eq, Left14.routed_eq]
  rfl

end Slot11

namespace Slot12

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨12, 45, #[153243090944, 22633202581504, 0, 235902085365760, 0, 0, 0, 0, 0, 0, 0, 22633202581504, 0, 0, 0, 0, 0, 0, 153243090944], #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

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
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 11, numerator := 11847133150963807813632000 }, some { target := 12, numerator := 237416548345314708585185280 }, some { target := 13, numerator := 398537559198422494850580480 }, some { target := 14, numerator := 382425458113111716224040960 }, some { target := 15, numerator := 11847133150963807813632000 }, some { target := 16, numerator := 382425458113111716224040960 }, some { target := 17, numerator := 255424190734779696461905920 }, some { target := 18, numerator := 12321018477002360126177280 }, some { target := 19, numerator := 237416548345314708585185280 }, some { target := 20, numerator := 11373247824925255501086720 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 31, numerator := 1749759568043444180877312000 }, some { target := 32, numerator := 35065181743590621384781332480 }, some { target := 33, numerator := 58861911868981462244712775680 }, some { target := 34, numerator := 56482238856442378158719631360 }, some { target := 35, numerator := 1749759568043444180877312000 }, some { target := 36, numerator := 56482238856442378158719631360 }, some { target := 37, numerator := 37724816287016656539714846720 }, some { target := 38, numerator := 1819749950765181948112404480 }, some { target := 39, numerator := 35065181743590621384781332480 }, some { target := 40, numerator := 1679769185321706413642219520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 76, numerator := 18237451350674509167329280000 }, some { target := 77, numerator := 365478525067517163713278771200 }, some { target := 78, numerator := 613507863436690488388956979200 }, some { target := 79, numerator := 588704929599773155921389158400 }, some { target := 80, numerator := 18237451350674509167329280000 }, some { target := 81, numerator := 588704929599773155921389158400 }, some { target := 82, numerator := 393199451120542417647619276800 }, some { target := 83, numerator := 18966949404701489534022451200 }, some { target := 84, numerator := 365478525067517163713278771200 }, some { target := 85, numerator := 17507953296647528800636108800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 305, numerator := 1749759568043444180877312000 }, some { target := 306, numerator := 35065181743590621384781332480 }, some { target := 307, numerator := 58861911868981462244712775680 }, some { target := 308, numerator := 56482238856442378158719631360 }, some { target := 309, numerator := 1749759568043444180877312000 }, some { target := 310, numerator := 56482238856442378158719631360 }, some { target := 311, numerator := 37724816287016656539714846720 }, some { target := 312, numerator := 1819749950765181948112404480 }, some { target := 313, numerator := 35065181743590621384781332480 }, some { target := 314, numerator := 1679769185321706413642219520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 643, numerator := 11847133150963807813632000 }, some { target := 644, numerator := 237416548345314708585185280 }, some { target := 645, numerator := 398537559198422494850580480 }, some { target := 646, numerator := 382425458113111716224040960 }, some { target := 647, numerator := 11847133150963807813632000 }, some { target := 648, numerator := 382425458113111716224040960 }, some { target := 649, numerator := 255424190734779696461905920 }, some { target := 650, numerator := 12321018477002360126177280 }, some { target := 651, numerator := 237416548345314708585185280 }, some { target := 652, numerator := 11373247824925255501086720 }]

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

end Slot12

namespace Slot13

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨13, 13, #[3779168567296, 0, 136958319788032, 0, 0, 136958370119680, 0, 0, 0, 0, 0, 0, 3779118235648, 0, 0, 0, 0, 0, 0], #[73529840107520, 67207648247808, 73529840107520, 67207648247808, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

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
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 2, numerator := 3612461586404324120943656960 }, some { target := 3, numerator := 3301857412620027093722333184 }, some { target := 4, numerator := 3612461586404324120943656960 }, some { target := 5, numerator := 3301857412620027093722333184 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 22, numerator := 130916803620311610440359608320 }, some { target := 23, numerator := 119660405552023135523992240128 }, some { target := 24, numerator := 130916803620311610440359608320 }, some { target := 25, numerator := 119660405552023135523992240128 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 72, numerator := 130916851731725997684083916800 }, some { target := 73, numerator := 119660449526755164238349598720 }, some { target := 74, numerator := 130916851731725997684083916800 }, some { target := 75, numerator := 119660449526755164238349598720 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 301, numerator := 3612413474989936877219348480 }, some { target := 302, numerator := 3301813437887998379364974592 }, some { target := 303, numerator := 3612413474989936877219348480 }, some { target := 304, numerator := 3301813437887998379364974592 }]

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

end Slot13

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3.Parent3
