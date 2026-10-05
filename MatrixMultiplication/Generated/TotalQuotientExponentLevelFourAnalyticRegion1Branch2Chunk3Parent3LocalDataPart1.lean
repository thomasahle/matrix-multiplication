import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk3Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 1, for region 1, branch 2,
parent 17; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot3

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨3, 51, #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0], #[1653998616576, 139083489738752, 0, 0, 0, 0, 139083456184320, 0, 0, 0, 0, 0, 0, 0, 1654032171008, 0, 0, 0, 0]⟩

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
  [some { target := 55, numerator := 202886526223909549517045760 }, some { target := 56, numerator := 17060574177872995065287147520 }, some { target := 61, numerator := 17060570061943223618843443200 }, some { target := 69, numerator := 202890642153680995960750080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 100, numerator := 208683284116021250931818496 }, some { target := 101, numerator := 17548019154383652067152494592 }, some { target := 106, numerator := 17548014920855887150810398720 }, some { target := 114, numerator := 208687517643786167273914368 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 126, numerator := 202886526223909549517045760 }, some { target := 127, numerator := 17060574177872995065287147520 }, some { target := 132, numerator := 17060570061943223618843443200 }, some { target := 140, numerator := 202890642153680995960750080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 195, numerator := 179699494655462743857954816 }, some { target := 196, numerator := 15110794271830367057825759232 }, some { target := 201, numerator := 15110790626292569490975621120 }, some { target := 209, numerator := 179703140193260310708092928 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 240, numerator := 8411095701454078752835239936 }, some { target := 241, numerator := 707282660916963309706618601472 }, some { target := 246, numerator := 707282490282274784884052459520 }, some { target := 254, numerator := 8411266336142603575401381888 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 266, numerator := 2289719367384122058835230720 }, some { target := 267, numerator := 192540765721709515736812093440 }, some { target := 272, numerator := 192540719270502095126947430400 }, some { target := 280, numerator := 2289765818591542668699893760 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 315, numerator := 208683284116021250931818496 }, some { target := 316, numerator := 17548019154383652067152494592 }, some { target := 321, numerator := 17548014920855887150810398720 }, some { target := 329, numerator := 208687517643786167273914368 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 341, numerator := 8411095701454078752835239936 }, some { target := 342, numerator := 707282660916963309706618601472 }, some { target := 347, numerator := 707282490282274784884052459520 }, some { target := 355, numerator := 8411266336142603575401381888 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 376, numerator := 202886526223909549517045760 }, some { target := 377, numerator := 17060574177872995065287147520 }, some { target := 382, numerator := 17060570061943223618843443200 }, some { target := 390, numerator := 202890642153680995960750080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 456, numerator := 202886526223909549517045760 }, some { target := 457, numerator := 17060574177872995065287147520 }, some { target := 462, numerator := 17060570061943223618843443200 }, some { target := 470, numerator := 202890642153680995960750080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 482, numerator := 173902736763351042443182080 }, some { target := 483, numerator := 14623349295319710055960412160 }, some { target := 488, numerator := 14623345767379905959008665600 }, some { target := 496, numerator := 173906264703155139394928640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 531, numerator := 202886526223909549517045760 }, some { target := 532, numerator := 17060574177872995065287147520 }, some { target := 537, numerator := 17060570061943223618843443200 }, some { target := 545, numerator := 202890642153680995960750080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 557, numerator := 2289719367384122058835230720 }, some { target := 558, numerator := 192540765721709515736812093440 }, some { target := 563, numerator := 192540719270502095126947430400 }, some { target := 571, numerator := 2289765818591542668699893760 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 592, numerator := 173902736763351042443182080 }, some { target := 593, numerator := 14623349295319710055960412160 }, some { target := 598, numerator := 14623345767379905959008665600 }, some { target := 606, numerator := 173906264703155139394928640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 653, numerator := 202886526223909549517045760 }, some { target := 654, numerator := 17060574177872995065287147520 }, some { target := 659, numerator := 17060570061943223618843443200 }, some { target := 667, numerator := 202890642153680995960750080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 688, numerator := 179699494655462743857954816 }, some { target := 689, numerator := 15110794271830367057825759232 }, some { target := 694, numerator := 15110790626292569490975621120 }, some { target := 702, numerator := 179703140193260310708092928 }]

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

end Slot3

namespace Slot4

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨4, 6, #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416], #[2130303778816, 50989851738112, 38139309588480, 44255343017984, 2130303778816, 44186623541248, 44392781971456, 2130303778816, 50989851738112, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 11, numerator := 5270160994882524058484736 }, some { target := 12, numerator := 126143853490413962948247552 }, some { target := 13, numerator := 94352882327735511369646080 }, some { target := 14, numerator := 109483344538849854634328064 }, some { target := 15, numerator := 5270160994882524058484736 }, some { target := 16, numerator := 109313339345466547406635008 }, some { target := 17, numerator := 109823354925616469089714176 }, some { target := 18, numerator := 5270160994882524058484736 }, some { target := 19, numerator := 126143853490413962948247552 }, some { target := 20, numerator := 5270160994882524058484736 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 31, numerator := 140537626530200641559592960 }, some { target := 32, numerator := 3363836093077705678619934720 }, some { target := 33, numerator := 2516076862072946969857228800 }, some { target := 34, numerator := 2919555854369329456915415040 }, some { target := 35, numerator := 140537626530200641559592960 }, some { target := 36, numerator := 2915022382545774597510266880 }, some { target := 37, numerator := 2928622798016439175725711360 }, some { target := 38, numerator := 140537626530200641559592960 }, some { target := 39, numerator := 3363836093077705678619934720 }, some { target := 40, numerator := 140537626530200641559592960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 45, numerator := 134389105369504363491360768 }, some { target := 46, numerator := 3216668264005556055180312576 }, some { target := 47, numerator := 2405998499357255539925975040 }, some { target := 48, numerator := 2791825285740671293175365632 }, some { target := 49, numerator := 134389105369504363491360768 }, some { target := 50, numerator := 2787490153309396958869192704 }, some { target := 51, numerator := 2800495550603219961787711488 }, some { target := 52, numerator := 134389105369504363491360768 }, some { target := 53, numerator := 3216668264005556055180312576 }, some { target := 54, numerator := 134389105369504363491360768 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 76, numerator := 4391800829068770048737280 }, some { target := 77, numerator := 105119877908678302456872960 }, some { target := 78, numerator := 78627401939779592808038400 }, some { target := 79, numerator := 91236120449041545528606720 }, some { target := 80, numerator := 4391800829068770048737280 }, some { target := 81, numerator := 91094449454555456172195840 }, some { target := 82, numerator := 91519462438013724241428480 }, some { target := 83, numerator := 4391800829068770048737280 }, some { target := 84, numerator := 105119877908678302456872960 }, some { target := 85, numerator := 4391800829068770048737280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 90, numerator := 137902546032759379530350592 }, some { target := 91, numerator := 3300764166332498697145810944 }, some { target := 92, numerator := 2468900420909079214172405760 }, some { target := 93, numerator := 2864814182099904529598251008 }, some { target := 94, numerator := 137902546032759379530350592 }, some { target := 95, numerator := 2860365712873041323806949376 }, some { target := 96, numerator := 2873711120553630941180854272 }, some { target := 97, numerator := 137902546032759379530350592 }, some { target := 98, numerator := 3300764166332498697145810944 }, some { target := 99, numerator := 137902546032759379530350592 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 116, numerator := 4391800829068770048737280 }, some { target := 117, numerator := 105119877908678302456872960 }, some { target := 118, numerator := 78627401939779592808038400 }, some { target := 119, numerator := 91236120449041545528606720 }, some { target := 120, numerator := 4391800829068770048737280 }, some { target := 121, numerator := 91094449454555456172195840 }, some { target := 122, numerator := 91519462438013724241428480 }, some { target := 123, numerator := 4391800829068770048737280 }, some { target := 124, numerator := 105119877908678302456872960 }, some { target := 125, numerator := 4391800829068770048737280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 171, numerator := 134389105369504363491360768 }, some { target := 172, numerator := 3216668264005556055180312576 }, some { target := 173, numerator := 2405998499357255539925975040 }, some { target := 174, numerator := 2791825285740671293175365632 }, some { target := 175, numerator := 134389105369504363491360768 }, some { target := 176, numerator := 2787490153309396958869192704 }, some { target := 177, numerator := 2800495550603219961787711488 }, some { target := 178, numerator := 134389105369504363491360768 }, some { target := 179, numerator := 3216668264005556055180312576 }, some { target := 180, numerator := 134389105369504363491360768 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 185, numerator := 76417334425796598848028672 }, some { target := 186, numerator := 1829085875611002462749589504 }, some { target := 187, numerator := 1368116793752164914859868160 }, some { target := 188, numerator := 1587508495813322892197756928 }, some { target := 189, numerator := 76417334425796598848028672 }, some { target := 190, numerator := 1585043420509264937396207616 }, some { target := 191, numerator := 1592438646421438801800855552 }, some { target := 192, numerator := 76417334425796598848028672 }, some { target := 193, numerator := 1829085875611002462749589504 }, some { target := 194, numerator := 76417334425796598848028672 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 216, numerator := 137902546032759379530350592 }, some { target := 217, numerator := 3300764166332498697145810944 }, some { target := 218, numerator := 2468900420909079214172405760 }, some { target := 219, numerator := 2864814182099904529598251008 }, some { target := 220, numerator := 137902546032759379530350592 }, some { target := 221, numerator := 2860365712873041323806949376 }, some { target := 222, numerator := 2873711120553630941180854272 }, some { target := 223, numerator := 137902546032759379530350592 }, some { target := 224, numerator := 3300764166332498697145810944 }, some { target := 225, numerator := 137902546032759379530350592 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 230, numerator := 2152860766409511077891014656 }, some { target := 231, numerator := 51529764150834103864359124992 }, some { target := 232, numerator := 38543152430879956394500423680 }, some { target := 233, numerator := 44723946244120165618123014144 }, some { target := 234, numerator := 2152860766409511077891014656 }, some { target := 235, numerator := 44654499122623084615610400768 }, some { target := 236, numerator := 44862840487114327623148240896 }, some { target := 237, numerator := 2152860766409511077891014656 }, some { target := 238, numerator := 51529764150834103864359124992 }, some { target := 239, numerator := 2152860766409511077891014656 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 256, numerator := 84322575918120384935755776 }, some { target := 257, numerator := 2018301655846623407171960832 }, some { target := 258, numerator := 1509646117243768181914337280 }, some { target := 259, numerator := 1751733512621597674149249024 }, some { target := 260, numerator := 84322575918120384935755776 }, some { target := 261, numerator := 1749013429527464758506160128 }, some { target := 262, numerator := 1757173678809863505435426816 }, some { target := 263, numerator := 84322575918120384935755776 }, some { target := 264, numerator := 2018301655846623407171960832 }, some { target := 265, numerator := 84322575918120384935755776 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 305, numerator := 140537626530200641559592960 }, some { target := 306, numerator := 3363836093077705678619934720 }, some { target := 307, numerator := 2516076862072946969857228800 }, some { target := 308, numerator := 2919555854369329456915415040 }, some { target := 309, numerator := 140537626530200641559592960 }, some { target := 310, numerator := 2915022382545774597510266880 }, some { target := 311, numerator := 2928622798016439175725711360 }, some { target := 312, numerator := 140537626530200641559592960 }, some { target := 313, numerator := 3363836093077705678619934720 }, some { target := 314, numerator := 140537626530200641559592960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 331, numerator := 134389105369504363491360768 }, some { target := 332, numerator := 3216668264005556055180312576 }, some { target := 333, numerator := 2405998499357255539925975040 }, some { target := 334, numerator := 2791825285740671293175365632 }, some { target := 335, numerator := 134389105369504363491360768 }, some { target := 336, numerator := 2787490153309396958869192704 }, some { target := 337, numerator := 2800495550603219961787711488 }, some { target := 338, numerator := 134389105369504363491360768 }, some { target := 339, numerator := 3216668264005556055180312576 }, some { target := 340, numerator := 134389105369504363491360768 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 432, numerator := 4391800829068770048737280 }, some { target := 433, numerator := 105119877908678302456872960 }, some { target := 434, numerator := 78627401939779592808038400 }, some { target := 435, numerator := 91236120449041545528606720 }, some { target := 436, numerator := 4391800829068770048737280 }, some { target := 437, numerator := 91094449454555456172195840 }, some { target := 438, numerator := 91519462438013724241428480 }, some { target := 439, numerator := 4391800829068770048737280 }, some { target := 440, numerator := 105119877908678302456872960 }, some { target := 441, numerator := 4391800829068770048737280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 446, numerator := 84322575918120384935755776 }, some { target := 447, numerator := 2018301655846623407171960832 }, some { target := 448, numerator := 1509646117243768181914337280 }, some { target := 449, numerator := 1751733512621597674149249024 }, some { target := 450, numerator := 84322575918120384935755776 }, some { target := 451, numerator := 1749013429527464758506160128 }, some { target := 452, numerator := 1757173678809863505435426816 }, some { target := 453, numerator := 84322575918120384935755776 }, some { target := 454, numerator := 2018301655846623407171960832 }, some { target := 455, numerator := 84322575918120384935755776 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 472, numerator := 4391800829068770048737280 }, some { target := 473, numerator := 105119877908678302456872960 }, some { target := 474, numerator := 78627401939779592808038400 }, some { target := 475, numerator := 91236120449041545528606720 }, some { target := 476, numerator := 4391800829068770048737280 }, some { target := 477, numerator := 91094449454555456172195840 }, some { target := 478, numerator := 91519462438013724241428480 }, some { target := 479, numerator := 4391800829068770048737280 }, some { target := 480, numerator := 105119877908678302456872960 }, some { target := 481, numerator := 4391800829068770048737280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 521, numerator := 135267465535318117501108224 }, some { target := 522, numerator := 3237692239587291715671687168 }, some { target := 523, numerator := 2421723979745211458487582720 }, some { target := 524, numerator := 2810072509830479602281086976 }, some { target := 525, numerator := 135267465535318117501108224 }, some { target := 526, numerator := 2805709043200308050103631872 }, some { target := 527, numerator := 2818799443090822706635997184 }, some { target := 528, numerator := 135267465535318117501108224 }, some { target := 529, numerator := 3237692239587291715671687168 }, some { target := 530, numerator := 135267465535318117501108224 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 547, numerator := 76417334425796598848028672 }, some { target := 548, numerator := 1829085875611002462749589504 }, some { target := 549, numerator := 1368116793752164914859868160 }, some { target := 550, numerator := 1587508495813322892197756928 }, some { target := 551, numerator := 76417334425796598848028672 }, some { target := 552, numerator := 1585043420509264937396207616 }, some { target := 553, numerator := 1592438646421438801800855552 }, some { target := 554, numerator := 76417334425796598848028672 }, some { target := 555, numerator := 1829085875611002462749589504 }, some { target := 556, numerator := 76417334425796598848028672 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 643, numerator := 5270160994882524058484736 }, some { target := 644, numerator := 126143853490413962948247552 }, some { target := 645, numerator := 94352882327735511369646080 }, some { target := 646, numerator := 109483344538849854634328064 }, some { target := 647, numerator := 5270160994882524058484736 }, some { target := 648, numerator := 109313339345466547406635008 }, some { target := 649, numerator := 109823354925616469089714176 }, some { target := 650, numerator := 5270160994882524058484736 }, some { target := 651, numerator := 126143853490413962948247552 }, some { target := 652, numerator := 5270160994882524058484736 }]

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

end Slot4

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3.Parent3
