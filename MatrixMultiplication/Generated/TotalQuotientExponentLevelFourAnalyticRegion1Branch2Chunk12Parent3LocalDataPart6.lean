import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk12Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 6, for region 1, branch 2,
parent 53; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot22

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨22, 36, #[140737521909760, 0, 140737454800896, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[24086361145344, 0, 233302254419968, 0, 0, 0, 0, 24086361145344, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 2]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        1 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes_eq

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
  [some { target := 4, numerator := 122034772059092754041237667840 }, some { target := 6, numerator := 1182037721148959335215771156480 }, some { target := 11, numerator := 122034772059092754041237667840 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 126, numerator := 122034713868392717161347416064 }, some { target := 128, numerator := 1182037157509585875746640887808 }, some { target := 133, numerator := 122034713868392717161347416064 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left2.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left2.routed_eq]
  rfl

end Slot22

namespace Slot23

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨23, 1, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total0.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        0 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total0.codes_eq

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
  [some { target := 0, numerator := 19807040628566084398385987584 }, some { target := 1, numerator := 19807040628566084398385987584 }, some { target := 2, numerator := 19807040628566084398385987584 }, some { target := 3, numerator := 19807040628566084398385987584 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq]
  rfl

end Slot23

namespace Slot24

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨24, 70, #[2199023255552, 2611340115968, 1992864825344, 20547123544064, 2473901162496, 1992864825344, 2473901162496, 2473901162496, 105965433126912, 2473901162496, 20547123544064, 105965433126912, 2199023255552, 2473901162496, 2473901162496, 2611340115968, 0, 0, 0], #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 56, numerator := 63468605529768031672074240 }, some { target := 57, numerator := 1692496147460480844588646400 }, some { target := 58, numerator := 1618449441009084807637893120 }, some { target := 59, numerator := 52890504608140026393395200 }, some { target := 60, numerator := 1660761844695596828752609280 }, some { target := 61, numerator := 52890504608140026393395200 }, some { target := 62, numerator := 1618449441009084807637893120 }, some { target := 63, numerator := 920294780181636459245076480 }, some { target := 64, numerator := 1660761844695596828752609280 }, some { target := 65, numerator := 25926925358910240938042327040 }, some { target := 66, numerator := 1015497688476288506753187840 }, some { target := 67, numerator := 1692496147460480844588646400 }, some { target := 68, numerator := 1618449441009084807637893120 }, some { target := 69, numerator := 52890504608140026393395200 }, some { target := 70, numerator := 1015497688476288506753187840 }, some { target := 71, numerator := 52890504608140026393395200 }, some { target := 72, numerator := 1629027541930712812916572160 }, some { target := 73, numerator := 920294780181636459245076480 }, some { target := 74, numerator := 63468605529768031672074240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 91, numerator := 75368969066599537610588160 }, some { target := 92, numerator := 2009839175109321002949017600 }, some { target := 93, numerator := 1921908711198288209069998080 }, some { target := 94, numerator := 62807474222166281342156800 }, some { target := 95, numerator := 1972154690576021234143723520 }, some { target := 96, numerator := 62807474222166281342156800 }, some { target := 97, numerator := 1921908711198288209069998080 }, some { target := 98, numerator := 1092850051465693295353528320 }, some { target := 99, numerator := 1972154690576021234143723520 }, some { target := 100, numerator := 30788223863705911113925263360 }, some { target := 101, numerator := 1205903505065592601769410560 }, some { target := 102, numerator := 2009839175109321002949017600 }, some { target := 103, numerator := 1921908711198288209069998080 }, some { target := 104, numerator := 62807474222166281342156800 }, some { target := 105, numerator := 1205903505065592601769410560 }, some { target := 106, numerator := 62807474222166281342156800 }, some { target := 107, numerator := 1934470206042721465338429440 }, some { target := 108, numerator := 1092850051465693295353528320 }, some { target := 109, numerator := 75368969066599537610588160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 152, numerator := 57518423761352278702817280 }, some { target := 153, numerator := 1533824633636060765408460800 }, some { target := 154, numerator := 1466719805914483106921840640 }, some { target := 155, numerator := 47932019801126898919014400 }, some { target := 156, numerator := 1505065421755384626057052160 }, some { target := 157, numerator := 47932019801126898919014400 }, some { target := 158, numerator := 1466719805914483106921840640 }, some { target := 159, numerator := 834017144539608041190850560 }, some { target := 160, numerator := 1505065421755384626057052160 }, some { target := 161, numerator := 23496276106512405850100858880 }, some { target := 162, numerator := 920294780181636459245076480 }, some { target := 163, numerator := 1533824633636060765408460800 }, some { target := 164, numerator := 1466719805914483106921840640 }, some { target := 165, numerator := 47932019801126898919014400 }, some { target := 166, numerator := 920294780181636459245076480 }, some { target := 167, numerator := 47932019801126898919014400 }, some { target := 168, numerator := 1476306209874708486705643520 }, some { target := 169, numerator := 834017144539608041190850560 }, some { target := 170, numerator := 57518423761352278702817280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 187, numerator := 593034782918770045935943680 }, some { target := 188, numerator := 15814260877833867891625164800 }, some { target := 189, numerator := 15122386964428636171366563840 }, some { target := 190, numerator := 494195652432308371613286400 }, some { target := 191, numerator := 15517743486374482868657192960 }, some { target := 192, numerator := 494195652432308371613286400 }, some { target := 193, numerator := 15122386964428636171366563840 }, some { target := 194, numerator := 8599004352322165666071183360 }, some { target := 195, numerator := 15517743486374482868657192960 }, some { target := 196, numerator := 242254708822317563764832993280 }, some { target := 197, numerator := 9488556526700320734975098880 }, some { target := 198, numerator := 15814260877833867891625164800 }, some { target := 199, numerator := 15122386964428636171366563840 }, some { target := 200, numerator := 494195652432308371613286400 }, some { target := 201, numerator := 9488556526700320734975098880 }, some { target := 202, numerator := 494195652432308371613286400 }, some { target := 203, numerator := 15221226094915097845689221120 }, some { target := 204, numerator := 8599004352322165666071183360 }, some { target := 205, numerator := 593034782918770045935943680 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 222, numerator := 71402181220989035631083520 }, some { target := 223, numerator := 1904058165893040950162227200 }, some { target := 224, numerator := 1820755621135220408592629760 }, some { target := 225, numerator := 59501817684157529692569600 }, some { target := 226, numerator := 1868357075282546432346685440 }, some { target := 227, numerator := 59501817684157529692569600 }, some { target := 228, numerator := 1820755621135220408592629760 }, some { target := 229, numerator := 1035331627704341016650711040 }, some { target := 230, numerator := 1868357075282546432346685440 }, some { target := 231, numerator := 29167791028774021055297617920 }, some { target := 232, numerator := 1142434899535824570097336320 }, some { target := 233, numerator := 1904058165893040950162227200 }, some { target := 234, numerator := 1820755621135220408592629760 }, some { target := 235, numerator := 59501817684157529692569600 }, some { target := 236, numerator := 1142434899535824570097336320 }, some { target := 237, numerator := 59501817684157529692569600 }, some { target := 238, numerator := 1832655984672051914531143680 }, some { target := 239, numerator := 1035331627704341016650711040 }, some { target := 240, numerator := 71402181220989035631083520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 283, numerator := 57518423761352278702817280 }, some { target := 284, numerator := 1533824633636060765408460800 }, some { target := 285, numerator := 1466719805914483106921840640 }, some { target := 286, numerator := 47932019801126898919014400 }, some { target := 287, numerator := 1505065421755384626057052160 }, some { target := 288, numerator := 47932019801126898919014400 }, some { target := 289, numerator := 1466719805914483106921840640 }, some { target := 290, numerator := 834017144539608041190850560 }, some { target := 291, numerator := 1505065421755384626057052160 }, some { target := 292, numerator := 23496276106512405850100858880 }, some { target := 293, numerator := 920294780181636459245076480 }, some { target := 294, numerator := 1533824633636060765408460800 }, some { target := 295, numerator := 1466719805914483106921840640 }, some { target := 296, numerator := 47932019801126898919014400 }, some { target := 297, numerator := 920294780181636459245076480 }, some { target := 298, numerator := 47932019801126898919014400 }, some { target := 299, numerator := 1476306209874708486705643520 }, some { target := 300, numerator := 834017144539608041190850560 }, some { target := 301, numerator := 57518423761352278702817280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 318, numerator := 71402181220989035631083520 }, some { target := 319, numerator := 1904058165893040950162227200 }, some { target := 320, numerator := 1820755621135220408592629760 }, some { target := 321, numerator := 59501817684157529692569600 }, some { target := 322, numerator := 1868357075282546432346685440 }, some { target := 323, numerator := 59501817684157529692569600 }, some { target := 324, numerator := 1820755621135220408592629760 }, some { target := 325, numerator := 1035331627704341016650711040 }, some { target := 326, numerator := 1868357075282546432346685440 }, some { target := 327, numerator := 29167791028774021055297617920 }, some { target := 328, numerator := 1142434899535824570097336320 }, some { target := 329, numerator := 1904058165893040950162227200 }, some { target := 330, numerator := 1820755621135220408592629760 }, some { target := 331, numerator := 59501817684157529692569600 }, some { target := 332, numerator := 1142434899535824570097336320 }, some { target := 333, numerator := 59501817684157529692569600 }, some { target := 334, numerator := 1832655984672051914531143680 }, some { target := 335, numerator := 1035331627704341016650711040 }, some { target := 336, numerator := 71402181220989035631083520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 419, numerator := 71402181220989035631083520 }, some { target := 420, numerator := 1904058165893040950162227200 }, some { target := 421, numerator := 1820755621135220408592629760 }, some { target := 422, numerator := 59501817684157529692569600 }, some { target := 423, numerator := 1868357075282546432346685440 }, some { target := 424, numerator := 59501817684157529692569600 }, some { target := 425, numerator := 1820755621135220408592629760 }, some { target := 426, numerator := 1035331627704341016650711040 }, some { target := 427, numerator := 1868357075282546432346685440 }, some { target := 428, numerator := 29167791028774021055297617920 }, some { target := 429, numerator := 1142434899535824570097336320 }, some { target := 430, numerator := 1904058165893040950162227200 }, some { target := 431, numerator := 1820755621135220408592629760 }, some { target := 432, numerator := 59501817684157529692569600 }, some { target := 433, numerator := 1142434899535824570097336320 }, some { target := 434, numerator := 59501817684157529692569600 }, some { target := 435, numerator := 1832655984672051914531143680 }, some { target := 436, numerator := 1035331627704341016650711040 }, some { target := 437, numerator := 71402181220989035631083520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 454, numerator := 3058393428965697026198077440 }, some { target := 455, numerator := 81557158105751920698615398400 }, some { target := 456, numerator := 77989032438625274168050974720 }, some { target := 457, numerator := 2548661190804747521831731200 }, some { target := 458, numerator := 80027961391269072185516359680 }, some { target := 459, numerator := 2548661190804747521831731200 }, some { target := 460, numerator := 77989032438625274168050974720 }, some { target := 461, numerator := 44346704720002606879872122880 }, some { target := 462, numerator := 80027961391269072185516359680 }, some { target := 463, numerator := 1249353715732487235201914634240 }, some { target := 464, numerator := 48934294863451152419169239040 }, some { target := 465, numerator := 81557158105751920698615398400 }, some { target := 466, numerator := 77989032438625274168050974720 }, some { target := 467, numerator := 2548661190804747521831731200 }, some { target := 468, numerator := 48934294863451152419169239040 }, some { target := 469, numerator := 2548661190804747521831731200 }, some { target := 470, numerator := 78498764676786223672417320960 }, some { target := 471, numerator := 44346704720002606879872122880 }, some { target := 472, numerator := 3058393428965697026198077440 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 489, numerator := 71402181220989035631083520 }, some { target := 490, numerator := 1904058165893040950162227200 }, some { target := 491, numerator := 1820755621135220408592629760 }, some { target := 492, numerator := 59501817684157529692569600 }, some { target := 493, numerator := 1868357075282546432346685440 }, some { target := 494, numerator := 59501817684157529692569600 }, some { target := 495, numerator := 1820755621135220408592629760 }, some { target := 496, numerator := 1035331627704341016650711040 }, some { target := 497, numerator := 1868357075282546432346685440 }, some { target := 498, numerator := 29167791028774021055297617920 }, some { target := 499, numerator := 1142434899535824570097336320 }, some { target := 500, numerator := 1904058165893040950162227200 }, some { target := 501, numerator := 1820755621135220408592629760 }, some { target := 502, numerator := 59501817684157529692569600 }, some { target := 503, numerator := 1142434899535824570097336320 }, some { target := 504, numerator := 59501817684157529692569600 }, some { target := 505, numerator := 1832655984672051914531143680 }, some { target := 506, numerator := 1035331627704341016650711040 }, some { target := 507, numerator := 71402181220989035631083520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 550, numerator := 593034782918770045935943680 }, some { target := 551, numerator := 15814260877833867891625164800 }, some { target := 552, numerator := 15122386964428636171366563840 }, some { target := 553, numerator := 494195652432308371613286400 }, some { target := 554, numerator := 15517743486374482868657192960 }, some { target := 555, numerator := 494195652432308371613286400 }, some { target := 556, numerator := 15122386964428636171366563840 }, some { target := 557, numerator := 8599004352322165666071183360 }, some { target := 558, numerator := 15517743486374482868657192960 }, some { target := 559, numerator := 242254708822317563764832993280 }, some { target := 560, numerator := 9488556526700320734975098880 }, some { target := 561, numerator := 15814260877833867891625164800 }, some { target := 562, numerator := 15122386964428636171366563840 }, some { target := 563, numerator := 494195652432308371613286400 }, some { target := 564, numerator := 9488556526700320734975098880 }, some { target := 565, numerator := 494195652432308371613286400 }, some { target := 566, numerator := 15221226094915097845689221120 }, some { target := 567, numerator := 8599004352322165666071183360 }, some { target := 568, numerator := 593034782918770045935943680 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 585, numerator := 3058393428965697026198077440 }, some { target := 586, numerator := 81557158105751920698615398400 }, some { target := 587, numerator := 77989032438625274168050974720 }, some { target := 588, numerator := 2548661190804747521831731200 }, some { target := 589, numerator := 80027961391269072185516359680 }, some { target := 590, numerator := 2548661190804747521831731200 }, some { target := 591, numerator := 77989032438625274168050974720 }, some { target := 592, numerator := 44346704720002606879872122880 }, some { target := 593, numerator := 80027961391269072185516359680 }, some { target := 594, numerator := 1249353715732487235201914634240 }, some { target := 595, numerator := 48934294863451152419169239040 }, some { target := 596, numerator := 81557158105751920698615398400 }, some { target := 597, numerator := 77989032438625274168050974720 }, some { target := 598, numerator := 2548661190804747521831731200 }, some { target := 599, numerator := 48934294863451152419169239040 }, some { target := 600, numerator := 2548661190804747521831731200 }, some { target := 601, numerator := 78498764676786223672417320960 }, some { target := 602, numerator := 44346704720002606879872122880 }, some { target := 603, numerator := 3058393428965697026198077440 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 660, numerator := 63468605529768031672074240 }, some { target := 661, numerator := 1692496147460480844588646400 }, some { target := 662, numerator := 1618449441009084807637893120 }, some { target := 663, numerator := 52890504608140026393395200 }, some { target := 664, numerator := 1660761844695596828752609280 }, some { target := 665, numerator := 52890504608140026393395200 }, some { target := 666, numerator := 1618449441009084807637893120 }, some { target := 667, numerator := 920294780181636459245076480 }, some { target := 668, numerator := 1660761844695596828752609280 }, some { target := 669, numerator := 25926925358910240938042327040 }, some { target := 670, numerator := 1015497688476288506753187840 }, some { target := 671, numerator := 1692496147460480844588646400 }, some { target := 672, numerator := 1618449441009084807637893120 }, some { target := 673, numerator := 52890504608140026393395200 }, some { target := 674, numerator := 1015497688476288506753187840 }, some { target := 675, numerator := 52890504608140026393395200 }, some { target := 676, numerator := 1629027541930712812916572160 }, some { target := 677, numerator := 920294780181636459245076480 }, some { target := 678, numerator := 63468605529768031672074240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 766, numerator := 71402181220989035631083520 }, some { target := 767, numerator := 1904058165893040950162227200 }, some { target := 768, numerator := 1820755621135220408592629760 }, some { target := 769, numerator := 59501817684157529692569600 }, some { target := 770, numerator := 1868357075282546432346685440 }, some { target := 771, numerator := 59501817684157529692569600 }, some { target := 772, numerator := 1820755621135220408592629760 }, some { target := 773, numerator := 1035331627704341016650711040 }, some { target := 774, numerator := 1868357075282546432346685440 }, some { target := 775, numerator := 29167791028774021055297617920 }, some { target := 776, numerator := 1142434899535824570097336320 }, some { target := 777, numerator := 1904058165893040950162227200 }, some { target := 778, numerator := 1820755621135220408592629760 }, some { target := 779, numerator := 59501817684157529692569600 }, some { target := 780, numerator := 1142434899535824570097336320 }, some { target := 781, numerator := 59501817684157529692569600 }, some { target := 782, numerator := 1832655984672051914531143680 }, some { target := 783, numerator := 1035331627704341016650711040 }, some { target := 784, numerator := 71402181220989035631083520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 801, numerator := 71402181220989035631083520 }, some { target := 802, numerator := 1904058165893040950162227200 }, some { target := 803, numerator := 1820755621135220408592629760 }, some { target := 804, numerator := 59501817684157529692569600 }, some { target := 805, numerator := 1868357075282546432346685440 }, some { target := 806, numerator := 59501817684157529692569600 }, some { target := 807, numerator := 1820755621135220408592629760 }, some { target := 808, numerator := 1035331627704341016650711040 }, some { target := 809, numerator := 1868357075282546432346685440 }, some { target := 810, numerator := 29167791028774021055297617920 }, some { target := 811, numerator := 1142434899535824570097336320 }, some { target := 812, numerator := 1904058165893040950162227200 }, some { target := 813, numerator := 1820755621135220408592629760 }, some { target := 814, numerator := 59501817684157529692569600 }, some { target := 815, numerator := 1142434899535824570097336320 }, some { target := 816, numerator := 59501817684157529692569600 }, some { target := 817, numerator := 1832655984672051914531143680 }, some { target := 818, numerator := 1035331627704341016650711040 }, some { target := 819, numerator := 71402181220989035631083520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 876, numerator := 75368969066599537610588160 }, some { target := 877, numerator := 2009839175109321002949017600 }, some { target := 878, numerator := 1921908711198288209069998080 }, some { target := 879, numerator := 62807474222166281342156800 }, some { target := 880, numerator := 1972154690576021234143723520 }, some { target := 881, numerator := 62807474222166281342156800 }, some { target := 882, numerator := 1921908711198288209069998080 }, some { target := 883, numerator := 1092850051465693295353528320 }, some { target := 884, numerator := 1972154690576021234143723520 }, some { target := 885, numerator := 30788223863705911113925263360 }, some { target := 886, numerator := 1205903505065592601769410560 }, some { target := 887, numerator := 2009839175109321002949017600 }, some { target := 888, numerator := 1921908711198288209069998080 }, some { target := 889, numerator := 62807474222166281342156800 }, some { target := 890, numerator := 1205903505065592601769410560 }, some { target := 891, numerator := 62807474222166281342156800 }, some { target := 892, numerator := 1934470206042721465338429440 }, some { target := 893, numerator := 1092850051465693295353528320 }, some { target := 894, numerator := 75368969066599537610588160 }]

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

end Slot24

namespace Slot25

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨25, 56, #[50466754920448, 0, 0, 180541483646976, 0, 50466738143232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

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
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 14, numerator := 6797376021766394138727546880 }, some { target := 15, numerator := 6991586765245433971262619648 }, some { target := 16, numerator := 6797376021766394138727546880 }, some { target := 17, numerator := 6020533047850234808587255808 }, some { target := 18, numerator := 281799788788086797008390586368 }, some { target := 19, numerator := 76713243674220733851353743360 }, some { target := 20, numerator := 6991586765245433971262619648 }, some { target := 21, numerator := 281799788788086797008390586368 }, some { target := 22, numerator := 6797376021766394138727546880 }, some { target := 23, numerator := 6797376021766394138727546880 }, some { target := 24, numerator := 5826322304371194976052183040 }, some { target := 25, numerator := 6797376021766394138727546880 }, some { target := 26, numerator := 76713243674220733851353743360 }, some { target := 27, numerator := 5826322304371194976052183040 }, some { target := 28, numerator := 6797376021766394138727546880 }, some { target := 29, numerator := 6020533047850234808587255808 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 136, numerator := 24317163919308131670750658560 }, some { target := 137, numerator := 25011940031288364004200677376 }, some { target := 138, numerator := 24317163919308131670750658560 }, some { target := 139, numerator := 21538059471387202336950583296 }, some { target := 140, numerator := 1008120138483317115835977302016 }, some { target := 141, numerator := 274436564232191771712757432320 }, some { target := 142, numerator := 25011940031288364004200677376 }, some { target := 143, numerator := 1008120138483317115835977302016 }, some { target := 144, numerator := 24317163919308131670750658560 }, some { target := 145, numerator := 24317163919308131670750658560 }, some { target := 146, numerator := 20843283359406970003500564480 }, some { target := 147, numerator := 24317163919308131670750658560 }, some { target := 148, numerator := 274436564232191771712757432320 }, some { target := 149, numerator := 20843283359406970003500564480 }, some { target := 150, numerator := 24317163919308131670750658560 }, some { target := 151, numerator := 21538059471387202336950583296 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 6797373762040245109307473920 }, some { target := 268, numerator := 6991584440955680683859116032 }, some { target := 269, numerator := 6797373762040245109307473920 }, some { target := 270, numerator := 6020531046378502811100905472 }, some { target := 271, numerator := 281799695106297018674432704512 }, some { target := 272, numerator := 76713218171597051947898634240 }, some { target := 273, numerator := 6991584440955680683859116032 }, some { target := 274, numerator := 281799695106297018674432704512 }, some { target := 275, numerator := 6797373762040245109307473920 }, some { target := 276, numerator := 6797373762040245109307473920 }, some { target := 277, numerator := 5826320367463067236549263360 }, some { target := 278, numerator := 6797373762040245109307473920 }, some { target := 279, numerator := 76713218171597051947898634240 }, some { target := 280, numerator := 5826320367463067236549263360 }, some { target := 281, numerator := 6797373762040245109307473920 }, some { target := 282, numerator := 6020531046378502811100905472 }]

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

end Slot25

namespace Slot26

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨26, 7, #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 2]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        1 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes_eq

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
  [some { target := 4, numerator := 1692496147460480844588646400 }, some { target := 5, numerator := 33917622795108036125556473856 }, some { target := 6, numerator := 56935570400570575611962064896 }, some { target := 7, numerator := 54633775640024321663321505792 }, some { target := 8, numerator := 1692496147460480844588646400 }, some { target := 9, numerator := 54633775640024321663321505792 }, some { target := 10, numerator := 36490216939247967009331216384 }, some { target := 11, numerator := 1760195993358900078372192256 }, some { target := 12, numerator := 33917622795108036125556473856 }, some { target := 13, numerator := 1624796301562061610805100544 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 126, numerator := 1692496147460480844588646400 }, some { target := 127, numerator := 33917622795108036125556473856 }, some { target := 128, numerator := 56935570400570575611962064896 }, some { target := 129, numerator := 54633775640024321663321505792 }, some { target := 130, numerator := 1692496147460480844588646400 }, some { target := 131, numerator := 54633775640024321663321505792 }, some { target := 132, numerator := 36490216939247967009331216384 }, some { target := 133, numerator := 1760195993358900078372192256 }, some { target := 134, numerator := 33917622795108036125556473856 }, some { target := 135, numerator := 1624796301562061610805100544 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left2.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left2.routed_eq]
  rfl

end Slot26

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12.Parent3
