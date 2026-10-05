import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk7Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 1, for region 1, branch 2,
parent 30; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot3

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨3, 245, #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0], #[147035521024, 23473808211968, 0, 234233306021888, 0, 0, 0, 0, 0, 0, 0, 23473808211968, 0, 0, 0, 0, 0, 0, 147018743808]⟩

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
  [some { target := 121, numerator := 86643549869160539147468800 }, some { target := 122, numerator := 13832399533584690783558041600 }, some { target := 124, numerator := 138026546170521322127989145600 }, some { target := 132, numerator := 13832399533584690783558041600 }, some { target := 139, numerator := 86633663567258535434649600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 196, numerator := 89119079865422268837396480 }, some { target := 197, numerator := 14227610948829967663088271360 }, some { target := 199, numerator := 141970161775393359903074549760 }, some { target := 207, numerator := 14227610948829967663088271360 }, some { target := 214, numerator := 89108911097751636447068160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 231, numerator := 86643549869160539147468800 }, some { target := 232, numerator := 13832399533584690783558041600 }, some { target := 234, numerator := 138026546170521322127989145600 }, some { target := 242, numerator := 13832399533584690783558041600 }, some { target := 249, numerator := 86633663567258535434649600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 337, numerator := 76741429884113620387758080 }, some { target := 338, numerator := 12251553872603583265437122560 }, some { target := 340, numerator := 122252083751033171027647528960 }, some { target := 348, numerator := 12251553872603583265437122560 }, some { target := 355, numerator := 76732673445286131384975360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 412, numerator := 3591994024575769780085063680 }, some { target := 413, numerator := 573451763520896752198363381760 }, some { target := 415, numerator := 5722186242669326811648921436160 }, some { target := 423, numerator := 573451763520896752198363381760 }, some { target := 430, numerator := 3591584166745489569019330560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 447, numerator := 977834348523383227521433600 }, some { target := 448, numerator := 156108509021884367414440755200 }, some { target := 450, numerator := 1557728163924454921158734643200 }, some { target := 458, numerator := 156108509021884367414440755200 }, some { target := 465, numerator := 977722774544774899905331200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 508, numerator := 89119079865422268837396480 }, some { target := 509, numerator := 14227610948829967663088271360 }, some { target := 511, numerator := 141970161775393359903074549760 }, some { target := 519, numerator := 14227610948829967663088271360 }, some { target := 526, numerator := 89108911097751636447068160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 543, numerator := 3591994024575769780085063680 }, some { target := 544, numerator := 573451763520896752198363381760 }, some { target := 546, numerator := 5722186242669326811648921436160 }, some { target := 554, numerator := 573451763520896752198363381760 }, some { target := 561, numerator := 3591584166745489569019330560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 578, numerator := 86643549869160539147468800 }, some { target := 579, numerator := 13832399533584690783558041600 }, some { target := 581, numerator := 138026546170521322127989145600 }, some { target := 589, numerator := 13832399533584690783558041600 }, some { target := 596, numerator := 86633663567258535434649600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 679, numerator := 86643549869160539147468800 }, some { target := 680, numerator := 13832399533584690783558041600 }, some { target := 682, numerator := 138026546170521322127989145600 }, some { target := 690, numerator := 13832399533584690783558041600 }, some { target := 697, numerator := 86633663567258535434649600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 714, numerator := 74265899887851890697830400 }, some { target := 715, numerator := 11856342457358306385906892800 }, some { target := 717, numerator := 118308468146161133252562124800 }, some { target := 725, numerator := 11856342457358306385906892800 }, some { target := 732, numerator := 74257425914793030372556800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 775, numerator := 86643549869160539147468800 }, some { target := 776, numerator := 13832399533584690783558041600 }, some { target := 778, numerator := 138026546170521322127989145600 }, some { target := 786, numerator := 13832399533584690783558041600 }, some { target := 793, numerator := 86633663567258535434649600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 810, numerator := 977834348523383227521433600 }, some { target := 811, numerator := 156108509021884367414440755200 }, some { target := 813, numerator := 1557728163924454921158734643200 }, some { target := 821, numerator := 156108509021884367414440755200 }, some { target := 828, numerator := 977722774544774899905331200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 845, numerator := 74265899887851890697830400 }, some { target := 846, numerator := 11856342457358306385906892800 }, some { target := 848, numerator := 118308468146161133252562124800 }, some { target := 856, numerator := 11856342457358306385906892800 }, some { target := 863, numerator := 74257425914793030372556800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 906, numerator := 86643549869160539147468800 }, some { target := 907, numerator := 13832399533584690783558041600 }, some { target := 909, numerator := 138026546170521322127989145600 }, some { target := 917, numerator := 13832399533584690783558041600 }, some { target := 924, numerator := 86633663567258535434649600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 941, numerator := 76741429884113620387758080 }, some { target := 942, numerator := 12251553872603583265437122560 }, some { target := 944, numerator := 122252083751033171027647528960 }, some { target := 952, numerator := 12251553872603583265437122560 }, some { target := 959, numerator := 76732673445286131384975360 }]

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
def data : BetaFourLocalSlotData := ⟨4, 56, #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416], #[3092376453120, 2405181685760, 2748779069440, 3229815406592, 38139309588480, 85761906966528, 2405181685760, 38139309588480, 2748779069440, 2680059592704, 2680059592704, 2680059592704, 85761906966528, 2680059592704, 3092376453120, 3229815406592, 0, 0, 0]⟩

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
  [some { target := 34, numerator := 71402181220989035631083520 }, some { target := 35, numerator := 55535029838547027713064960 }, some { target := 36, numerator := 63468605529768031672074240 }, some { target := 37, numerator := 74575611497477437214687232 }, some { target := 38, numerator := 880626901725531439450030080 }, some { target := 39, numerator := 1980220492528762588168716288 }, some { target := 40, numerator := 55535029838547027713064960 }, some { target := 41, numerator := 880626901725531439450030080 }, some { target := 42, numerator := 63468605529768031672074240 }, some { target := 43, numerator := 61881890391523830880272384 }, some { target := 44, numerator := 61881890391523830880272384 }, some { target := 45, numerator := 61881890391523830880272384 }, some { target := 46, numerator := 1980220492528762588168716288 }, some { target := 47, numerator := 61881890391523830880272384 }, some { target := 48, numerator := 71402181220989035631083520 }, some { target := 49, numerator := 74575611497477437214687232 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 79, numerator := 1904058165893040950162227200 }, some { target := 80, numerator := 1480934129027920739015065600 }, some { target := 81, numerator := 1692496147460480844588646400 }, some { target := 82, numerator := 1988682973266064992391659520 }, some { target := 83, numerator := 23483384046014171718667468800 }, some { target := 84, numerator := 52805879800767002351165767680 }, some { target := 85, numerator := 1480934129027920739015065600 }, some { target := 86, numerator := 23483384046014171718667468800 }, some { target := 87, numerator := 1692496147460480844588646400 }, some { target := 88, numerator := 1650183743773968823473930240 }, some { target := 89, numerator := 1650183743773968823473930240 }, some { target := 90, numerator := 1650183743773968823473930240 }, some { target := 91, numerator := 52805879800767002351165767680 }, some { target := 92, numerator := 1650183743773968823473930240 }, some { target := 93, numerator := 1904058165893040950162227200 }, some { target := 94, numerator := 1988682973266064992391659520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 105, numerator := 1820755621135220408592629760 }, some { target := 106, numerator := 1416143260882949206683156480 }, some { target := 107, numerator := 1618449441009084807637893120 }, some { target := 108, numerator := 1901678093185674648974524416 }, some { target := 109, numerator := 22455985994001051705975767040 }, some { target := 110, numerator := 50495622559483445998302265344 }, some { target := 111, numerator := 1416143260882949206683156480 }, some { target := 112, numerator := 22455985994001051705975767040 }, some { target := 113, numerator := 1618449441009084807637893120 }, some { target := 114, numerator := 1577988204983857687446945792 }, some { target := 115, numerator := 1577988204983857687446945792 }, some { target := 116, numerator := 1577988204983857687446945792 }, some { target := 117, numerator := 50495622559483445998302265344 }, some { target := 118, numerator := 1577988204983857687446945792 }, some { target := 119, numerator := 1820755621135220408592629760 }, some { target := 120, numerator := 1901678093185674648974524416 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 154, numerator := 59501817684157529692569600 }, some { target := 155, numerator := 46279191532122523094220800 }, some { target := 156, numerator := 52890504608140026393395200 }, some { target := 157, numerator := 62146342914564531012239360 }, some { target := 158, numerator := 733855751437942866208358400 }, some { target := 159, numerator := 1650183743773968823473930240 }, some { target := 160, numerator := 46279191532122523094220800 }, some { target := 161, numerator := 733855751437942866208358400 }, some { target := 162, numerator := 52890504608140026393395200 }, some { target := 163, numerator := 51568241992936525733560320 }, some { target := 164, numerator := 51568241992936525733560320 }, some { target := 165, numerator := 51568241992936525733560320 }, some { target := 166, numerator := 1650183743773968823473930240 }, some { target := 167, numerator := 51568241992936525733560320 }, some { target := 168, numerator := 59501817684157529692569600 }, some { target := 169, numerator := 62146342914564531012239360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 180, numerator := 1868357075282546432346685440 }, some { target := 181, numerator := 1453166614108647225158533120 }, some { target := 182, numerator := 1660761844695596828752609280 }, some { target := 183, numerator := 1951395167517326273784315904 }, some { target := 184, numerator := 23043070595151405998942453760 }, some { target := 185, numerator := 51815769554502621057081409536 }, some { target := 186, numerator := 1453166614108647225158533120 }, some { target := 187, numerator := 23043070595151405998942453760 }, some { target := 188, numerator := 1660761844695596828752609280 }, some { target := 189, numerator := 1619242798578206908033794048 }, some { target := 190, numerator := 1619242798578206908033794048 }, some { target := 191, numerator := 1619242798578206908033794048 }, some { target := 192, numerator := 51815769554502621057081409536 }, some { target := 193, numerator := 1619242798578206908033794048 }, some { target := 194, numerator := 1868357075282546432346685440 }, some { target := 195, numerator := 1951395167517326273784315904 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 215, numerator := 59501817684157529692569600 }, some { target := 216, numerator := 46279191532122523094220800 }, some { target := 217, numerator := 52890504608140026393395200 }, some { target := 218, numerator := 62146342914564531012239360 }, some { target := 219, numerator := 733855751437942866208358400 }, some { target := 220, numerator := 1650183743773968823473930240 }, some { target := 221, numerator := 46279191532122523094220800 }, some { target := 222, numerator := 733855751437942866208358400 }, some { target := 223, numerator := 52890504608140026393395200 }, some { target := 224, numerator := 51568241992936525733560320 }, some { target := 225, numerator := 51568241992936525733560320 }, some { target := 226, numerator := 51568241992936525733560320 }, some { target := 227, numerator := 1650183743773968823473930240 }, some { target := 228, numerator := 51568241992936525733560320 }, some { target := 229, numerator := 59501817684157529692569600 }, some { target := 230, numerator := 62146342914564531012239360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 295, numerator := 1820755621135220408592629760 }, some { target := 296, numerator := 1416143260882949206683156480 }, some { target := 297, numerator := 1618449441009084807637893120 }, some { target := 298, numerator := 1901678093185674648974524416 }, some { target := 299, numerator := 22455985994001051705975767040 }, some { target := 300, numerator := 50495622559483445998302265344 }, some { target := 301, numerator := 1416143260882949206683156480 }, some { target := 302, numerator := 22455985994001051705975767040 }, some { target := 303, numerator := 1618449441009084807637893120 }, some { target := 304, numerator := 1577988204983857687446945792 }, some { target := 305, numerator := 1577988204983857687446945792 }, some { target := 306, numerator := 1577988204983857687446945792 }, some { target := 307, numerator := 50495622559483445998302265344 }, some { target := 308, numerator := 1577988204983857687446945792 }, some { target := 309, numerator := 1820755621135220408592629760 }, some { target := 310, numerator := 1901678093185674648974524416 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 321, numerator := 1035331627704341016650711040 }, some { target := 322, numerator := 805257932658931901839441920 }, some { target := 323, numerator := 920294780181636459245076480 }, some { target := 324, numerator := 1081346366713422839612964864 }, some { target := 325, numerator := 12769090075020205872025436160 }, some { target := 326, numerator := 28713197141667057528446386176 }, some { target := 327, numerator := 805257932658931901839441920 }, some { target := 328, numerator := 12769090075020205872025436160 }, some { target := 329, numerator := 920294780181636459245076480 }, some { target := 330, numerator := 897287410677095547763949568 }, some { target := 331, numerator := 897287410677095547763949568 }, some { target := 332, numerator := 897287410677095547763949568 }, some { target := 333, numerator := 28713197141667057528446386176 }, some { target := 334, numerator := 897287410677095547763949568 }, some { target := 335, numerator := 1035331627704341016650711040 }, some { target := 336, numerator := 1081346366713422839612964864 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 370, numerator := 1868357075282546432346685440 }, some { target := 371, numerator := 1453166614108647225158533120 }, some { target := 372, numerator := 1660761844695596828752609280 }, some { target := 373, numerator := 1951395167517326273784315904 }, some { target := 374, numerator := 23043070595151405998942453760 }, some { target := 375, numerator := 51815769554502621057081409536 }, some { target := 376, numerator := 1453166614108647225158533120 }, some { target := 377, numerator := 23043070595151405998942453760 }, some { target := 378, numerator := 1660761844695596828752609280 }, some { target := 379, numerator := 1619242798578206908033794048 }, some { target := 380, numerator := 1619242798578206908033794048 }, some { target := 381, numerator := 1619242798578206908033794048 }, some { target := 382, numerator := 51815769554502621057081409536 }, some { target := 383, numerator := 1619242798578206908033794048 }, some { target := 384, numerator := 1868357075282546432346685440 }, some { target := 385, numerator := 1951395167517326273784315904 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 396, numerator := 29167791028774021055297617920 }, some { target := 397, numerator := 22686059689046460820787036160 }, some { target := 398, numerator := 25926925358910240938042327040 }, some { target := 399, numerator := 30464137296719533102199734272 }, some { target := 400, numerator := 359736089354879593015337287680 }, some { target := 401, numerator := 808920071197999517266920603648 }, some { target := 402, numerator := 22686059689046460820787036160 }, some { target := 403, numerator := 359736089354879593015337287680 }, some { target := 404, numerator := 25926925358910240938042327040 }, some { target := 405, numerator := 25278752224937484914591268864 }, some { target := 406, numerator := 25278752224937484914591268864 }, some { target := 407, numerator := 25278752224937484914591268864 }, some { target := 408, numerator := 808920071197999517266920603648 }, some { target := 409, numerator := 25278752224937484914591268864 }, some { target := 410, numerator := 29167791028774021055297617920 }, some { target := 411, numerator := 30464137296719533102199734272 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 431, numerator := 1142434899535824570097336320 }, some { target := 432, numerator := 888560477416752443409039360 }, some { target := 433, numerator := 1015497688476288506753187840 }, some { target := 434, numerator := 1193209783959638995434995712 }, some { target := 435, numerator := 14090030427608503031200481280 }, some { target := 436, numerator := 31683527880460201410699460608 }, some { target := 437, numerator := 888560477416752443409039360 }, some { target := 438, numerator := 14090030427608503031200481280 }, some { target := 439, numerator := 1015497688476288506753187840 }, some { target := 440, numerator := 990110246264381294084358144 }, some { target := 441, numerator := 990110246264381294084358144 }, some { target := 442, numerator := 990110246264381294084358144 }, some { target := 443, numerator := 31683527880460201410699460608 }, some { target := 444, numerator := 990110246264381294084358144 }, some { target := 445, numerator := 1142434899535824570097336320 }, some { target := 446, numerator := 1193209783959638995434995712 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 492, numerator := 1904058165893040950162227200 }, some { target := 493, numerator := 1480934129027920739015065600 }, some { target := 494, numerator := 1692496147460480844588646400 }, some { target := 495, numerator := 1988682973266064992391659520 }, some { target := 496, numerator := 23483384046014171718667468800 }, some { target := 497, numerator := 52805879800767002351165767680 }, some { target := 498, numerator := 1480934129027920739015065600 }, some { target := 499, numerator := 23483384046014171718667468800 }, some { target := 500, numerator := 1692496147460480844588646400 }, some { target := 501, numerator := 1650183743773968823473930240 }, some { target := 502, numerator := 1650183743773968823473930240 }, some { target := 503, numerator := 1650183743773968823473930240 }, some { target := 504, numerator := 52805879800767002351165767680 }, some { target := 505, numerator := 1650183743773968823473930240 }, some { target := 506, numerator := 1904058165893040950162227200 }, some { target := 507, numerator := 1988682973266064992391659520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 527, numerator := 1820755621135220408592629760 }, some { target := 528, numerator := 1416143260882949206683156480 }, some { target := 529, numerator := 1618449441009084807637893120 }, some { target := 530, numerator := 1901678093185674648974524416 }, some { target := 531, numerator := 22455985994001051705975767040 }, some { target := 532, numerator := 50495622559483445998302265344 }, some { target := 533, numerator := 1416143260882949206683156480 }, some { target := 534, numerator := 22455985994001051705975767040 }, some { target := 535, numerator := 1618449441009084807637893120 }, some { target := 536, numerator := 1577988204983857687446945792 }, some { target := 537, numerator := 1577988204983857687446945792 }, some { target := 538, numerator := 1577988204983857687446945792 }, some { target := 539, numerator := 50495622559483445998302265344 }, some { target := 540, numerator := 1577988204983857687446945792 }, some { target := 541, numerator := 1820755621135220408592629760 }, some { target := 542, numerator := 1901678093185674648974524416 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 637, numerator := 59501817684157529692569600 }, some { target := 638, numerator := 46279191532122523094220800 }, some { target := 639, numerator := 52890504608140026393395200 }, some { target := 640, numerator := 62146342914564531012239360 }, some { target := 641, numerator := 733855751437942866208358400 }, some { target := 642, numerator := 1650183743773968823473930240 }, some { target := 643, numerator := 46279191532122523094220800 }, some { target := 644, numerator := 733855751437942866208358400 }, some { target := 645, numerator := 52890504608140026393395200 }, some { target := 646, numerator := 51568241992936525733560320 }, some { target := 647, numerator := 51568241992936525733560320 }, some { target := 648, numerator := 51568241992936525733560320 }, some { target := 649, numerator := 1650183743773968823473930240 }, some { target := 650, numerator := 51568241992936525733560320 }, some { target := 651, numerator := 59501817684157529692569600 }, some { target := 652, numerator := 62146342914564531012239360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 663, numerator := 1142434899535824570097336320 }, some { target := 664, numerator := 888560477416752443409039360 }, some { target := 665, numerator := 1015497688476288506753187840 }, some { target := 666, numerator := 1193209783959638995434995712 }, some { target := 667, numerator := 14090030427608503031200481280 }, some { target := 668, numerator := 31683527880460201410699460608 }, some { target := 669, numerator := 888560477416752443409039360 }, some { target := 670, numerator := 14090030427608503031200481280 }, some { target := 671, numerator := 1015497688476288506753187840 }, some { target := 672, numerator := 990110246264381294084358144 }, some { target := 673, numerator := 990110246264381294084358144 }, some { target := 674, numerator := 990110246264381294084358144 }, some { target := 675, numerator := 31683527880460201410699460608 }, some { target := 676, numerator := 990110246264381294084358144 }, some { target := 677, numerator := 1142434899535824570097336320 }, some { target := 678, numerator := 1193209783959638995434995712 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 698, numerator := 59501817684157529692569600 }, some { target := 699, numerator := 46279191532122523094220800 }, some { target := 700, numerator := 52890504608140026393395200 }, some { target := 701, numerator := 62146342914564531012239360 }, some { target := 702, numerator := 733855751437942866208358400 }, some { target := 703, numerator := 1650183743773968823473930240 }, some { target := 704, numerator := 46279191532122523094220800 }, some { target := 705, numerator := 733855751437942866208358400 }, some { target := 706, numerator := 52890504608140026393395200 }, some { target := 707, numerator := 51568241992936525733560320 }, some { target := 708, numerator := 51568241992936525733560320 }, some { target := 709, numerator := 51568241992936525733560320 }, some { target := 710, numerator := 1650183743773968823473930240 }, some { target := 711, numerator := 51568241992936525733560320 }, some { target := 712, numerator := 59501817684157529692569600 }, some { target := 713, numerator := 62146342914564531012239360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 759, numerator := 1832655984672051914531143680 }, some { target := 760, numerator := 1425399099189373711302000640 }, some { target := 761, numerator := 1629027541930712812916572160 }, some { target := 762, numerator := 1914107361768587555176972288 }, some { target := 763, numerator := 22602757144288640279217438720 }, some { target := 764, numerator := 50825659308238239762997051392 }, some { target := 765, numerator := 1425399099189373711302000640 }, some { target := 766, numerator := 22602757144288640279217438720 }, some { target := 767, numerator := 1629027541930712812916572160 }, some { target := 768, numerator := 1588301853382444992593657856 }, some { target := 769, numerator := 1588301853382444992593657856 }, some { target := 770, numerator := 1588301853382444992593657856 }, some { target := 771, numerator := 50825659308238239762997051392 }, some { target := 772, numerator := 1588301853382444992593657856 }, some { target := 773, numerator := 1832655984672051914531143680 }, some { target := 774, numerator := 1914107361768587555176972288 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 794, numerator := 1035331627704341016650711040 }, some { target := 795, numerator := 805257932658931901839441920 }, some { target := 796, numerator := 920294780181636459245076480 }, some { target := 797, numerator := 1081346366713422839612964864 }, some { target := 798, numerator := 12769090075020205872025436160 }, some { target := 799, numerator := 28713197141667057528446386176 }, some { target := 800, numerator := 805257932658931901839441920 }, some { target := 801, numerator := 12769090075020205872025436160 }, some { target := 802, numerator := 920294780181636459245076480 }, some { target := 803, numerator := 897287410677095547763949568 }, some { target := 804, numerator := 897287410677095547763949568 }, some { target := 805, numerator := 897287410677095547763949568 }, some { target := 806, numerator := 28713197141667057528446386176 }, some { target := 807, numerator := 897287410677095547763949568 }, some { target := 808, numerator := 1035331627704341016650711040 }, some { target := 809, numerator := 1081346366713422839612964864 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 890, numerator := 71402181220989035631083520 }, some { target := 891, numerator := 55535029838547027713064960 }, some { target := 892, numerator := 63468605529768031672074240 }, some { target := 893, numerator := 74575611497477437214687232 }, some { target := 894, numerator := 880626901725531439450030080 }, some { target := 895, numerator := 1980220492528762588168716288 }, some { target := 896, numerator := 55535029838547027713064960 }, some { target := 897, numerator := 880626901725531439450030080 }, some { target := 898, numerator := 63468605529768031672074240 }, some { target := 899, numerator := 61881890391523830880272384 }, some { target := 900, numerator := 61881890391523830880272384 }, some { target := 901, numerator := 61881890391523830880272384 }, some { target := 902, numerator := 1980220492528762588168716288 }, some { target := 903, numerator := 61881890391523830880272384 }, some { target := 904, numerator := 71402181220989035631083520 }, some { target := 905, numerator := 74575611497477437214687232 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent0
