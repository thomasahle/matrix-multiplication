import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk4Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 3, for region 1, branch 2,
parent 21; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot15

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨15, 1, #[1653998616576, 139083489738752, 0, 0, 0, 0, 139083456184320, 0, 0, 0, 0, 0, 0, 0, 1654032171008, 0, 0, 0, 0], #[70437463654400, 69956427317248, 70437463654400, 70643622084608, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes

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
        1 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total1.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 263, numerator := 116503467439499881375334400 }, some { target := 264, numerator := 115707834003327687063502848 }, some { target := 265, numerator := 116503467439499881375334400 }, some { target := 266, numerator := 116844453197859393223262208 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 338, numerator := 9796688253400459351215308800 }, some { target := 339, numerator := 9729784040938212311743594496 }, some { target := 340, numerator := 9796688253400459351215308800 }, some { target := 341, numerator := 9825361487312850939560329216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 599, numerator := 9796685889911374907179008000 }, some { target := 600, numerator := 9729781693590028932203151360 }, some { target := 601, numerator := 9796685889911374907179008000 }, some { target := 602, numerator := 9825359116906237467882946560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 773, numerator := 116505830928584325411635200 }, some { target := 774, numerator := 115710181351511066603945984 }, some { target := 775, numerator := 116505830928584325411635200 }, some { target := 776, numerator := 116846823604472864900644864 }]

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

end Slot15

namespace Slot16

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨16, 41, #[153243090944, 22633202581504, 0, 235902085365760, 0, 0, 0, 0, 0, 0, 0, 22633202581504, 0, 0, 0, 0, 0, 0, 153243090944], #[2130303778816, 52226802319360, 2130303778816, 43774306680832, 43018392436736, 2130303778816, 43087111913472, 38620345925632, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

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
        2 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 131, numerator := 13384627764333333094334464 }, some { target := 132, numerator := 328139261319139779086909440 }, some { target := 133, numerator := 13384627764333333094334464 }, some { target := 134, numerator := 275032512447752683261001728 }, some { target := 135, numerator := 270283128402344081195270144 }, some { target := 136, numerator := 13384627764333333094334464 }, some { target := 137, numerator := 270714890588290317746700288 }, some { target := 138, numerator := 242650348501784941903740928 }, some { target := 139, numerator := 328139261319139779086909440 }, some { target := 140, numerator := 13384627764333333094334464 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 227, numerator := 1976839476429526714573389824 }, some { target := 228, numerator := 48464451680207751712121815040 }, some { target := 229, numerator := 1976839476429526714573389824 }, some { target := 230, numerator := 40620862789858339263975784448 }, some { target := 231, numerator := 39919403620802700752352968704 }, some { target := 232, numerator := 1976839476429526714573389824 }, some { target := 233, numerator := 39983172636171395162500497408 }, some { target := 234, numerator := 35838186637206258502911131648 }, some { target := 235, numerator := 48464451680207751712121815040 }, some { target := 236, numerator := 1976839476429526714573389824 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 302, numerator := 20604267259295378801489346560 }, some { target := 303, numerator := 505136874744015738359093657600 }, some { target := 304, numerator := 20604267259295378801489346560 }, some { target := 305, numerator := 423384459489392138598345605120 }, some { target := 306, numerator := 416073267881255068701042933760 }, some { target := 307, numerator := 20604267259295378801489346560 }, some { target := 308, numerator := 416737921663812984146252267520 }, some { target := 309, numerator := 373535425797548480207645573120 }, some { target := 310, numerator := 505136874744015738359093657600 }, some { target := 311, numerator := 20604267259295378801489346560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 589, numerator := 1976839476429526714573389824 }, some { target := 590, numerator := 48464451680207751712121815040 }, some { target := 591, numerator := 1976839476429526714573389824 }, some { target := 592, numerator := 40620862789858339263975784448 }, some { target := 593, numerator := 39919403620802700752352968704 }, some { target := 594, numerator := 1976839476429526714573389824 }, some { target := 595, numerator := 39983172636171395162500497408 }, some { target := 596, numerator := 35838186637206258502911131648 }, some { target := 597, numerator := 48464451680207751712121815040 }, some { target := 598, numerator := 1976839476429526714573389824 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 763, numerator := 13384627764333333094334464 }, some { target := 764, numerator := 328139261319139779086909440 }, some { target := 765, numerator := 13384627764333333094334464 }, some { target := 766, numerator := 275032512447752683261001728 }, some { target := 767, numerator := 270283128402344081195270144 }, some { target := 768, numerator := 13384627764333333094334464 }, some { target := 769, numerator := 270714890588290317746700288 }, some { target := 770, numerator := 242650348501784941903740928 }, some { target := 771, numerator := 328139261319139779086909440 }, some { target := 772, numerator := 13384627764333333094334464 }]

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
def data : BetaFourLocalSlotData := ⟨17, 602, #[3779168567296, 0, 136958319788032, 0, 0, 136958370119680, 0, 0, 0, 0, 0, 0, 3779118235648, 0, 0, 0, 0, 0, 0], #[3298534883328, 3229815406592, 2542620639232, 79920751443968, 2542620639232, 2542620639232, 2611340115968, 2611340115968, 44186623541248, 2405181685760, 79920751443968, 44186623541248, 3298534883328, 2542620639232, 2405181685760, 3229815406592, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

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
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 80, numerator := 7504363048219938878417534976 }, some { target := 81, numerator := 7348022151382023485117169664 }, some { target := 82, numerator := 5784613183002869552113516544 }, some { target := 83, numerator := 181824463022495602408324857856 }, some { target := 84, numerator := 5784613183002869552113516544 }, some { target := 85, numerator := 5784613183002869552113516544 }, some { target := 86, numerator := 5940954079840784945413881856 }, some { target := 87, numerator := 5940954079840784945413881856 }, some { target := 88, numerator := 100527196666779597892134895616 }, some { target := 89, numerator := 5471931389327038765512785920 }, some { target := 90, numerator := 181824463022495602408324857856 }, some { target := 91, numerator := 100527196666779597892134895616 }, some { target := 92, numerator := 7504363048219938878417534976 }, some { target := 93, numerator := 5784613183002869552113516544 }, some { target := 94, numerator := 5471931389327038765512785920 }, some { target := 95, numerator := 7348022151382023485117169664 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 176, numerator := 271960600820454658180059758592 }, some { target := 177, numerator := 266294754970028519467975180288 }, some { target := 178, numerator := 209636296465767132347129397248 }, some { target := 179, numerator := 6589378724045599322154364567552 }, some { target := 180, numerator := 209636296465767132347129397248 }, some { target := 181, numerator := 209636296465767132347129397248 }, some { target := 182, numerator := 215302142316193271059213975552 }, some { target := 183, numerator := 215302142316193271059213975552 }, some { target := 184, numerator := 3643138881824007191870383849472 }, some { target := 185, numerator := 198304604764914854922960240640 }, some { target := 186, numerator := 6589378724045599322154364567552 }, some { target := 187, numerator := 3643138881824007191870383849472 }, some { target := 188, numerator := 271960600820454658180059758592 }, some { target := 189, numerator := 209636296465767132347129397248 }, some { target := 190, numerator := 198304604764914854922960240640 }, some { target := 191, numerator := 266294754970028519467975180288 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 286, numerator := 271960700764914049538410414080 }, some { target := 287, numerator := 266294852832311673506360197120 }, some { target := 288, numerator := 209636373506287913185858027520 }, some { target := 289, numerator := 6589381145616563325274402324480 }, some { target := 290, numerator := 209636373506287913185858027520 }, some { target := 291, numerator := 209636373506287913185858027520 }, some { target := 292, numerator := 215302221438890289217908244480 }, some { target := 293, numerator := 215302221438890289217908244480 }, some { target := 294, numerator := 3643140220663327788608289505280 }, some { target := 295, numerator := 198304677641083161121757593600 }, some { target := 296, numerator := 6589381145616563325274402324480 }, some { target := 297, numerator := 3643140220663327788608289505280 }, some { target := 298, numerator := 271960700764914049538410414080 }, some { target := 299, numerator := 209636373506287913185858027520 }, some { target := 300, numerator := 198304677641083161121757593600 }, some { target := 301, numerator := 266294852832311673506360197120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 573, numerator := 7504263103760547520066879488 }, some { target := 574, numerator := 7347924289098869446732152832 }, some { target := 575, numerator := 5784536142482088713384886272 }, some { target := 576, numerator := 181822041451531599288287100928 }, some { target := 577, numerator := 5784536142482088713384886272 }, some { target := 578, numerator := 5784536142482088713384886272 }, some { target := 579, numerator := 5940874957143766786719612928 }, some { target := 580, numerator := 5940874957143766786719612928 }, some { target := 581, numerator := 100525857827459001154229239808 }, some { target := 582, numerator := 5471858513158732566715432960 }, some { target := 583, numerator := 181822041451531599288287100928 }, some { target := 584, numerator := 100525857827459001154229239808 }, some { target := 585, numerator := 7504263103760547520066879488 }, some { target := 586, numerator := 5784536142482088713384886272 }, some { target := 587, numerator := 5471858513158732566715432960 }, some { target := 588, numerator := 7347924289098869446732152832 }]

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

namespace Slot18

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨18, 1064, #[52224319291392, 0, 0, 177026338127872, 0, 52224319291392, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 26, numerator := 22911077279115218737176772608 }, some { target := 27, numerator := 610962060776405832991380602880 }, some { target := 28, numerator := 584232470617438077798007701504 }, some { target := 29, numerator := 19092564399262682280980643840 }, some { target := 30, numerator := 599506522136848223622792216576 }, some { target := 31, numerator := 19092564399262682280980643840 }, some { target := 32, numerator := 584232470617438077798007701504 }, some { target := 33, numerator := 332210620547170671689063202816 }, some { target := 34, numerator := 599506522136848223622792216576 }, some { target := 35, numerator := 9359175068518566854136711610368 }, some { target := 36, numerator := 366577236465843499794828361728 }, some { target := 37, numerator := 610962060776405832991380602880 }, some { target := 38, numerator := 584232470617438077798007701504 }, some { target := 39, numerator := 19092564399262682280980643840 }, some { target := 40, numerator := 366577236465843499794828361728 }, some { target := 41, numerator := 19092564399262682280980643840 }, some { target := 42, numerator := 588050983497290614254203830272 }, some { target := 43, numerator := 332210620547170671689063202816 }, some { target := 44, numerator := 22911077279115218737176772608 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 157, numerator := 77662364360486244946834096128 }, some { target := 158, numerator := 2070996382946299865248909230080 }, some { target := 159, numerator := 1980390291192399246144269451264 }, some { target := 160, numerator := 64718636967071870789028413440 }, some { target := 161, numerator := 2032165200766056742775492182016 }, some { target := 162, numerator := 64718636967071870789028413440 }, some { target := 163, numerator := 1980390291192399246144269451264 }, some { target := 164, numerator := 1126104283227050551729094393856 }, some { target := 165, numerator := 2032165200766056742775492182016 }, some { target := 166, numerator := 31725075841258631060781728268288 }, some { target := 167, numerator := 1242597829767779919149345538048 }, some { target := 168, numerator := 2070996382946299865248909230080 }, some { target := 169, numerator := 1980390291192399246144269451264 }, some { target := 170, numerator := 64718636967071870789028413440 }, some { target := 171, numerator := 1242597829767779919149345538048 }, some { target := 172, numerator := 64718636967071870789028413440 }, some { target := 173, numerator := 1993334018585813620302075133952 }, some { target := 174, numerator := 1126104283227050551729094393856 }, some { target := 175, numerator := 77662364360486244946834096128 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 22911077279115218737176772608 }, some { target := 268, numerator := 610962060776405832991380602880 }, some { target := 269, numerator := 584232470617438077798007701504 }, some { target := 270, numerator := 19092564399262682280980643840 }, some { target := 271, numerator := 599506522136848223622792216576 }, some { target := 272, numerator := 19092564399262682280980643840 }, some { target := 273, numerator := 584232470617438077798007701504 }, some { target := 274, numerator := 332210620547170671689063202816 }, some { target := 275, numerator := 599506522136848223622792216576 }, some { target := 276, numerator := 9359175068518566854136711610368 }, some { target := 277, numerator := 366577236465843499794828361728 }, some { target := 278, numerator := 610962060776405832991380602880 }, some { target := 279, numerator := 584232470617438077798007701504 }, some { target := 280, numerator := 19092564399262682280980643840 }, some { target := 281, numerator := 366577236465843499794828361728 }, some { target := 282, numerator := 19092564399262682280980643840 }, some { target := 283, numerator := 588050983497290614254203830272 }, some { target := 284, numerator := 332210620547170671689063202816 }, some { target := 285, numerator := 22911077279115218737176772608 }]

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

end Slot18

namespace Slot19

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨19, 52, #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

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
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 10, numerator := 17601959933589000783721922560 }, some { target := 11, numerator := 18104873074548686520399691776 }, some { target := 12, numerator := 17601959933589000783721922560 }, some { target := 13, numerator := 15590307369750257837010845696 }, some { target := 14, numerator := 729726967532504003919443132416 }, some { target := 15, numerator := 198650690679075865987718840320 }, some { target := 16, numerator := 18104873074548686520399691776 }, some { target := 17, numerator := 729726967532504003919443132416 }, some { target := 18, numerator := 17601959933589000783721922560 }, some { target := 19, numerator := 17601959933589000783721922560 }, some { target := 20, numerator := 15087394228790572100333076480 }, some { target := 21, numerator := 17601959933589000783721922560 }, some { target := 22, numerator := 198650690679075865987718840320 }, some { target := 23, numerator := 15087394228790572100333076480 }, some { target := 24, numerator := 17601959933589000783721922560 }, some { target := 25, numerator := 15590307369750257837010845696 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 141, numerator := 17601959933589000783721922560 }, some { target := 142, numerator := 18104873074548686520399691776 }, some { target := 143, numerator := 17601959933589000783721922560 }, some { target := 144, numerator := 15590307369750257837010845696 }, some { target := 145, numerator := 729726967532504003919443132416 }, some { target := 146, numerator := 198650690679075865987718840320 }, some { target := 147, numerator := 18104873074548686520399691776 }, some { target := 148, numerator := 729726967532504003919443132416 }, some { target := 149, numerator := 17601959933589000783721922560 }, some { target := 150, numerator := 17601959933589000783721922560 }, some { target := 151, numerator := 15087394228790572100333076480 }, some { target := 152, numerator := 17601959933589000783721922560 }, some { target := 153, numerator := 198650690679075865987718840320 }, some { target := 154, numerator := 15087394228790572100333076480 }, some { target := 155, numerator := 17601959933589000783721922560 }, some { target := 156, numerator := 15590307369750257837010845696 }]

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

end Slot19

namespace Slot20

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨20, 0, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot20

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4.Parent3
