import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk0Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 2, for region 1, branch 2,
parent 4; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk0.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot5

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨5, 1, #[3298534883328, 3229815406592, 2542620639232, 79920751443968, 2542620639232, 2542620639232, 2611340115968, 2611340115968, 44186623541248, 2405181685760, 79920751443968, 44186623541248, 3298534883328, 2542620639232, 2405181685760, 3229815406592, 0, 0, 0], #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 2, numerator := 232113757366008801543585792 }, some { target := 3, numerator := 232113757366008801543585792 }, some { target := 4, numerator := 232113757366008801543585792 }, some { target := 5, numerator := 232113757366008801543585792 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 7, numerator := 227278054087550284844761088 }, some { target := 8, numerator := 227278054087550284844761088 }, some { target := 9, numerator := 227278054087550284844761088 }, some { target := 10, numerator := 227278054087550284844761088 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 22, numerator := 178921021302965117856514048 }, some { target := 23, numerator := 178921021302965117856514048 }, some { target := 24, numerator := 178921021302965117856514048 }, some { target := 25, numerator := 178921021302965117856514048 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 27, numerator := 5623922912847254920733130752 }, some { target := 28, numerator := 5623922912847254920733130752 }, some { target := 29, numerator := 5623922912847254920733130752 }, some { target := 30, numerator := 5623922912847254920733130752 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 41, numerator := 178921021302965117856514048 }, some { target := 42, numerator := 178921021302965117856514048 }, some { target := 43, numerator := 178921021302965117856514048 }, some { target := 44, numerator := 178921021302965117856514048 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 72, numerator := 178921021302965117856514048 }, some { target := 73, numerator := 178921021302965117856514048 }, some { target := 74, numerator := 178921021302965117856514048 }, some { target := 75, numerator := 178921021302965117856514048 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 86, numerator := 183756724581423634555338752 }, some { target := 87, numerator := 183756724581423634555338752 }, some { target := 88, numerator := 183756724581423634555338752 }, some { target := 89, numerator := 183756724581423634555338752 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 162, numerator := 183756724581423634555338752 }, some { target := 163, numerator := 183756724581423634555338752 }, some { target := 164, numerator := 183756724581423634555338752 }, some { target := 165, numerator := 183756724581423634555338752 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 167, numerator := 3109357208048826237344284672 }, some { target := 168, numerator := 3109357208048826237344284672 }, some { target := 169, numerator := 3109357208048826237344284672 }, some { target := 170, numerator := 3109357208048826237344284672 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 181, numerator := 169249614746048084458864640 }, some { target := 182, numerator := 169249614746048084458864640 }, some { target := 183, numerator := 169249614746048084458864640 }, some { target := 184, numerator := 169249614746048084458864640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 212, numerator := 5623922912847254920733130752 }, some { target := 213, numerator := 5623922912847254920733130752 }, some { target := 214, numerator := 5623922912847254920733130752 }, some { target := 215, numerator := 5623922912847254920733130752 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 226, numerator := 3109357208048826237344284672 }, some { target := 227, numerator := 3109357208048826237344284672 }, some { target := 228, numerator := 3109357208048826237344284672 }, some { target := 229, numerator := 3109357208048826237344284672 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 301, numerator := 232113757366008801543585792 }, some { target := 302, numerator := 232113757366008801543585792 }, some { target := 303, numerator := 232113757366008801543585792 }, some { target := 304, numerator := 232113757366008801543585792 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 428, numerator := 178921021302965117856514048 }, some { target := 429, numerator := 178921021302965117856514048 }, some { target := 430, numerator := 178921021302965117856514048 }, some { target := 431, numerator := 178921021302965117856514048 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 442, numerator := 169249614746048084458864640 }, some { target := 443, numerator := 169249614746048084458864640 }, some { target := 444, numerator := 169249614746048084458864640 }, some { target := 445, numerator := 169249614746048084458864640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 517, numerator := 227278054087550284844761088 }, some { target := 518, numerator := 227278054087550284844761088 }, some { target := 519, numerator := 227278054087550284844761088 }, some { target := 520, numerator := 227278054087550284844761088 }]

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

end Slot5

namespace Slot6

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨6, 0, #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3298534883328, 3229815406592, 2542620639232, 79920751443968, 2542620639232, 2542620639232, 2611340115968, 2611340115968, 44186623541248, 2405181685760, 79920751443968, 44186623541248, 3298534883328, 2542620639232, 2405181685760, 3229815406592, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot6

namespace Slot7

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨7, 10, #[24086361145344, 0, 233302254419968, 0, 0, 0, 0, 24086361145344, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 2, 7]

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
  [some { target := 142, numerator := 99312128062941679363031040 }, some { target := 143, numerator := 2648323415011778116347494400 }, some { target := 144, numerator := 2532459265605012823757291520 }, some { target := 145, numerator := 82760106719118066135859200 }, some { target := 146, numerator := 2598667350980307276665978880 }, some { target := 147, numerator := 82760106719118066135859200 }, some { target := 148, numerator := 2532459265605012823757291520 }, some { target := 149, numerator := 1440025856912654350763950080 }, some { target := 150, numerator := 2598667350980307276665978880 }, some { target := 151, numerator := 40569004313711676019798179840 }, some { target := 152, numerator := 1588994049007066869808496640 }, some { target := 153, numerator := 2648323415011778116347494400 }, some { target := 154, numerator := 2532459265605012823757291520 }, some { target := 155, numerator := 82760106719118066135859200 }, some { target := 156, numerator := 1588994049007066869808496640 }, some { target := 157, numerator := 82760106719118066135859200 }, some { target := 158, numerator := 2549011286948836436984463360 }, some { target := 159, numerator := 1440025856912654350763950080 }, some { target := 160, numerator := 99312128062941679363031040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 357, numerator := 961944530704160648991866880 }, some { target := 358, numerator := 25651854152110950639783116800 }, some { target := 359, numerator := 24529585532956096549292605440 }, some { target := 360, numerator := 801620442253467207493222400 }, some { target := 361, numerator := 25170881886758870315287183360 }, some { target := 362, numerator := 801620442253467207493222400 }, some { target := 363, numerator := 24529585532956096549292605440 }, some { target := 364, numerator := 13948195695210329410382069760 }, some { target := 365, numerator := 25170881886758870315287183360 }, some { target := 366, numerator := 392954340792649625113177620480 }, some { target := 367, numerator := 15391112491266570383869870080 }, some { target := 368, numerator := 25651854152110950639783116800 }, some { target := 369, numerator := 24529585532956096549292605440 }, some { target := 370, numerator := 801620442253467207493222400 }, some { target := 371, numerator := 15391112491266570383869870080 }, some { target := 372, numerator := 801620442253467207493222400 }, some { target := 373, numerator := 24689909621406789990791249920 }, some { target := 374, numerator := 13948195695210329410382069760 }, some { target := 375, numerator := 961944530704160648991866880 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 669, numerator := 99312128062941679363031040 }, some { target := 670, numerator := 2648323415011778116347494400 }, some { target := 671, numerator := 2532459265605012823757291520 }, some { target := 672, numerator := 82760106719118066135859200 }, some { target := 673, numerator := 2598667350980307276665978880 }, some { target := 674, numerator := 82760106719118066135859200 }, some { target := 675, numerator := 2532459265605012823757291520 }, some { target := 676, numerator := 1440025856912654350763950080 }, some { target := 677, numerator := 2598667350980307276665978880 }, some { target := 678, numerator := 40569004313711676019798179840 }, some { target := 679, numerator := 1588994049007066869808496640 }, some { target := 680, numerator := 2648323415011778116347494400 }, some { target := 681, numerator := 2532459265605012823757291520 }, some { target := 682, numerator := 82760106719118066135859200 }, some { target := 683, numerator := 1588994049007066869808496640 }, some { target := 684, numerator := 82760106719118066135859200 }, some { target := 685, numerator := 2549011286948836436984463360 }, some { target := 686, numerator := 1440025856912654350763950080 }, some { target := 687, numerator := 99312128062941679363031040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left2.expected ++ Left7.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left2.routed_eq, Left7.routed_eq]
  rfl

end Slot7

namespace Slot8

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨8, 52, #[1661028270080, 139076460085248, 0, 0, 0, 0, 139076510416896, 0, 0, 0, 0, 0, 0, 0, 1660977938432, 0, 0, 0, 0], #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0]⟩

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
  [some { target := 55, numerator := 207743888285753610443161600 }, some { target := 56, numerator := 213679427951060856455823360 }, some { target := 57, numerator := 207743888285753610443161600 }, some { target := 58, numerator := 184001729624524626392514560 }, some { target := 59, numerator := 8612468054360813964372213760 }, some { target := 60, numerator := 2344538167796362175001395200 }, some { target := 61, numerator := 213679427951060856455823360 }, some { target := 62, numerator := 8612468054360813964372213760 }, some { target := 63, numerator := 207743888285753610443161600 }, some { target := 64, numerator := 207743888285753610443161600 }, some { target := 65, numerator := 178066189959217380379852800 }, some { target := 66, numerator := 207743888285753610443161600 }, some { target := 67, numerator := 2344538167796362175001395200 }, some { target := 68, numerator := 178066189959217380379852800 }, some { target := 69, numerator := 207743888285753610443161600 }, some { target := 70, numerator := 184001729624524626392514560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 100, numerator := 17394216045303247173278760960 }, some { target := 101, numerator := 17891193646597625663943868416 }, some { target := 102, numerator := 17394216045303247173278760960 }, some { target := 103, numerator := 15406305640125733210618331136 }, some { target := 104, numerator := 721114499478143189955070918656 }, some { target := 105, numerator := 196306152511279503812717445120 }, some { target := 106, numerator := 17891193646597625663943868416 }, some { target := 107, numerator := 721114499478143189955070918656 }, some { target := 108, numerator := 17394216045303247173278760960 }, some { target := 109, numerator := 17394216045303247173278760960 }, some { target := 110, numerator := 14909328038831354719953223680 }, some { target := 111, numerator := 17394216045303247173278760960 }, some { target := 112, numerator := 196306152511279503812717445120 }, some { target := 113, numerator := 14909328038831354719953223680 }, some { target := 114, numerator := 17394216045303247173278760960 }, some { target := 115, numerator := 15406305640125733210618331136 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 315, numerator := 17394222340254662326663249920 }, some { target := 316, numerator := 17891200121404795535996485632 }, some { target := 317, numerator := 17394222340254662326663249920 }, some { target := 318, numerator := 15406311215654129489330307072 }, some { target := 319, numerator := 721114760448843286742525018112 }, some { target := 320, numerator := 196306223554302617686628106240 }, some { target := 321, numerator := 17891200121404795535996485632 }, some { target := 322, numerator := 721114760448843286742525018112 }, some { target := 323, numerator := 17394222340254662326663249920 }, some { target := 324, numerator := 17394222340254662326663249920 }, some { target := 325, numerator := 14909333434503996279997071360 }, some { target := 326, numerator := 17394222340254662326663249920 }, some { target := 327, numerator := 196306223554302617686628106240 }, some { target := 328, numerator := 14909333434503996279997071360 }, some { target := 329, numerator := 17394222340254662326663249920 }, some { target := 330, numerator := 15406311215654129489330307072 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 653, numerator := 207737593334338457058672640 }, some { target := 654, numerator := 213672953143890984403206144 }, some { target := 655, numerator := 207737593334338457058672640 }, some { target := 656, numerator := 183996154096128347680538624 }, some { target := 657, numerator := 8612207083660717176918114304 }, some { target := 658, numerator := 2344467124773248301090734080 }, some { target := 659, numerator := 213672953143890984403206144 }, some { target := 660, numerator := 8612207083660717176918114304 }, some { target := 661, numerator := 207737593334338457058672640 }, some { target := 662, numerator := 207737593334338457058672640 }, some { target := 663, numerator := 178060794286575820336005120 }, some { target := 664, numerator := 207737593334338457058672640 }, some { target := 665, numerator := 2344467124773248301090734080 }, some { target := 666, numerator := 178060794286575820336005120 }, some { target := 667, numerator := 207737593334338457058672640 }, some { target := 668, numerator := 183996154096128347680538624 }]

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

end Slot8

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk0.Parent3
