import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk16Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 1, for region 1, branch 1,
parent 68; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot6

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨6, 218, #[206963736576, 24461784907776, 0, 232137462644736, 0, 0, 0, 0, 0, 0, 0, 24461801684992, 0, 0, 0, 0, 0, 0, 206963736576], #[3298534883328, 2473901162496, 2611340115968, 3367254360064, 45079976738816, 78821239816192, 2405181685760, 45079976738816, 2542620639232, 2611340115968, 2611340115968, 2542620639232, 78821239816192, 2542620639232, 3298534883328, 3367254360064, 0, 0, 0]⟩

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
  [some { target := 34, numerator := 148823608820205792792674304 }, some { target := 35, numerator := 111617706615154344594505728 }, some { target := 36, numerator := 117818690315996252627533824 }, some { target := 37, numerator := 151924100670626746809188352 }, some { target := 38, numerator := 2033922653876145834833215488 }, some { target := 39, numerator := 3556264152432834256941613056 }, some { target := 40, numerator := 108517214764733390577991680 }, some { target := 41, numerator := 2033922653876145834833215488 }, some { target := 42, numerator := 114718198465575298611019776 }, some { target := 43, numerator := 117818690315996252627533824 }, some { target := 44, numerator := 117818690315996252627533824 }, some { target := 45, numerator := 114718198465575298611019776 }, some { target := 46, numerator := 3556264152432834256941613056 }, some { target := 47, numerator := 114718198465575298611019776 }, some { target := 48, numerator := 148823608820205792792674304 }, some { target := 49, numerator := 151924100670626746809188352 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 79, numerator := 17589995080234887589190959104 }, some { target := 80, numerator := 13192496310176165691893219328 }, some { target := 81, numerator := 13925412771852619341442842624 }, some { target := 82, numerator := 17956453311073114413965770752 }, some { target := 83, numerator := 240396599429876797052276441088 }, some { target := 84, numerator := 420327590771446168016708960256 }, some { target := 85, numerator := 12826038079337938867118407680 }, some { target := 86, numerator := 240396599429876797052276441088 }, some { target := 87, numerator := 13558954541014392516668030976 }, some { target := 88, numerator := 13925412771852619341442842624 }, some { target := 89, numerator := 13925412771852619341442842624 }, some { target := 90, numerator := 13558954541014392516668030976 }, some { target := 91, numerator := 420327590771446168016708960256 }, some { target := 92, numerator := 13558954541014392516668030976 }, some { target := 93, numerator := 17589995080234887589190959104 }, some { target := 94, numerator := 17956453311073114413965770752 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 154, numerator := 166925546980878863975992786944 }, some { target := 155, numerator := 125194160235659147981994590208 }, some { target := 156, numerator := 132149391359862433980994289664 }, some { target := 157, numerator := 170403162542980506975492636672 }, some { target := 158, numerator := 2281315808738677807671901421568 }, some { target := 159, numerator := 3988825049730584520426327638016 }, some { target := 160, numerator := 121716544673557504982494740480 }, some { target := 161, numerator := 2281315808738677807671901421568 }, some { target := 162, numerator := 128671775797760790981494439936 }, some { target := 163, numerator := 132149391359862433980994289664 }, some { target := 164, numerator := 132149391359862433980994289664 }, some { target := 165, numerator := 128671775797760790981494439936 }, some { target := 166, numerator := 3988825049730584520426327638016 }, some { target := 167, numerator := 128671775797760790981494439936 }, some { target := 168, numerator := 166925546980878863975992786944 }, some { target := 169, numerator := 170403162542980506975492636672 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 492, numerator := 17590007144405511795237715968 }, some { target := 493, numerator := 13192505358304133846428286976 }, some { target := 494, numerator := 13925422322654363504563191808 }, some { target := 495, numerator := 17956465626580626624305168384 }, some { target := 496, numerator := 240396764306875327868248784896 }, some { target := 497, numerator := 420327879054856708940367921152 }, some { target := 498, numerator := 12826046876129019017360834560 }, some { target := 499, numerator := 240396764306875327868248784896 }, some { target := 500, numerator := 13558963840479248675495739392 }, some { target := 501, numerator := 13925422322654363504563191808 }, some { target := 502, numerator := 13925422322654363504563191808 }, some { target := 503, numerator := 13558963840479248675495739392 }, some { target := 504, numerator := 420327879054856708940367921152 }, some { target := 505, numerator := 13558963840479248675495739392 }, some { target := 506, numerator := 17590007144405511795237715968 }, some { target := 507, numerator := 17956465626580626624305168384 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 890, numerator := 148823608820205792792674304 }, some { target := 891, numerator := 111617706615154344594505728 }, some { target := 892, numerator := 117818690315996252627533824 }, some { target := 893, numerator := 151924100670626746809188352 }, some { target := 894, numerator := 2033922653876145834833215488 }, some { target := 895, numerator := 3556264152432834256941613056 }, some { target := 896, numerator := 108517214764733390577991680 }, some { target := 897, numerator := 2033922653876145834833215488 }, some { target := 898, numerator := 114718198465575298611019776 }, some { target := 899, numerator := 117818690315996252627533824 }, some { target := 900, numerator := 117818690315996252627533824 }, some { target := 901, numerator := 114718198465575298611019776 }, some { target := 902, numerator := 3556264152432834256941613056 }, some { target := 903, numerator := 114718198465575298611019776 }, some { target := 904, numerator := 148823608820205792792674304 }, some { target := 905, numerator := 151924100670626746809188352 }]

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

end Slot6

namespace Slot7

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨7, 214, #[3298534883328, 2473901162496, 2611340115968, 3367254360064, 45079976738816, 78821239816192, 2405181685760, 45079976738816, 2542620639232, 2611340115968, 2611340115968, 2542620639232, 78821239816192, 2542620639232, 3298534883328, 3367254360064, 0, 0, 0], #[206963736576, 24461784907776, 0, 232137462644736, 0, 0, 0, 0, 0, 0, 0, 24461801684992, 0, 0, 0, 0, 0, 0, 206963736576]⟩

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
  [some { target := 121, numerator := 146092900401486420447854592 }, some { target := 122, numerator := 17267242876927825431591124992 }, some { target := 124, numerator := 163862692907835215095699341312 }, some { target := 132, numerator := 17267254719737520753123262464 }, some { target := 139, numerator := 146092900401486420447854592 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 196, numerator := 109569675301114815335890944 }, some { target := 197, numerator := 12950432157695869073693343744 }, some { target := 199, numerator := 122897019680876411321774505984 }, some { target := 207, numerator := 12950441039803140564842446848 }, some { target := 214, numerator := 109569675301114815335890944 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 231, numerator := 115656879484510082854551552 }, some { target := 232, numerator := 13669900610901195133342973952 }, some { target := 234, numerator := 129724631885369545284095311872 }, some { target := 242, numerator := 13669909986458870596222582784 }, some { target := 249, numerator := 115656879484510082854551552 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 337, numerator := 149136502493184054207184896 }, some { target := 338, numerator := 17626977103530488461415940096 }, some { target := 340, numerator := 167276499010081782076859744256 }, some { target := 348, numerator := 17626989193065385768813330432 }, some { target := 355, numerator := 149136502493184054207184896 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 412, numerator := 1996602972153647746120679424 }, some { target := 413, numerator := 235985652651346947565078708224 }, some { target := 415, numerator := 2239456803073747939641224331264 }, some { target := 423, numerator := 235985814503079450292684587008 }, some { target := 430, numerator := 1996602972153647746120679424 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 447, numerator := 3491011599177185921951858688 }, some { target := 448, numerator := 412615157913254495209062924288 }, some { target := 450, numerator := 3915635599276812327390982176768 }, some { target := 458, numerator := 412615440907061172996507959296 }, some { target := 465, numerator := 3491011599177185921951858688 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 508, numerator := 106526073209417181576560640 }, some { target := 509, numerator := 12590697931093206043868528640 }, some { target := 511, numerator := 119483213578629844340614103040 }, some { target := 519, numerator := 12590706566475275549152378880 }, some { target := 526, numerator := 106526073209417181576560640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 543, numerator := 1996602972153647746120679424 }, some { target := 544, numerator := 235985652651346947565078708224 }, some { target := 546, numerator := 2239456803073747939641224331264 }, some { target := 554, numerator := 235985814503079450292684587008 }, some { target := 561, numerator := 1996602972153647746120679424 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 578, numerator := 112613277392812449095221248 }, some { target := 579, numerator := 13310166384298532103518158848 }, some { target := 581, numerator := 126310825783122978302934908928 }, some { target := 589, numerator := 13310175513131005580532514816 }, some { target := 596, numerator := 112613277392812449095221248 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 679, numerator := 115656879484510082854551552 }, some { target := 680, numerator := 13669900610901195133342973952 }, some { target := 682, numerator := 129724631885369545284095311872 }, some { target := 690, numerator := 13669909986458870596222582784 }, some { target := 697, numerator := 115656879484510082854551552 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 714, numerator := 115656879484510082854551552 }, some { target := 715, numerator := 13669900610901195133342973952 }, some { target := 717, numerator := 129724631885369545284095311872 }, some { target := 725, numerator := 13669909986458870596222582784 }, some { target := 732, numerator := 115656879484510082854551552 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 775, numerator := 112613277392812449095221248 }, some { target := 776, numerator := 13310166384298532103518158848 }, some { target := 778, numerator := 126310825783122978302934908928 }, some { target := 786, numerator := 13310175513131005580532514816 }, some { target := 793, numerator := 112613277392812449095221248 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 810, numerator := 3491011599177185921951858688 }, some { target := 811, numerator := 412615157913254495209062924288 }, some { target := 813, numerator := 3915635599276812327390982176768 }, some { target := 821, numerator := 412615440907061172996507959296 }, some { target := 828, numerator := 3491011599177185921951858688 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 845, numerator := 112613277392812449095221248 }, some { target := 846, numerator := 13310166384298532103518158848 }, some { target := 848, numerator := 126310825783122978302934908928 }, some { target := 856, numerator := 13310175513131005580532514816 }, some { target := 863, numerator := 112613277392812449095221248 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 906, numerator := 146092900401486420447854592 }, some { target := 907, numerator := 17267242876927825431591124992 }, some { target := 909, numerator := 163862692907835215095699341312 }, some { target := 917, numerator := 17267254719737520753123262464 }, some { target := 924, numerator := 146092900401486420447854592 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 941, numerator := 149136502493184054207184896 }, some { target := 942, numerator := 17626977103530488461415940096 }, some { target := 944, numerator := 167276499010081782076859744256 }, some { target := 952, numerator := 17626989193065385768813330432 }, some { target := 959, numerator := 149136502493184054207184896 }]

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

end Slot7

namespace Slot8

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨8, 30, #[3517964091392, 0, 137219541041152, 0, 0, 137219490709504, 0, 0, 0, 0, 0, 0, 3517980868608, 0, 0, 0, 0, 0, 0], #[2130303778816, 51608327028736, 39101382262784, 43568148250624, 2130303778816, 43568148250624, 43499428773888, 2130303778816, 51608327028736, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 10, numerator := 224829965928941207326556160 }, some { target := 11, numerator := 5446687239117253119427215360 }, some { target := 12, numerator := 4126717761727985386090659840 }, some { target := 13, numerator := 4598135432224152433710858240 }, some { target := 14, numerator := 224829965928941207326556160 }, some { target := 15, numerator := 4598135432224152433710858240 }, some { target := 16, numerator := 4590882852678057556055162880 }, some { target := 17, numerator := 224829965928941207326556160 }, some { target := 18, numerator := 5446687239117253119427215360 }, some { target := 19, numerator := 224829965928941207326556160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 55, numerator := 8769579204220899136855080960 }, some { target := 56, numerator := 212450128463545008121876316160 }, some { target := 57, numerator := 160964211845215858350662615040 }, some { target := 58, numerator := 179352039208904840411810365440 }, some { target := 59, numerator := 8769579204220899136855080960 }, some { target := 60, numerator := 179352039208904840411810365440 }, some { target := 61, numerator := 179069149557155779149331169280 }, some { target := 62, numerator := 8769579204220899136855080960 }, some { target := 63, numerator := 212450128463545008121876316160 }, some { target := 64, numerator := 8769579204220899136855080960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 144, numerator := 8769575987569901283752017920 }, some { target := 145, numerator := 212450050537580511745089208320 }, some { target := 146, numerator := 160964152804105607434028974080 }, some { target := 147, numerator := 179351973423203787545121914880 }, some { target := 148, numerator := 8769575987569901283752017920 }, some { target := 149, numerator := 179351973423203787545121914880 }, some { target := 150, numerator := 179069083875217661697258946560 }, some { target := 151, numerator := 8769575987569901283752017920 }, some { target := 152, numerator := 212450050537580511745089208320 }, some { target := 153, numerator := 8769575987569901283752017920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 482, numerator := 224831038145940491694243840 }, some { target := 483, numerator := 5446713214438751911689584640 }, some { target := 484, numerator := 4126737442098069024968540160 }, some { target := 485, numerator := 4598157360791170055940341760 }, some { target := 486, numerator := 224831038145940491694243840 }, some { target := 487, numerator := 4598157360791170055940341760 }, some { target := 488, numerator := 4590904746657430040079237120 }, some { target := 489, numerator := 224831038145940491694243840 }, some { target := 490, numerator := 5446713214438751911689584640 }, some { target := 491, numerator := 224831038145940491694243840 }]

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

end Slot8

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16.Parent2
