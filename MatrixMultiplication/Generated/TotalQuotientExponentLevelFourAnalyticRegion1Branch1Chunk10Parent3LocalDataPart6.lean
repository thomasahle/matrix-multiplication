import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk10Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 6, for region 1, branch 1,
parent 45; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot24

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨24, 27, #[140737505132544, 0, 140737471578112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2130303778816, 52226802319360, 38620345925632, 43087111913472, 2130303778816, 43018392436736, 43774306680832, 2130303778816, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 4, numerator := 8094968253134856309763473408 }, some { target := 5, numerator := 198457286205886799852265799680 }, some { target := 6, numerator := 146753940589089975680228130816 }, some { target := 7, numerator := 163727261119856609878119284736 }, some { target := 8, numerator := 8094968253134856309763473408 }, some { target := 9, numerator := 163466133111690969351997882368 }, some { target := 10, numerator := 166338541201513015139333308416 }, some { target := 11, numerator := 8094968253134856309763473408 }, some { target := 12, numerator := 198457286205886799852265799680 }, some { target := 13, numerator := 8094968253134856309763473408 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 126, numerator := 8094966323144257597901635584 }, some { target := 127, numerator := 198457238889988250787265904640 }, some { target := 128, numerator := 146753905600228153871636103168 }, some { target := 129, numerator := 163727222084240306899494371328 }, some { target := 130, numerator := 8094966323144257597901635584 }, some { target := 131, numerator := 163466094138332427622142705664 }, some { target := 132, numerator := 166338501543319099673011027968 }, some { target := 133, numerator := 8094966323144257597901635584 }, some { target := 134, numerator := 198457238889988250787265904640 }, some { target := 135, numerator := 8094966323144257597901635584 }]

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

end Slot24

namespace Slot25

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨25, 418, #[50290594152448, 0, 0, 180893771628544, 0, 50290610929664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0]⟩

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
  [some { target := 14, numerator := 67895462364501195606393356288 }, some { target := 15, numerator := 50560450696968975451569520640 }, some { target := 16, numerator := 53449619308224345477373493248 }, some { target := 17, numerator := 69340046670128880619295342592 }, some { target := 18, numerator := 928867708518601463295977193472 }, some { target := 19, numerator := 1680051547444997670005010071552 }, some { target := 20, numerator := 50560450696968975451569520640 }, some { target := 21, numerator := 928867708518601463295977193472 }, some { target := 22, numerator := 54894203613852030490275479552 }, some { target := 23, numerator := 54894203613852030490275479552 }, some { target := 24, numerator := 53449619308224345477373493248 }, some { target := 25, numerator := 53449619308224345477373493248 }, some { target := 26, numerator := 1680051547444997670005010071552 }, some { target := 27, numerator := 53449619308224345477373493248 }, some { target := 28, numerator := 67895462364501195606393356288 }, some { target := 29, numerator := 69340046670128880619295342592 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 136, numerator := 244217959055085805541538136064 }, some { target := 137, numerator := 181864437594212833913911377920 }, some { target := 138, numerator := 192256691171024995851849170944 }, some { target := 139, numerator := 249414085843491886510507032576 }, some { target := 140, numerator := 3341109524945110063047000457216 }, some { target := 141, numerator := 6043095454916272166910826643456 }, some { target := 142, numerator := 181864437594212833913911377920 }, some { target := 143, numerator := 3341109524945110063047000457216 }, some { target := 144, numerator := 197452817959431076820818067456 }, some { target := 145, numerator := 197452817959431076820818067456 }, some { target := 146, numerator := 192256691171024995851849170944 }, some { target := 147, numerator := 192256691171024995851849170944 }, some { target := 148, numerator := 6043095454916272166910826643456 }, some { target := 149, numerator := 192256691171024995851849170944 }, some { target := 150, numerator := 244217959055085805541538136064 }, some { target := 151, numerator := 249414085843491886510507032576 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 67895485014797075112509046784 }, some { target := 268, numerator := 50560467564210587849740779520 }, some { target := 269, numerator := 53449637139308335726868824064 }, some { target := 270, numerator := 69340069802345949051073069056 }, some { target := 271, numerator := 928868018393925942496666320896 }, some { target := 272, numerator := 1680052107919340390549957902336 }, some { target := 273, numerator := 50560467564210587849740779520 }, some { target := 274, numerator := 928868018393925942496666320896 }, some { target := 275, numerator := 54894221926857209665432846336 }, some { target := 276, numerator := 54894221926857209665432846336 }, some { target := 277, numerator := 53449637139308335726868824064 }, some { target := 278, numerator := 53449637139308335726868824064 }, some { target := 279, numerator := 1680052107919340390549957902336 }, some { target := 280, numerator := 53449637139308335726868824064 }, some { target := 281, numerator := 67895485014797075112509046784 }, some { target := 282, numerator := 69340069802345949051073069056 }]

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
def data : BetaFourLocalSlotData := ⟨26, 926, #[3517964091392, 0, 137219541041152, 0, 0, 137219490709504, 0, 0, 0, 0, 0, 0, 3517980868608, 0, 0, 0, 0, 0, 0], #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416]⟩

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
  [some { target := 56, numerator := 1343177731936771341834780672 }, some { target := 57, numerator := 19476077113083184456604319744 }, some { target := 58, numerator := 34474895119710464440426037248 }, some { target := 59, numerator := 1119314776613976118195650560 }, some { target := 60, numerator := 21490843710988341469356490752 }, some { target := 61, numerator := 1119314776613976118195650560 }, some { target := 62, numerator := 34251032164387669216786907136 }, some { target := 63, numerator := 35818072851647235782260817920 }, some { target := 64, numerator := 21490843710988341469356490752 }, some { target := 65, numerator := 548688103496171093139507904512 }, some { target := 66, numerator := 35146483985678850111343427584 }, some { target := 67, numerator := 19476077113083184456604319744 }, some { target := 68, numerator := 34251032164387669216786907136 }, some { target := 69, numerator := 1119314776613976118195650560 }, some { target := 70, numerator := 35146483985678850111343427584 }, some { target := 71, numerator := 1119314776613976118195650560 }, some { target := 72, numerator := 34251032164387669216786907136 }, some { target := 73, numerator := 35818072851647235782260817920 }, some { target := 74, numerator := 1343177731936771341834780672 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 152, numerator := 52391163503926145811147128832 }, some { target := 153, numerator := 759671870806929114261633368064 }, some { target := 154, numerator := 1344706529934104409152776306688 }, some { target := 155, numerator := 43659302919938454842622607360 }, some { target := 156, numerator := 838258616062818332978354061312 }, some { target := 157, numerator := 43659302919938454842622607360 }, some { target := 158, numerator := 1335974669350116718184251785216 }, some { target := 159, numerator := 1397097693438030554963923435520 }, some { target := 160, numerator := 838258616062818332978354061312 }, some { target := 161, numerator := 21401790291353830563853602127872 }, some { target := 162, numerator := 1370902111686067482058349871104 }, some { target := 163, numerator := 759671870806929114261633368064 }, some { target := 164, numerator := 1335974669350116718184251785216 }, some { target := 165, numerator := 43659302919938454842622607360 }, some { target := 166, numerator := 1370902111686067482058349871104 }, some { target := 167, numerator := 43659302919938454842622607360 }, some { target := 168, numerator := 1335974669350116718184251785216 }, some { target := 169, numerator := 1397097693438030554963923435520 }, some { target := 170, numerator := 52391163503926145811147128832 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 283, numerator := 52391144287030507024221732864 }, some { target := 284, numerator := 759671592161942351851215126528 }, some { target := 285, numerator := 1344706036700449680288357810176 }, some { target := 286, numerator := 43659286905858755853518110720 }, some { target := 287, numerator := 838258308592488112387547725824 }, some { target := 288, numerator := 43659286905858755853518110720 }, some { target := 289, numerator := 1335974179319277929117654188032 }, some { target := 290, numerator := 1397097180987480187312579543040 }, some { target := 291, numerator := 838258308592488112387547725824 }, some { target := 292, numerator := 21401782441251962119394577874944 }, some { target := 293, numerator := 1370901608843964933800468676608 }, some { target := 294, numerator := 759671592161942351851215126528 }, some { target := 295, numerator := 1335974179319277929117654188032 }, some { target := 296, numerator := 43659286905858755853518110720 }, some { target := 297, numerator := 1370901608843964933800468676608 }, some { target := 298, numerator := 43659286905858755853518110720 }, some { target := 299, numerator := 1335974179319277929117654188032 }, some { target := 300, numerator := 1397097180987480187312579543040 }, some { target := 301, numerator := 52391144287030507024221732864 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 660, numerator := 1343184137568650937476579328 }, some { target := 661, numerator := 19476169994745438593410400256 }, some { target := 662, numerator := 34475059530928707395232202752 }, some { target := 663, numerator := 1119320114640542447897149440 }, some { target := 664, numerator := 21490946201098414999625269248 }, some { target := 665, numerator := 1119320114640542447897149440 }, some { target := 666, numerator := 34251195508000598905652772864 }, some { target := 667, numerator := 35818243668497358332708782080 }, some { target := 668, numerator := 21490946201098414999625269248 }, some { target := 669, numerator := 548690720196793907959182655488 }, some { target := 670, numerator := 35146651599713032863970492416 }, some { target := 671, numerator := 19476169994745438593410400256 }, some { target := 672, numerator := 34251195508000598905652772864 }, some { target := 673, numerator := 1119320114640542447897149440 }, some { target := 674, numerator := 35146651599713032863970492416 }, some { target := 675, numerator := 1119320114640542447897149440 }, some { target := 676, numerator := 34251195508000598905652772864 }, some { target := 677, numerator := 35818243668497358332708782080 }, some { target := 678, numerator := 1343184137568650937476579328 }]

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

end Slot26

namespace Slot27

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨27, 66, #[412316860416, 6184752906240, 10857677324288, 412316860416, 6871947673600, 412316860416, 10857677324288, 10788957847552, 6871947673600, 166507292131328, 10651518894080, 6184752906240, 10857677324288, 412316860416, 10651518894080, 412316860416, 10857677324288, 10857677324288, 412316860416], #[2130303778816, 2405181685760, 2061584302080, 27144193310720, 2405181685760, 2061584302080, 2405181685760, 2405181685760, 99711960743936, 2473901162496, 27144193310720, 99711960743936, 2130303778816, 2405181685760, 2473901162496, 2405181685760, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

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
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 110, numerator := 57971770943707764643332096 }, some { target := 111, numerator := 65451999452573282661826560 }, some { target := 112, numerator := 56101713816491385138708480 }, some { target := 113, numerator := 738672565250469904326328320 }, some { target := 114, numerator := 65451999452573282661826560 }, some { target := 115, numerator := 56101713816491385138708480 }, some { target := 116, numerator := 65451999452573282661826560 }, some { target := 117, numerator := 65451999452573282661826560 }, some { target := 118, numerator := 2713452891590966661208866816 }, some { target := 119, numerator := 67322056579789662166450176 }, some { target := 120, numerator := 738672565250469904326328320 }, some { target := 121, numerator := 2713452891590966661208866816 }, some { target := 122, numerator := 57971770943707764643332096 }, some { target := 123, numerator := 65451999452573282661826560 }, some { target := 124, numerator := 67322056579789662166450176 }, some { target := 125, numerator := 65451999452573282661826560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 206, numerator := 869576564155616469649981440 }, some { target := 207, numerator := 981779991788599239927398400 }, some { target := 208, numerator := 841525707247370777080627200 }, some { target := 209, numerator := 11080088478757048564894924800 }, some { target := 210, numerator := 981779991788599239927398400 }, some { target := 211, numerator := 841525707247370777080627200 }, some { target := 212, numerator := 981779991788599239927398400 }, some { target := 213, numerator := 981779991788599239927398400 }, some { target := 214, numerator := 40701793373864499918133002240 }, some { target := 215, numerator := 1009830848696844932496752640 }, some { target := 216, numerator := 11080088478757048564894924800 }, some { target := 217, numerator := 40701793373864499918133002240 }, some { target := 218, numerator := 869576564155616469649981440 }, some { target := 219, numerator := 981779991788599239927398400 }, some { target := 220, numerator := 1009830848696844932496752640 }, some { target := 221, numerator := 981779991788599239927398400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 241, numerator := 1526589968184304468941078528 }, some { target := 242, numerator := 1723569318917763110094766080 }, some { target := 243, numerator := 1477345130500939808652656640 }, some { target := 244, numerator := 19451710884929040813926645760 }, some { target := 245, numerator := 1723569318917763110094766080 }, some { target := 246, numerator := 1477345130500939808652656640 }, some { target := 247, numerator := 1723569318917763110094766080 }, some { target := 248, numerator := 1723569318917763110094766080 }, some { target := 249, numerator := 71454259478562122078500159488 }, some { target := 250, numerator := 1772814156601127770383187968 }, some { target := 251, numerator := 19451710884929040813926645760 }, some { target := 252, numerator := 71454259478562122078500159488 }, some { target := 253, numerator := 1526589968184304468941078528 }, some { target := 254, numerator := 1723569318917763110094766080 }, some { target := 255, numerator := 1772814156601127770383187968 }, some { target := 256, numerator := 1723569318917763110094766080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 302, numerator := 57971770943707764643332096 }, some { target := 303, numerator := 65451999452573282661826560 }, some { target := 304, numerator := 56101713816491385138708480 }, some { target := 305, numerator := 738672565250469904326328320 }, some { target := 306, numerator := 65451999452573282661826560 }, some { target := 307, numerator := 56101713816491385138708480 }, some { target := 308, numerator := 65451999452573282661826560 }, some { target := 309, numerator := 65451999452573282661826560 }, some { target := 310, numerator := 2713452891590966661208866816 }, some { target := 311, numerator := 67322056579789662166450176 }, some { target := 312, numerator := 738672565250469904326328320 }, some { target := 313, numerator := 2713452891590966661208866816 }, some { target := 314, numerator := 57971770943707764643332096 }, some { target := 315, numerator := 65451999452573282661826560 }, some { target := 316, numerator := 67322056579789662166450176 }, some { target := 317, numerator := 65451999452573282661826560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 337, numerator := 966196182395129410722201600 }, some { target := 338, numerator := 1090866657542888044363776000 }, some { target := 339, numerator := 935028563608189752311808000 }, some { target := 340, numerator := 12311209420841165072105472000 }, some { target := 341, numerator := 1090866657542888044363776000 }, some { target := 342, numerator := 935028563608189752311808000 }, some { target := 343, numerator := 1090866657542888044363776000 }, some { target := 344, numerator := 1090866657542888044363776000 }, some { target := 345, numerator := 45224214859849444353481113600 }, some { target := 346, numerator := 1122034276329827702774169600 }, some { target := 347, numerator := 12311209420841165072105472000 }, some { target := 348, numerator := 45224214859849444353481113600 }, some { target := 349, numerator := 966196182395129410722201600 }, some { target := 350, numerator := 1090866657542888044363776000 }, some { target := 351, numerator := 1122034276329827702774169600 }, some { target := 352, numerator := 1090866657542888044363776000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 363, numerator := 57971770943707764643332096 }, some { target := 364, numerator := 65451999452573282661826560 }, some { target := 365, numerator := 56101713816491385138708480 }, some { target := 366, numerator := 738672565250469904326328320 }, some { target := 367, numerator := 65451999452573282661826560 }, some { target := 368, numerator := 56101713816491385138708480 }, some { target := 369, numerator := 65451999452573282661826560 }, some { target := 370, numerator := 65451999452573282661826560 }, some { target := 371, numerator := 2713452891590966661208866816 }, some { target := 372, numerator := 67322056579789662166450176 }, some { target := 373, numerator := 738672565250469904326328320 }, some { target := 374, numerator := 2713452891590966661208866816 }, some { target := 375, numerator := 57971770943707764643332096 }, some { target := 376, numerator := 65451999452573282661826560 }, some { target := 377, numerator := 67322056579789662166450176 }, some { target := 378, numerator := 65451999452573282661826560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 473, numerator := 1526589968184304468941078528 }, some { target := 474, numerator := 1723569318917763110094766080 }, some { target := 475, numerator := 1477345130500939808652656640 }, some { target := 476, numerator := 19451710884929040813926645760 }, some { target := 477, numerator := 1723569318917763110094766080 }, some { target := 478, numerator := 1477345130500939808652656640 }, some { target := 479, numerator := 1723569318917763110094766080 }, some { target := 480, numerator := 1723569318917763110094766080 }, some { target := 481, numerator := 71454259478562122078500159488 }, some { target := 482, numerator := 1772814156601127770383187968 }, some { target := 483, numerator := 19451710884929040813926645760 }, some { target := 484, numerator := 71454259478562122078500159488 }, some { target := 485, numerator := 1526589968184304468941078528 }, some { target := 486, numerator := 1723569318917763110094766080 }, some { target := 487, numerator := 1772814156601127770383187968 }, some { target := 488, numerator := 1723569318917763110094766080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 508, numerator := 1516928006360353174833856512 }, some { target := 509, numerator := 1712660652342334229651128320 }, some { target := 510, numerator := 1467994844864857911129538560 }, some { target := 511, numerator := 19328598790720629163205591040 }, some { target := 512, numerator := 1712660652342334229651128320 }, some { target := 513, numerator := 1467994844864857911129538560 }, some { target := 514, numerator := 1712660652342334229651128320 }, some { target := 515, numerator := 1712660652342334229651128320 }, some { target := 516, numerator := 71002017329963627634965348352 }, some { target := 517, numerator := 1761593813837829493355446272 }, some { target := 518, numerator := 19328598790720629163205591040 }, some { target := 519, numerator := 71002017329963627634965348352 }, some { target := 520, numerator := 1516928006360353174833856512 }, some { target := 521, numerator := 1712660652342334229651128320 }, some { target := 522, numerator := 1761593813837829493355446272 }, some { target := 523, numerator := 1712660652342334229651128320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 569, numerator := 966196182395129410722201600 }, some { target := 570, numerator := 1090866657542888044363776000 }, some { target := 571, numerator := 935028563608189752311808000 }, some { target := 572, numerator := 12311209420841165072105472000 }, some { target := 573, numerator := 1090866657542888044363776000 }, some { target := 574, numerator := 935028563608189752311808000 }, some { target := 575, numerator := 1090866657542888044363776000 }, some { target := 576, numerator := 1090866657542888044363776000 }, some { target := 577, numerator := 45224214859849444353481113600 }, some { target := 578, numerator := 1122034276329827702774169600 }, some { target := 579, numerator := 12311209420841165072105472000 }, some { target := 580, numerator := 45224214859849444353481113600 }, some { target := 581, numerator := 966196182395129410722201600 }, some { target := 582, numerator := 1090866657542888044363776000 }, some { target := 583, numerator := 1122034276329827702774169600 }, some { target := 584, numerator := 1090866657542888044363776000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 604, numerator := 23410933499433985621798944768 }, some { target := 605, numerator := 26431699112264177314934292480 }, some { target := 606, numerator := 22655742096226437698515107840 }, some { target := 607, numerator := 298300604266981429697115586560 }, some { target := 608, numerator := 26431699112264177314934292480 }, some { target := 609, numerator := 22655742096226437698515107840 }, some { target := 610, numerator := 26431699112264177314934292480 }, some { target := 611, numerator := 26431699112264177314934292480 }, some { target := 612, numerator := 1095782726054152036684847382528 }, some { target := 613, numerator := 27186890515471725238218129408 }, some { target := 614, numerator := 298300604266981429697115586560 }, some { target := 615, numerator := 1095782726054152036684847382528 }, some { target := 616, numerator := 23410933499433985621798944768 }, some { target := 617, numerator := 26431699112264177314934292480 }, some { target := 618, numerator := 27186890515471725238218129408 }, some { target := 619, numerator := 26431699112264177314934292480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 630, numerator := 1497604082712450586619412480 }, some { target := 631, numerator := 1690843319191476468763852800 }, some { target := 632, numerator := 1449294273592694116083302400 }, some { target := 633, numerator := 19082374602303805861763481600 }, some { target := 634, numerator := 1690843319191476468763852800 }, some { target := 635, numerator := 1449294273592694116083302400 }, some { target := 636, numerator := 1690843319191476468763852800 }, some { target := 637, numerator := 1690843319191476468763852800 }, some { target := 638, numerator := 70097533032766638747895726080 }, some { target := 639, numerator := 1739153128311232939299962880 }, some { target := 640, numerator := 19082374602303805861763481600 }, some { target := 641, numerator := 70097533032766638747895726080 }, some { target := 642, numerator := 1497604082712450586619412480 }, some { target := 643, numerator := 1690843319191476468763852800 }, some { target := 644, numerator := 1739153128311232939299962880 }, some { target := 645, numerator := 1690843319191476468763852800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 679, numerator := 869576564155616469649981440 }, some { target := 680, numerator := 981779991788599239927398400 }, some { target := 681, numerator := 841525707247370777080627200 }, some { target := 682, numerator := 11080088478757048564894924800 }, some { target := 683, numerator := 981779991788599239927398400 }, some { target := 684, numerator := 841525707247370777080627200 }, some { target := 685, numerator := 981779991788599239927398400 }, some { target := 686, numerator := 981779991788599239927398400 }, some { target := 687, numerator := 40701793373864499918133002240 }, some { target := 688, numerator := 1009830848696844932496752640 }, some { target := 689, numerator := 11080088478757048564894924800 }, some { target := 690, numerator := 40701793373864499918133002240 }, some { target := 691, numerator := 869576564155616469649981440 }, some { target := 692, numerator := 981779991788599239927398400 }, some { target := 693, numerator := 1009830848696844932496752640 }, some { target := 694, numerator := 981779991788599239927398400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 705, numerator := 1526589968184304468941078528 }, some { target := 706, numerator := 1723569318917763110094766080 }, some { target := 707, numerator := 1477345130500939808652656640 }, some { target := 708, numerator := 19451710884929040813926645760 }, some { target := 709, numerator := 1723569318917763110094766080 }, some { target := 710, numerator := 1477345130500939808652656640 }, some { target := 711, numerator := 1723569318917763110094766080 }, some { target := 712, numerator := 1723569318917763110094766080 }, some { target := 713, numerator := 71454259478562122078500159488 }, some { target := 714, numerator := 1772814156601127770383187968 }, some { target := 715, numerator := 19451710884929040813926645760 }, some { target := 716, numerator := 71454259478562122078500159488 }, some { target := 717, numerator := 1526589968184304468941078528 }, some { target := 718, numerator := 1723569318917763110094766080 }, some { target := 719, numerator := 1772814156601127770383187968 }, some { target := 720, numerator := 1723569318917763110094766080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 785, numerator := 57971770943707764643332096 }, some { target := 786, numerator := 65451999452573282661826560 }, some { target := 787, numerator := 56101713816491385138708480 }, some { target := 788, numerator := 738672565250469904326328320 }, some { target := 789, numerator := 65451999452573282661826560 }, some { target := 790, numerator := 56101713816491385138708480 }, some { target := 791, numerator := 65451999452573282661826560 }, some { target := 792, numerator := 65451999452573282661826560 }, some { target := 793, numerator := 2713452891590966661208866816 }, some { target := 794, numerator := 67322056579789662166450176 }, some { target := 795, numerator := 738672565250469904326328320 }, some { target := 796, numerator := 2713452891590966661208866816 }, some { target := 797, numerator := 57971770943707764643332096 }, some { target := 798, numerator := 65451999452573282661826560 }, some { target := 799, numerator := 67322056579789662166450176 }, some { target := 800, numerator := 65451999452573282661826560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 820, numerator := 1497604082712450586619412480 }, some { target := 821, numerator := 1690843319191476468763852800 }, some { target := 822, numerator := 1449294273592694116083302400 }, some { target := 823, numerator := 19082374602303805861763481600 }, some { target := 824, numerator := 1690843319191476468763852800 }, some { target := 825, numerator := 1449294273592694116083302400 }, some { target := 826, numerator := 1690843319191476468763852800 }, some { target := 827, numerator := 1690843319191476468763852800 }, some { target := 828, numerator := 70097533032766638747895726080 }, some { target := 829, numerator := 1739153128311232939299962880 }, some { target := 830, numerator := 19082374602303805861763481600 }, some { target := 831, numerator := 70097533032766638747895726080 }, some { target := 832, numerator := 1497604082712450586619412480 }, some { target := 833, numerator := 1690843319191476468763852800 }, some { target := 834, numerator := 1739153128311232939299962880 }, some { target := 835, numerator := 1690843319191476468763852800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 846, numerator := 57971770943707764643332096 }, some { target := 847, numerator := 65451999452573282661826560 }, some { target := 848, numerator := 56101713816491385138708480 }, some { target := 849, numerator := 738672565250469904326328320 }, some { target := 850, numerator := 65451999452573282661826560 }, some { target := 851, numerator := 56101713816491385138708480 }, some { target := 852, numerator := 65451999452573282661826560 }, some { target := 853, numerator := 65451999452573282661826560 }, some { target := 854, numerator := 2713452891590966661208866816 }, some { target := 855, numerator := 67322056579789662166450176 }, some { target := 856, numerator := 738672565250469904326328320 }, some { target := 857, numerator := 2713452891590966661208866816 }, some { target := 858, numerator := 57971770943707764643332096 }, some { target := 859, numerator := 65451999452573282661826560 }, some { target := 860, numerator := 67322056579789662166450176 }, some { target := 861, numerator := 65451999452573282661826560 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 895, numerator := 1526589968184304468941078528 }, some { target := 896, numerator := 1723569318917763110094766080 }, some { target := 897, numerator := 1477345130500939808652656640 }, some { target := 898, numerator := 19451710884929040813926645760 }, some { target := 899, numerator := 1723569318917763110094766080 }, some { target := 900, numerator := 1477345130500939808652656640 }, some { target := 901, numerator := 1723569318917763110094766080 }, some { target := 902, numerator := 1723569318917763110094766080 }, some { target := 903, numerator := 71454259478562122078500159488 }, some { target := 904, numerator := 1772814156601127770383187968 }, some { target := 905, numerator := 19451710884929040813926645760 }, some { target := 906, numerator := 71454259478562122078500159488 }, some { target := 907, numerator := 1526589968184304468941078528 }, some { target := 908, numerator := 1723569318917763110094766080 }, some { target := 909, numerator := 1772814156601127770383187968 }, some { target := 910, numerator := 1723569318917763110094766080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 921, numerator := 1526589968184304468941078528 }, some { target := 922, numerator := 1723569318917763110094766080 }, some { target := 923, numerator := 1477345130500939808652656640 }, some { target := 924, numerator := 19451710884929040813926645760 }, some { target := 925, numerator := 1723569318917763110094766080 }, some { target := 926, numerator := 1477345130500939808652656640 }, some { target := 927, numerator := 1723569318917763110094766080 }, some { target := 928, numerator := 1723569318917763110094766080 }, some { target := 929, numerator := 71454259478562122078500159488 }, some { target := 930, numerator := 1772814156601127770383187968 }, some { target := 931, numerator := 19451710884929040813926645760 }, some { target := 932, numerator := 71454259478562122078500159488 }, some { target := 933, numerator := 1526589968184304468941078528 }, some { target := 934, numerator := 1723569318917763110094766080 }, some { target := 935, numerator := 1772814156601127770383187968 }, some { target := 936, numerator := 1723569318917763110094766080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 966, numerator := 57971770943707764643332096 }, some { target := 967, numerator := 65451999452573282661826560 }, some { target := 968, numerator := 56101713816491385138708480 }, some { target := 969, numerator := 738672565250469904326328320 }, some { target := 970, numerator := 65451999452573282661826560 }, some { target := 971, numerator := 56101713816491385138708480 }, some { target := 972, numerator := 65451999452573282661826560 }, some { target := 973, numerator := 65451999452573282661826560 }, some { target := 974, numerator := 2713452891590966661208866816 }, some { target := 975, numerator := 67322056579789662166450176 }, some { target := 976, numerator := 738672565250469904326328320 }, some { target := 977, numerator := 2713452891590966661208866816 }, some { target := 978, numerator := 57971770943707764643332096 }, some { target := 979, numerator := 65451999452573282661826560 }, some { target := 980, numerator := 67322056579789662166450176 }, some { target := 981, numerator := 65451999452573282661826560 }]

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

end Slot27

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10.Parent3
