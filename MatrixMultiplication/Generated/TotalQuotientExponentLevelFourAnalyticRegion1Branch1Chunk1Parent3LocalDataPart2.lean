import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk1Parent3LocalDataBase

/-! Line-budgeted parent-local routing slots, part 2, for region 1, branch 1,
parent 8; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent3

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot8

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨8, 1, #[49882488373248, 0, 0, 181709966409728, 0, 49882521927680, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[70643622084608, 70437463654400, 69956427317248, 70437463654400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 1, numerator := 3523879657279584200539766784 }, some { target := 2, numerator := 3513595961781686581277491200 }, some { target := 3, numerator := 3489600672286592136332181504 }, some { target := 4, numerator := 3513595961781686581277491200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 51, numerator := 12836650196055638792810266624 }, some { target := 52, numerator := 12799189154627460858590003200 }, some { target := 53, numerator := 12711780057961712345409388544 }, some { target := 54, numerator := 12799189154627460858590003200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 140, numerator := 3523882027686197672217149440 }, some { target := 141, numerator := 3513598325270771025313792000 }, some { target := 142, numerator := 3489603019634775515872624640 }, some { target := 143, numerator := 3513598325270771025313792000 }]

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

end Slot8

namespace Slot9

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨9, 27, #[3434312892416, 0, 137303192240128, 0, 0, 137303158685696, 0, 0, 0, 0, 0, 0, 3434312892416, 0, 0, 0, 0, 0, 0], #[2130303778816, 52226802319360, 38620345925632, 43087111913472, 2130303778816, 43018392436736, 43774306680832, 2130303778816, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 10, numerator := 197535502773458415032205312 }, some { target := 11, numerator := 4842805874446077271757291520 }, some { target := 12, numerator := 3581127501893020298325786624 }, some { target := 13, numerator := 3995314846418013749199765504 }, some { target := 14, numerator := 197535502773458415032205312 }, some { target := 15, numerator := 3988942733425321542263242752 }, some { target := 16, numerator := 4059035976344935818564993024 }, some { target := 17, numerator := 197535502773458415032205312 }, some { target := 18, numerator := 4842805874446077271757291520 }, some { target := 19, numerator := 197535502773458415032205312 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 55, numerator := 7897432750361397894731268096 }, some { target := 56, numerator := 193614480331440722580508508160 }, some { target := 57, numerator := 143172813087196955381902344192 }, some { target := 58, numerator := 159731946273438596128919519232 }, some { target := 59, numerator := 7897432750361397894731268096 }, some { target := 60, numerator := 159477190378265647809734639616 }, some { target := 61, numerator := 162279505225168079320768315392 }, some { target := 62, numerator := 7897432750361397894731268096 }, some { target := 63, numerator := 193614480331440722580508508160 }, some { target := 64, numerator := 7897432750361397894731268096 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 144, numerator := 7897430820370799182869430272 }, some { target := 145, numerator := 193614433015542173515508613120 }, some { target := 146, numerator := 143172778098335133573310316544 }, some { target := 147, numerator := 159731907237822293150294605824 }, some { target := 148, numerator := 7897430820370799182869430272 }, some { target := 149, numerator := 159477151404907106079879462912 }, some { target := 150, numerator := 162279465566974163854446034944 }, some { target := 151, numerator := 7897430820370799182869430272 }, some { target := 152, numerator := 193614433015542173515508613120 }, some { target := 153, numerator := 7897430820370799182869430272 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 482, numerator := 197535502773458415032205312 }, some { target := 483, numerator := 4842805874446077271757291520 }, some { target := 484, numerator := 3581127501893020298325786624 }, some { target := 485, numerator := 3995314846418013749199765504 }, some { target := 486, numerator := 197535502773458415032205312 }, some { target := 487, numerator := 3988942733425321542263242752 }, some { target := 488, numerator := 4059035976344935818564993024 }, some { target := 489, numerator := 197535502773458415032205312 }, some { target := 490, numerator := 4842805874446077271757291520 }, some { target := 491, numerator := 197535502773458415032205312 }]

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

end Slot9

namespace Slot10

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨10, 229, #[139552882688, 22870029762560, 0, 235455811420160, 0, 0, 0, 0, 0, 0, 0, 22870029762560, 0, 0, 0, 0, 0, 0, 139552882688], #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0]⟩

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
  [some { target := 34, numerator := 103217181573666503114358784 }, some { target := 35, numerator := 76863858618687821468139520 }, some { target := 36, numerator := 81256079111184268409176064 }, some { target := 37, numerator := 105413291819914726584877056 }, some { target := 38, numerator := 1412098888337607691543248896 }, some { target := 39, numerator := 2554076216386683896212750336 }, some { target := 40, numerator := 76863858618687821468139520 }, some { target := 41, numerator := 1412098888337607691543248896 }, some { target := 42, numerator := 83452189357432491879694336 }, some { target := 43, numerator := 83452189357432491879694336 }, some { target := 44, numerator := 81256079111184268409176064 }, some { target := 45, numerator := 81256079111184268409176064 }, some { target := 46, numerator := 2554076216386683896212750336 }, some { target := 47, numerator := 81256079111184268409176064 }, some { target := 48, numerator := 103217181573666503114358784 }, some { target := 49, numerator := 105413291819914726584877056 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 79, numerator := 16915308155080455684704174080 }, some { target := 80, numerator := 12596506072932254233290342400 }, some { target := 81, numerator := 13316306419956954475192647680 }, some { target := 82, numerator := 17275208328592805805655326720 }, some { target := 83, numerator := 231415811568441127771591147520 }, some { target := 84, numerator := 418563901794863190666190520320 }, some { target := 85, numerator := 12596506072932254233290342400 }, some { target := 86, numerator := 231415811568441127771591147520 }, some { target := 87, numerator := 13676206593469304596143800320 }, some { target := 88, numerator := 13676206593469304596143800320 }, some { target := 89, numerator := 13316306419956954475192647680 }, some { target := 90, numerator := 13316306419956954475192647680 }, some { target := 91, numerator := 418563901794863190666190520320 }, some { target := 92, numerator := 13316306419956954475192647680 }, some { target := 93, numerator := 16915308155080455684704174080 }, some { target := 94, numerator := 17275208328592805805655326720 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 154, numerator := 174149646870887816542164090880 }, some { target := 155, numerator := 129685907244278161254803046400 }, some { target := 156, numerator := 137096530515379770469363220480 }, some { target := 157, numerator := 177854958506438621149444177920 }, some { target := 158, numerator := 2382515381659167362481095966720 }, some { target := 159, numerator := 4309277432145585758266741227520 }, some { target := 160, numerator := 129685907244278161254803046400 }, some { target := 161, numerator := 2382515381659167362481095966720 }, some { target := 162, numerator := 140801842150930575076643307520 }, some { target := 163, numerator := 140801842150930575076643307520 }, some { target := 164, numerator := 137096530515379770469363220480 }, some { target := 165, numerator := 137096530515379770469363220480 }, some { target := 166, numerator := 4309277432145585758266741227520 }, some { target := 167, numerator := 137096530515379770469363220480 }, some { target := 168, numerator := 174149646870887816542164090880 }, some { target := 169, numerator := 177854958506438621149444177920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 492, numerator := 16915308155080455684704174080 }, some { target := 493, numerator := 12596506072932254233290342400 }, some { target := 494, numerator := 13316306419956954475192647680 }, some { target := 495, numerator := 17275208328592805805655326720 }, some { target := 496, numerator := 231415811568441127771591147520 }, some { target := 497, numerator := 418563901794863190666190520320 }, some { target := 498, numerator := 12596506072932254233290342400 }, some { target := 499, numerator := 231415811568441127771591147520 }, some { target := 500, numerator := 13676206593469304596143800320 }, some { target := 501, numerator := 13676206593469304596143800320 }, some { target := 502, numerator := 13316306419956954475192647680 }, some { target := 503, numerator := 13316306419956954475192647680 }, some { target := 504, numerator := 418563901794863190666190520320 }, some { target := 505, numerator := 13316306419956954475192647680 }, some { target := 506, numerator := 16915308155080455684704174080 }, some { target := 507, numerator := 17275208328592805805655326720 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 890, numerator := 103217181573666503114358784 }, some { target := 891, numerator := 76863858618687821468139520 }, some { target := 892, numerator := 81256079111184268409176064 }, some { target := 893, numerator := 105413291819914726584877056 }, some { target := 894, numerator := 1412098888337607691543248896 }, some { target := 895, numerator := 2554076216386683896212750336 }, some { target := 896, numerator := 76863858618687821468139520 }, some { target := 897, numerator := 1412098888337607691543248896 }, some { target := 898, numerator := 83452189357432491879694336 }, some { target := 899, numerator := 83452189357432491879694336 }, some { target := 900, numerator := 81256079111184268409176064 }, some { target := 901, numerator := 81256079111184268409176064 }, some { target := 902, numerator := 2554076216386683896212750336 }, some { target := 903, numerator := 81256079111184268409176064 }, some { target := 904, numerator := 103217181573666503114358784 }, some { target := 905, numerator := 105413291819914726584877056 }]

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

end Slot10

namespace Slot11

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨11, 126, #[706035580928, 140031452774400, 0, 0, 0, 0, 140031452774400, 0, 0, 0, 0, 0, 0, 0, 706035580928, 0, 0, 0, 0], #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416]⟩

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
  [some { target := 121, numerator := 36679907132847675616002048 }, some { target := 122, numerator := 531858653426291296432029696 }, some { target := 123, numerator := 941450949743090340810719232 }, some { target := 124, numerator := 30566589277373063013335040 }, some { target := 125, numerator := 586878514125562809856032768 }, some { target := 126, numerator := 30566589277373063013335040 }, some { target := 127, numerator := 935337631887615728208052224 }, some { target := 128, numerator := 978130856875938016426721280 }, some { target := 129, numerator := 586878514125562809856032768 }, some { target := 130, numerator := 14983742063768275489136836608 }, some { target := 131, numerator := 959790903309514178618720256 }, some { target := 132, numerator := 531858653426291296432029696 }, some { target := 133, numerator := 935337631887615728208052224 }, some { target := 134, numerator := 30566589277373063013335040 }, some { target := 135, numerator := 959790903309514178618720256 }, some { target := 136, numerator := 30566589277373063013335040 }, some { target := 137, numerator := 935337631887615728208052224 }, some { target := 138, numerator := 978130856875938016426721280 }, some { target := 139, numerator := 36679907132847675616002048 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 196, numerator := 7274903449896429573006950400 }, some { target := 197, numerator := 105486100023498228808600780800 }, some { target := 198, numerator := 186722521880675025707178393600 }, some { target := 199, numerator := 6062419541580357977505792000 }, some { target := 200, numerator := 116398455198342873168111206400 }, some { target := 201, numerator := 6062419541580357977505792000 }, some { target := 202, numerator := 185510037972358954111677235200 }, some { target := 203, numerator := 193997425330571455280185344000 }, some { target := 204, numerator := 116398455198342873168111206400 }, some { target := 205, numerator := 2971798059282691480573339238400 }, some { target := 206, numerator := 190359973605623240493681868800 }, some { target := 207, numerator := 105486100023498228808600780800 }, some { target := 208, numerator := 185510037972358954111677235200 }, some { target := 209, numerator := 6062419541580357977505792000 }, some { target := 210, numerator := 190359973605623240493681868800 }, some { target := 211, numerator := 6062419541580357977505792000 }, some { target := 212, numerator := 185510037972358954111677235200 }, some { target := 213, numerator := 193997425330571455280185344000 }, some { target := 214, numerator := 7274903449896429573006950400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 508, numerator := 7274903449896429573006950400 }, some { target := 509, numerator := 105486100023498228808600780800 }, some { target := 510, numerator := 186722521880675025707178393600 }, some { target := 511, numerator := 6062419541580357977505792000 }, some { target := 512, numerator := 116398455198342873168111206400 }, some { target := 513, numerator := 6062419541580357977505792000 }, some { target := 514, numerator := 185510037972358954111677235200 }, some { target := 515, numerator := 193997425330571455280185344000 }, some { target := 516, numerator := 116398455198342873168111206400 }, some { target := 517, numerator := 2971798059282691480573339238400 }, some { target := 518, numerator := 190359973605623240493681868800 }, some { target := 519, numerator := 105486100023498228808600780800 }, some { target := 520, numerator := 185510037972358954111677235200 }, some { target := 521, numerator := 6062419541580357977505792000 }, some { target := 522, numerator := 190359973605623240493681868800 }, some { target := 523, numerator := 6062419541580357977505792000 }, some { target := 524, numerator := 185510037972358954111677235200 }, some { target := 525, numerator := 193997425330571455280185344000 }, some { target := 526, numerator := 7274903449896429573006950400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 906, numerator := 36679907132847675616002048 }, some { target := 907, numerator := 531858653426291296432029696 }, some { target := 908, numerator := 941450949743090340810719232 }, some { target := 909, numerator := 30566589277373063013335040 }, some { target := 910, numerator := 586878514125562809856032768 }, some { target := 911, numerator := 30566589277373063013335040 }, some { target := 912, numerator := 935337631887615728208052224 }, some { target := 913, numerator := 978130856875938016426721280 }, some { target := 914, numerator := 586878514125562809856032768 }, some { target := 915, numerator := 14983742063768275489136836608 }, some { target := 916, numerator := 959790903309514178618720256 }, some { target := 917, numerator := 531858653426291296432029696 }, some { target := 918, numerator := 935337631887615728208052224 }, some { target := 919, numerator := 30566589277373063013335040 }, some { target := 920, numerator := 959790903309514178618720256 }, some { target := 921, numerator := 30566589277373063013335040 }, some { target := 922, numerator := 935337631887615728208052224 }, some { target := 923, numerator := 978130856875938016426721280 }, some { target := 924, numerator := 36679907132847675616002048 }]

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
def data : BetaFourLocalSlotData := ⟨12, 3, #[5963008442368, 0, 269517133447168, 0, 0, 0, 0, 5994834821120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2130303778816, 2405181685760, 2061584302080, 27144193310720, 2405181685760, 2061584302080, 2405181685760, 2405181685760, 99711960743936, 2473901162496, 27144193310720, 99711960743936, 2130303778816, 2405181685760, 2473901162496, 2405181685760, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

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
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 250, numerator := 38109058253664781665828864 }, some { target := 251, numerator := 43026356092847334138839040 }, some { target := 252, numerator := 36879733793869143547576320 }, some { target := 253, numerator := 485583161619277056709754880 }, some { target := 254, numerator := 43026356092847334138839040 }, some { target := 255, numerator := 36879733793869143547576320 }, some { target := 256, numerator := 43026356092847334138839040 }, some { target := 257, numerator := 43026356092847334138839040 }, some { target := 258, numerator := 1783749791163470909584441344 }, some { target := 259, numerator := 44255680552642972257091584 }, some { target := 260, numerator := 485583161619277056709754880 }, some { target := 261, numerator := 1783749791163470909584441344 }, some { target := 262, numerator := 38109058253664781665828864 }, some { target := 263, numerator := 43026356092847334138839040 }, some { target := 264, numerator := 44255680552642972257091584 }, some { target := 265, numerator := 43026356092847334138839040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 562, numerator := 1722460103514474404080779264 }, some { target := 563, numerator := 1944713020096987230413783040 }, some { target := 564, numerator := 1666896874368846197497528320 }, some { target := 565, numerator := 21947475512523141600384122880 }, some { target := 566, numerator := 1944713020096987230413783040 }, some { target := 567, numerator := 1666896874368846197497528320 }, some { target := 568, numerator := 1944713020096987230413783040 }, some { target := 569, numerator := 1944713020096987230413783040 }, some { target := 570, numerator := 80622245490306527752297119744 }, some { target := 571, numerator := 2000276249242615436997033984 }, some { target := 572, numerator := 21947475512523141600384122880 }, some { target := 573, numerator := 80622245490306527752297119744 }, some { target := 574, numerator := 1722460103514474404080779264 }, some { target := 575, numerator := 1944713020096987230413783040 }, some { target := 576, numerator := 2000276249242615436997033984 }, some { target := 577, numerator := 1944713020096987230413783040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 925, numerator := 38312457818429026216181760 }, some { target := 926, numerator := 43256000762742448953753600 }, some { target := 927, numerator := 37076572082350670531788800 }, some { target := 928, numerator := 488174865750950495335219200 }, some { target := 929, numerator := 43256000762742448953753600 }, some { target := 930, numerator := 37076572082350670531788800 }, some { target := 931, numerator := 43256000762742448953753600 }, some { target := 932, numerator := 43256000762742448953753600 }, some { target := 933, numerator := 1793270203049694098054184960 }, some { target := 934, numerator := 44491886498820804638146560 }, some { target := 935, numerator := 488174865750950495335219200 }, some { target := 936, numerator := 1793270203049694098054184960 }, some { target := 937, numerator := 38312457818429026216181760 }, some { target := 938, numerator := 43256000762742448953753600 }, some { target := 939, numerator := 44491886498820804638146560 }, some { target := 940, numerator := 43256000762742448953753600 }]

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

end Slot12

namespace Slot13

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨13, 0, #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1649267441664, 34428457844736, 1786706395136, 37039797960704, 55456617725952, 1717986918400, 55456617725952, 57793079934976, 34428457844736, 1717986918400, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot13

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1.Parent3
