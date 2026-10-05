import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk5Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 2, for region 1, branch 1,
parent 24; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot8

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨8, 9, #[3506505252864, 0, 137230932770816, 0, 0, 137230983102464, 0, 0, 0, 0, 0, 0, 3506555584512, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total8.codes

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
        8 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total8.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 0, numerator := 8882941359471185954189869056 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 6, numerator := 347643662450823295736337137664 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 27, numerator := 347643789954718333216757907456 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 148, numerator := 8883068863366223434610638848 }]

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

namespace Slot9

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨9, 7, #[69122129920, 22265714442240, 0, 236805236457472, 0, 0, 0, 0, 0, 0, 0, 22265781551104, 0, 0, 0, 0, 0, 0, 69122129920], #[70643622084608, 70437463654400, 69956427317248, 70437463654400, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

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
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 2, numerator := 34181263366261587857899520 }, some { target := 3, numerator := 34081512597683003457536000 }, some { target := 4, numerator := 33848760804332973190021120 }, some { target := 5, numerator := 34081512597683003457536000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 8, numerator := 11010515015509806725663293440 }, some { target := 9, numerator := 10978383162351704176852992000 }, some { target := 10, numerator := 10903408838316131562962288640 }, some { target := 11, numerator := 10978383162351704176852992000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 28, numerator := 117101457423705219428444536832 }, some { target := 29, numerator := 116759721653013472679139737600 }, some { target := 30, numerator := 115962338188066063597428539392 }, some { target := 31, numerator := 116759721653013472679139737600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 149, numerator := 11010548201202395329146650624 }, some { target := 150, numerator := 10978416251198886393361203200 }, some { target := 151, numerator := 10903441701190698876528492544 }, some { target := 152, numerator := 10978416251198886393361203200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 378, numerator := 34181263366261587857899520 }, some { target := 379, numerator := 34081512597683003457536000 }, some { target := 380, numerator := 33848760804332973190021120 }, some { target := 381, numerator := 34081512597683003457536000 }]

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

end Slot9

namespace Slot10

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨10, 6, #[797874061312, 139939614294016, 0, 0, 0, 0, 139939631071232, 0, 0, 0, 0, 0, 0, 0, 797857284096, 0, 0, 0, 0], #[2130303778816, 52226802319360, 38620345925632, 43087111913472, 2130303778816, 43018392436736, 43774306680832, 2130303778816, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

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
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 17, numerator := 10198284766993334824599552 }, some { target := 18, numerator := 250022465255320466667601920 }, some { target := 19, numerator := 184885033517750134562095104 }, some { target := 20, numerator := 206268533835639385000771584 }, some { target := 21, numerator := 10198284766993334824599552 }, some { target := 22, numerator := 205939556907671858070945792 }, some { target := 23, numerator := 209558303115314654299029504 }, some { target := 24, numerator := 10198284766993334824599552 }, some { target := 25, numerator := 250022465255320466667601920 }, some { target := 26, numerator := 10198284766993334824599552 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 37, numerator := 1788683334819574877138190336 }, some { target := 38, numerator := 43851591434286351826613698560 }, some { target := 39, numerator := 32427097876406486482311708672 }, some { target := 40, numerator := 36177562933286240256956301312 }, some { target := 41, numerator := 1788683334819574877138190336 }, some { target := 42, numerator := 36119863470872705583500230656 }, some { target := 43, numerator := 36754557557421586991517007872 }, some { target := 44, numerator := 1788683334819574877138190336 }, some { target := 45, numerator := 43851591434286351826613698560 }, some { target := 46, numerator := 1788683334819574877138190336 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 153, numerator := 1788683549262974734011727872 }, some { target := 154, numerator := 43851596691608412833835909120 }, some { target := 155, numerator := 32427101764057800016599711744 }, some { target := 156, numerator := 36177567270576940587914625024 }, some { target := 157, numerator := 1788683549262974734011727872 }, some { target := 158, numerator := 36119867801245876886817472512 }, some { target := 159, numerator := 36754561963887577598886150144 }, some { target := 160, numerator := 1788683549262974734011727872 }, some { target := 161, numerator := 43851596691608412833835909120 }, some { target := 162, numerator := 1788683549262974734011727872 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 382, numerator := 10198070323593477951062016 }, some { target := 383, numerator := 250017207933259459445391360 }, some { target := 384, numerator := 184881145866436600274092032 }, some { target := 385, numerator := 206264196544939054042447872 }, some { target := 386, numerator := 10198070323593477951062016 }, some { target := 387, numerator := 205935226534500554753703936 }, some { target := 388, numerator := 209553896649324046929887232 }, some { target := 389, numerator := 10198070323593477951062016 }, some { target := 390, numerator := 250017207933259459445391360 }, some { target := 391, numerator := 10198070323593477951062016 }]

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

end Slot10

namespace Slot11

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨11, 3, #[2130303778816, 51608327028736, 39101382262784, 43568148250624, 2130303778816, 43568148250624, 43499428773888, 2130303778816, 51608327028736, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

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
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 61, numerator := 20641463896623219229065216 }, some { target := 62, numerator := 15371302901740695170580480 }, some { target := 63, numerator := 16249663067554449180327936 }, some { target := 64, numerator := 21080643979530096233938944 }, some { target := 65, numerator := 282392793309121914133807104 }, some { target := 66, numerator := 510766436420697956668145664 }, some { target := 67, numerator := 15371302901740695170580480 }, some { target := 68, numerator := 282392793309121914133807104 }, some { target := 69, numerator := 16688843150461326185201664 }, some { target := 70, numerator := 16688843150461326185201664 }, some { target := 71, numerator := 16249663067554449180327936 }, some { target := 72, numerator := 16249663067554449180327936 }, some { target := 73, numerator := 510766436420697956668145664 }, some { target := 74, numerator := 16249663067554449180327936 }, some { target := 75, numerator := 20641463896623219229065216 }, some { target := 76, numerator := 21080643979530096233938944 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 132, numerator := 500056109237549601323483136 }, some { target := 133, numerator := 372382209006685873325998080 }, some { target := 134, numerator := 393661192378496494658912256 }, some { target := 135, numerator := 510695600923454911989940224 }, some { target := 136, numerator := 6841193154037114758531907584 }, some { target := 137, numerator := 12373728830707876305089593344 }, some { target := 138, numerator := 372382209006685873325998080 }, some { target := 139, numerator := 6841193154037114758531907584 }, some { target := 140, numerator := 404300684064401805325369344 }, some { target := 141, numerator := 404300684064401805325369344 }, some { target := 142, numerator := 393661192378496494658912256 }, some { target := 143, numerator := 393661192378496494658912256 }, some { target := 144, numerator := 12373728830707876305089593344 }, some { target := 145, numerator := 393661192378496494658912256 }, some { target := 146, numerator := 500056109237549601323483136 }, some { target := 147, numerator := 510695600923454911989940224 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 177, numerator := 378870740554148765849616384 }, some { target := 178, numerator := 282137785519046953292267520 }, some { target := 179, numerator := 298259944691563922051825664 }, some { target := 180, numerator := 386931820140407250229395456 }, some { target := 181, numerator := 5183274173964205456197943296 }, some { target := 182, numerator := 9375035558818617333683060736 }, some { target := 183, numerator := 282137785519046953292267520 }, some { target := 184, numerator := 5183274173964205456197943296 }, some { target := 185, numerator := 306321024277822406431604736 }, some { target := 186, numerator := 306321024277822406431604736 }, some { target := 187, numerator := 298259944691563922051825664 }, some { target := 188, numerator := 298259944691563922051825664 }, some { target := 189, numerator := 9375035558818617333683060736 }, some { target := 190, numerator := 298259944691563922051825664 }, some { target := 191, numerator := 378870740554148765849616384 }, some { target := 192, numerator := 386931820140407250229395456 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 203, numerator := 422151229369649064233140224 }, some { target := 204, numerator := 314367936764632281875742720 }, some { target := 205, numerator := 332331818865468412268642304 }, some { target := 206, numerator := 431133170420067129429590016 }, some { target := 207, numerator := 5775388095418815921317216256 }, some { target := 208, numerator := 10445997441636209823471108096 }, some { target := 209, numerator := 314367936764632281875742720 }, some { target := 210, numerator := 5775388095418815921317216256 }, some { target := 211, numerator := 341313759915886477465092096 }, some { target := 212, numerator := 341313759915886477465092096 }, some { target := 213, numerator := 332331818865468412268642304 }, some { target := 214, numerator := 332331818865468412268642304 }, some { target := 215, numerator := 10445997441636209823471108096 }, some { target := 216, numerator := 332331818865468412268642304 }, some { target := 217, numerator := 422151229369649064233140224 }, some { target := 218, numerator := 431133170420067129429590016 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 272, numerator := 20641463896623219229065216 }, some { target := 273, numerator := 15371302901740695170580480 }, some { target := 274, numerator := 16249663067554449180327936 }, some { target := 275, numerator := 21080643979530096233938944 }, some { target := 276, numerator := 282392793309121914133807104 }, some { target := 277, numerator := 510766436420697956668145664 }, some { target := 278, numerator := 15371302901740695170580480 }, some { target := 279, numerator := 282392793309121914133807104 }, some { target := 280, numerator := 16688843150461326185201664 }, some { target := 281, numerator := 16688843150461326185201664 }, some { target := 282, numerator := 16249663067554449180327936 }, some { target := 283, numerator := 16249663067554449180327936 }, some { target := 284, numerator := 510766436420697956668145664 }, some { target := 285, numerator := 16249663067554449180327936 }, some { target := 286, numerator := 20641463896623219229065216 }, some { target := 287, numerator := 21080643979530096233938944 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 317, numerator := 422151229369649064233140224 }, some { target := 318, numerator := 314367936764632281875742720 }, some { target := 319, numerator := 332331818865468412268642304 }, some { target := 320, numerator := 431133170420067129429590016 }, some { target := 321, numerator := 5775388095418815921317216256 }, some { target := 322, numerator := 10445997441636209823471108096 }, some { target := 323, numerator := 314367936764632281875742720 }, some { target := 324, numerator := 5775388095418815921317216256 }, some { target := 325, numerator := 341313759915886477465092096 }, some { target := 326, numerator := 341313759915886477465092096 }, some { target := 327, numerator := 332331818865468412268642304 }, some { target := 328, numerator := 332331818865468412268642304 }, some { target := 329, numerator := 10445997441636209823471108096 }, some { target := 330, numerator := 332331818865468412268642304 }, some { target := 331, numerator := 422151229369649064233140224 }, some { target := 332, numerator := 431133170420067129429590016 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 343, numerator := 421485375695564444258009088 }, some { target := 344, numerator := 313872088283930969128304640 }, some { target := 345, numerator := 331807636185869881649922048 }, some { target := 346, numerator := 430453149646533900518817792 }, some { target := 347, numerator := 5766278650473360375699996672 }, some { target := 348, numerator := 10429521104977477631320522752 }, some { target := 349, numerator := 313872088283930969128304640 }, some { target := 350, numerator := 5766278650473360375699996672 }, some { target := 351, numerator := 340775410136839337910730752 }, some { target := 352, numerator := 340775410136839337910730752 }, some { target := 353, numerator := 331807636185869881649922048 }, some { target := 354, numerator := 331807636185869881649922048 }, some { target := 355, numerator := 10429521104977477631320522752 }, some { target := 356, numerator := 331807636185869881649922048 }, some { target := 357, numerator := 421485375695564444258009088 }, some { target := 358, numerator := 430453149646533900518817792 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 392, numerator := 20641463896623219229065216 }, some { target := 393, numerator := 15371302901740695170580480 }, some { target := 394, numerator := 16249663067554449180327936 }, some { target := 395, numerator := 21080643979530096233938944 }, some { target := 396, numerator := 282392793309121914133807104 }, some { target := 397, numerator := 510766436420697956668145664 }, some { target := 398, numerator := 15371302901740695170580480 }, some { target := 399, numerator := 282392793309121914133807104 }, some { target := 400, numerator := 16688843150461326185201664 }, some { target := 401, numerator := 16688843150461326185201664 }, some { target := 402, numerator := 16249663067554449180327936 }, some { target := 403, numerator := 16249663067554449180327936 }, some { target := 404, numerator := 510766436420697956668145664 }, some { target := 405, numerator := 16249663067554449180327936 }, some { target := 406, numerator := 20641463896623219229065216 }, some { target := 407, numerator := 21080643979530096233938944 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 418, numerator := 500056109237549601323483136 }, some { target := 419, numerator := 372382209006685873325998080 }, some { target := 420, numerator := 393661192378496494658912256 }, some { target := 421, numerator := 510695600923454911989940224 }, some { target := 422, numerator := 6841193154037114758531907584 }, some { target := 423, numerator := 12373728830707876305089593344 }, some { target := 424, numerator := 372382209006685873325998080 }, some { target := 425, numerator := 6841193154037114758531907584 }, some { target := 426, numerator := 404300684064401805325369344 }, some { target := 427, numerator := 404300684064401805325369344 }, some { target := 428, numerator := 393661192378496494658912256 }, some { target := 429, numerator := 393661192378496494658912256 }, some { target := 430, numerator := 12373728830707876305089593344 }, some { target := 431, numerator := 393661192378496494658912256 }, some { target := 432, numerator := 500056109237549601323483136 }, some { target := 433, numerator := 510695600923454911989940224 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 453, numerator := 20641463896623219229065216 }, some { target := 454, numerator := 15371302901740695170580480 }, some { target := 455, numerator := 16249663067554449180327936 }, some { target := 456, numerator := 21080643979530096233938944 }, some { target := 457, numerator := 282392793309121914133807104 }, some { target := 458, numerator := 510766436420697956668145664 }, some { target := 459, numerator := 15371302901740695170580480 }, some { target := 460, numerator := 282392793309121914133807104 }, some { target := 461, numerator := 16688843150461326185201664 }, some { target := 462, numerator := 16688843150461326185201664 }, some { target := 463, numerator := 16249663067554449180327936 }, some { target := 464, numerator := 16249663067554449180327936 }, some { target := 465, numerator := 510766436420697956668145664 }, some { target := 466, numerator := 16249663067554449180327936 }, some { target := 467, numerator := 20641463896623219229065216 }, some { target := 468, numerator := 21080643979530096233938944 }]

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

end Slot11

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5.Parent2
