import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk3Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 2, for region 1, branch 2,
parent 16; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot7

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨7, 4, #[209765531648, 21993537667072, 0, 237068353536000, 0, 0, 0, 0, 0, 0, 0, 21993554444288, 0, 0, 0, 0, 0, 0, 209765531648], #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 2, numerator := 59043748135319174106841088 }, some { target := 3, numerator := 59043748135319174106841088 }, some { target := 4, numerator := 59043748135319174106841088 }, some { target := 5, numerator := 59043748135319174106841088 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 8, numerator := 6190630502624026694602719232 }, some { target := 9, numerator := 6190630502624026694602719232 }, some { target := 10, numerator := 6190630502624026694602719232 }, some { target := 11, numerator := 6190630502624026694602719232 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 28, numerator := 66728809290379162986479616000 }, some { target := 29, numerator := 66728809290379162986479616000 }, some { target := 30, numerator := 66728809290379162986479616000 }, some { target := 31, numerator := 66728809290379162986479616000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 149, numerator := 6190635224990509564247932928 }, some { target := 150, numerator := 6190635224990509564247932928 }, some { target := 151, numerator := 6190635224990509564247932928 }, some { target := 152, numerator := 6190635224990509564247932928 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 378, numerator := 59043748135319174106841088 }, some { target := 379, numerator := 59043748135319174106841088 }, some { target := 380, numerator := 59043748135319174106841088 }, some { target := 381, numerator := 59043748135319174106841088 }]

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

end Slot7

namespace Slot8

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨8, 3, #[2130303778816, 50989851738112, 38139309588480, 44255343017984, 2130303778816, 44186623541248, 44392781971456, 2130303778816, 50989851738112, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0]⟩

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
  [some { target := 61, numerator := 15371302901740695170580480 }, some { target := 62, numerator := 15810482984647572175454208 }, some { target := 63, numerator := 15371302901740695170580480 }, some { target := 64, numerator := 13614582570113187151085568 }, some { target := 65, numerator := 637250300297878534071779328 }, some { target := 66, numerator := 173476132748216416925122560 }, some { target := 67, numerator := 15810482984647572175454208 }, some { target := 68, numerator := 637250300297878534071779328 }, some { target := 69, numerator := 15371302901740695170580480 }, some { target := 70, numerator := 15371302901740695170580480 }, some { target := 71, numerator := 13175402487206310146211840 }, some { target := 72, numerator := 15371302901740695170580480 }, some { target := 73, numerator := 173476132748216416925122560 }, some { target := 74, numerator := 13175402487206310146211840 }, some { target := 75, numerator := 15371302901740695170580480 }, some { target := 76, numerator := 13614582570113187151085568 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 132, numerator := 367919572680374058599055360 }, some { target := 133, numerator := 378431560471241888844742656 }, some { target := 134, numerator := 367919572680374058599055360 }, some { target := 135, numerator := 325871621516902737616306176 }, some { target := 136, numerator := 15252894284549221686492266496 }, some { target := 137, numerator := 4152235177392792947046481920 }, some { target := 138, numerator := 378431560471241888844742656 }, some { target := 139, numerator := 15252894284549221686492266496 }, some { target := 140, numerator := 367919572680374058599055360 }, some { target := 141, numerator := 367919572680374058599055360 }, some { target := 142, numerator := 315359633726034907370618880 }, some { target := 143, numerator := 367919572680374058599055360 }, some { target := 144, numerator := 4152235177392792947046481920 }, some { target := 145, numerator := 315359633726034907370618880 }, some { target := 146, numerator := 367919572680374058599055360 }, some { target := 147, numerator := 325871621516902737616306176 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 177, numerator := 275195906789228574828134400 }, some { target := 178, numerator := 283058646983206534108938240 }, some { target := 179, numerator := 275195906789228574828134400 }, some { target := 180, numerator := 243744946013316737704919040 }, some { target := 181, numerator := 11408836021462018916446371840 }, some { target := 182, numerator := 3105782376621293915917516800 }, some { target := 183, numerator := 283058646983206534108938240 }, some { target := 184, numerator := 11408836021462018916446371840 }, some { target := 185, numerator := 275195906789228574828134400 }, some { target := 186, numerator := 275195906789228574828134400 }, some { target := 187, numerator := 235882205819338778424115200 }, some { target := 188, numerator := 275195906789228574828134400 }, some { target := 189, numerator := 3105782376621293915917516800 }, some { target := 190, numerator := 235882205819338778424115200 }, some { target := 191, numerator := 275195906789228574828134400 }, some { target := 192, numerator := 243744946013316737704919040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 203, numerator := 319326421571645409350123520 }, some { target := 204, numerator := 328450033616549563902984192 }, some { target := 205, numerator := 319326421571645409350123520 }, some { target := 206, numerator := 282831973392028791138680832 }, some { target := 207, numerator := 13238361077155928256200835072 }, some { target := 208, numerator := 3603826757737141048379965440 }, some { target := 209, numerator := 328450033616549563902984192 }, some { target := 210, numerator := 13238361077155928256200835072 }, some { target := 211, numerator := 319326421571645409350123520 }, some { target := 212, numerator := 319326421571645409350123520 }, some { target := 213, numerator := 273708361347124636585820160 }, some { target := 214, numerator := 319326421571645409350123520 }, some { target := 215, numerator := 3603826757737141048379965440 }, some { target := 216, numerator := 273708361347124636585820160 }, some { target := 217, numerator := 319326421571645409350123520 }, some { target := 218, numerator := 282831973392028791138680832 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 272, numerator := 15371302901740695170580480 }, some { target := 273, numerator := 15810482984647572175454208 }, some { target := 274, numerator := 15371302901740695170580480 }, some { target := 275, numerator := 13614582570113187151085568 }, some { target := 276, numerator := 637250300297878534071779328 }, some { target := 277, numerator := 173476132748216416925122560 }, some { target := 278, numerator := 15810482984647572175454208 }, some { target := 279, numerator := 637250300297878534071779328 }, some { target := 280, numerator := 15371302901740695170580480 }, some { target := 281, numerator := 15371302901740695170580480 }, some { target := 282, numerator := 13175402487206310146211840 }, some { target := 283, numerator := 15371302901740695170580480 }, some { target := 284, numerator := 173476132748216416925122560 }, some { target := 285, numerator := 13175402487206310146211840 }, some { target := 286, numerator := 15371302901740695170580480 }, some { target := 287, numerator := 13614582570113187151085568 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 317, numerator := 318830573090944096602685440 }, some { target := 318, numerator := 327940018036399642219905024 }, some { target := 319, numerator := 318830573090944096602685440 }, some { target := 320, numerator := 282392793309121914133807104 }, some { target := 321, numerator := 13217804615855996690585616384 }, some { target := 322, numerator := 3598230753454940518801735680 }, some { target := 323, numerator := 327940018036399642219905024 }, some { target := 324, numerator := 13217804615855996690585616384 }, some { target := 325, numerator := 318830573090944096602685440 }, some { target := 326, numerator := 318830573090944096602685440 }, some { target := 327, numerator := 273283348363666368516587520 }, some { target := 328, numerator := 318830573090944096602685440 }, some { target := 329, numerator := 3598230753454940518801735680 }, some { target := 330, numerator := 273283348363666368516587520 }, some { target := 331, numerator := 318830573090944096602685440 }, some { target := 332, numerator := 282392793309121914133807104 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 343, numerator := 320318118533048034844999680 }, some { target := 344, numerator := 329470064776849407269142528 }, some { target := 345, numerator := 320318118533048034844999680 }, some { target := 346, numerator := 283710333557842545148428288 }, some { target := 347, numerator := 13279473999755791387431272448 }, some { target := 348, numerator := 3615018766301542107536424960 }, some { target := 349, numerator := 329470064776849407269142528 }, some { target := 350, numerator := 13279473999755791387431272448 }, some { target := 351, numerator := 320318118533048034844999680 }, some { target := 352, numerator := 320318118533048034844999680 }, some { target := 353, numerator := 274558387314041172724285440 }, some { target := 354, numerator := 320318118533048034844999680 }, some { target := 355, numerator := 3615018766301542107536424960 }, some { target := 356, numerator := 274558387314041172724285440 }, some { target := 357, numerator := 320318118533048034844999680 }, some { target := 358, numerator := 283710333557842545148428288 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 392, numerator := 15371302901740695170580480 }, some { target := 393, numerator := 15810482984647572175454208 }, some { target := 394, numerator := 15371302901740695170580480 }, some { target := 395, numerator := 13614582570113187151085568 }, some { target := 396, numerator := 637250300297878534071779328 }, some { target := 397, numerator := 173476132748216416925122560 }, some { target := 398, numerator := 15810482984647572175454208 }, some { target := 399, numerator := 637250300297878534071779328 }, some { target := 400, numerator := 15371302901740695170580480 }, some { target := 401, numerator := 15371302901740695170580480 }, some { target := 402, numerator := 13175402487206310146211840 }, some { target := 403, numerator := 15371302901740695170580480 }, some { target := 404, numerator := 173476132748216416925122560 }, some { target := 405, numerator := 13175402487206310146211840 }, some { target := 406, numerator := 15371302901740695170580480 }, some { target := 407, numerator := 13614582570113187151085568 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 418, numerator := 367919572680374058599055360 }, some { target := 419, numerator := 378431560471241888844742656 }, some { target := 420, numerator := 367919572680374058599055360 }, some { target := 421, numerator := 325871621516902737616306176 }, some { target := 422, numerator := 15252894284549221686492266496 }, some { target := 423, numerator := 4152235177392792947046481920 }, some { target := 424, numerator := 378431560471241888844742656 }, some { target := 425, numerator := 15252894284549221686492266496 }, some { target := 426, numerator := 367919572680374058599055360 }, some { target := 427, numerator := 367919572680374058599055360 }, some { target := 428, numerator := 315359633726034907370618880 }, some { target := 429, numerator := 367919572680374058599055360 }, some { target := 430, numerator := 4152235177392792947046481920 }, some { target := 431, numerator := 315359633726034907370618880 }, some { target := 432, numerator := 367919572680374058599055360 }, some { target := 433, numerator := 325871621516902737616306176 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 453, numerator := 15371302901740695170580480 }, some { target := 454, numerator := 15810482984647572175454208 }, some { target := 455, numerator := 15371302901740695170580480 }, some { target := 456, numerator := 13614582570113187151085568 }, some { target := 457, numerator := 637250300297878534071779328 }, some { target := 458, numerator := 173476132748216416925122560 }, some { target := 459, numerator := 15810482984647572175454208 }, some { target := 460, numerator := 637250300297878534071779328 }, some { target := 461, numerator := 15371302901740695170580480 }, some { target := 462, numerator := 15371302901740695170580480 }, some { target := 463, numerator := 13175402487206310146211840 }, some { target := 464, numerator := 15371302901740695170580480 }, some { target := 465, numerator := 173476132748216416925122560 }, some { target := 466, numerator := 13175402487206310146211840 }, some { target := 467, numerator := 15371302901740695170580480 }, some { target := 468, numerator := 13614582570113187151085568 }]

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

end Slot8

namespace Slot9

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨9, 7, #[1653998616576, 139083489738752, 0, 0, 0, 0, 139083456184320, 0, 0, 0, 0, 0, 0, 0, 1654032171008, 0, 0, 0, 0], #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 17, numerator := 19890835904304857795788800 }, some { target := 18, numerator := 398612351522269350227607552 }, some { target := 19, numerator := 669127719820815416250335232 }, some { target := 20, numerator := 642076182990960809648062464 }, some { target := 21, numerator := 19890835904304857795788800 }, some { target := 22, numerator := 642076182990960809648062464 }, some { target := 23, numerator := 428846422096812734077206528 }, some { target := 24, numerator := 20686469340477052107620352 }, some { target := 25, numerator := 398612351522269350227607552 }, some { target := 26, numerator := 19095202468132663483957248 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 37, numerator := 1672605311556175986792857600 }, some { target := 38, numerator := 33519010443585766775328866304 }, some { target := 39, numerator := 56266442680749760195711729664 }, some { target := 40, numerator := 53991699457033360853673443328 }, some { target := 41, numerator := 1672605311556175986792857600 }, some { target := 42, numerator := 53991699457033360853673443328 }, some { target := 43, numerator := 36061370517151154275254009856 }, some { target := 44, numerator := 1739509524018423026264571904 }, some { target := 45, numerator := 33519010443585766775328866304 }, some { target := 46, numerator := 1605701099093928947321143296 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 153, numerator := 1672604908033649374396416000 }, some { target := 154, numerator := 33519002356994333462904176640 }, some { target := 155, numerator := 56266429106251964954695434240 }, some { target := 156, numerator := 53991686431326201805516308480 }, some { target := 157, numerator := 1672604908033649374396416000 }, some { target := 158, numerator := 53991686431326201805516308480 }, some { target := 159, numerator := 36061361817205480511986728960 }, some { target := 160, numerator := 1739509104354995349372272640 }, some { target := 161, numerator := 33519002356994333462904176640 }, some { target := 162, numerator := 1605700711712303399420559360 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 382, numerator := 19891239426831470192230400 }, some { target := 383, numerator := 398620438113702662652297216 }, some { target := 384, numerator := 669141294318610657266630656 }, some { target := 385, numerator := 642089208698119857805197312 }, some { target := 386, numerator := 19891239426831470192230400 }, some { target := 387, numerator := 642089208698119857805197312 }, some { target := 388, numerator := 428855122042486497344487424 }, some { target := 389, numerator := 20686889003904728999919616 }, some { target := 390, numerator := 398620438113702662652297216 }, some { target := 391, numerator := 19095589849758211384541184 }]

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

end Slot9

namespace Slot10

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨10, 8, #[153243090944, 22633202581504, 0, 235902085365760, 0, 0, 0, 0, 0, 0, 0, 22633202581504, 0, 0, 0, 0, 0, 0, 153243090944], #[73529840107520, 67207648247808, 73529840107520, 67207648247808, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 2, numerator := 90143519797555728786391040 }, some { target := 3, numerator := 82392862020569628741206016 }, some { target := 4, numerator := 90143519797555728786391040 }, some { target := 5, numerator := 82392862020569628741206016 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 8, numerator := 13313726135512784167386480640 }, some { target := 9, numerator := 12168994542552806463274745856 }, some { target := 10, numerator := 13313726135512784167386480640 }, some { target := 11, numerator := 12168994542552806463274745856 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 28, numerator := 138766740943798931975412121600 }, some { target := 29, numerator := 126835394993490986422386032640 }, some { target := 30, numerator := 138766740943798931975412121600 }, some { target := 31, numerator := 126835394993490986422386032640 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 149, numerator := 13313726135512784167386480640 }, some { target := 150, numerator := 12168994542552806463274745856 }, some { target := 151, numerator := 13313726135512784167386480640 }, some { target := 152, numerator := 12168994542552806463274745856 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 378, numerator := 90143519797555728786391040 }, some { target := 379, numerator := 82392862020569628741206016 }, some { target := 380, numerator := 90143519797555728786391040 }, some { target := 381, numerator := 82392862020569628741206016 }]

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3.Parent2
