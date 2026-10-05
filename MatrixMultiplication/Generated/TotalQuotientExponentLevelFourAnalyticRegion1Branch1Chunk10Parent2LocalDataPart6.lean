import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk10Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 6, for region 1, branch 1,
parent 44; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot26

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨26, 1385, #[50290594152448, 0, 0, 180893771628544, 0, 50290610929664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416]⟩

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
  [some { target := 26, numerator := 28718888946808761859367239680 }, some { target := 27, numerator := 416423889728727046960824975360 }, some { target := 28, numerator := 737118149634758221057092485120 }, some { target := 29, numerator := 23932407455673968216139366400 }, some { target := 30, numerator := 459502223148940189749875834880 }, some { target := 31, numerator := 23932407455673968216139366400 }, some { target := 32, numerator := 732331668143623427413864611840 }, some { target := 33, numerator := 765837038581566982916459724800 }, some { target := 34, numerator := 459502223148940189749875834880 }, some { target := 35, numerator := 11731666134771379219551517409280 }, some { target := 36, numerator := 751477594108162601986776104960 }, some { target := 37, numerator := 416423889728727046960824975360 }, some { target := 38, numerator := 732331668143623427413864611840 }, some { target := 39, numerator := 23932407455673968216139366400 }, some { target := 40, numerator := 751477594108162601986776104960 }, some { target := 41, numerator := 23932407455673968216139366400 }, some { target := 42, numerator := 732331668143623427413864611840 }, some { target := 43, numerator := 765837038581566982916459724800 }, some { target := 44, numerator := 28718888946808761859367239680 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 157, numerator := 103300989501565868067300311040 }, some { target := 158, numerator := 1497864347772705086975854510080 }, some { target := 159, numerator := 2651392063873523947060707983360 }, some { target := 160, numerator := 86084157917971556722750259200 }, some { target := 161, numerator := 1652815832025053889076804976640 }, some { target := 162, numerator := 86084157917971556722750259200 }, some { target := 163, numerator := 2634175232289929635716157931520 }, some { target := 164, numerator := 2754693053375089815128008294400 }, some { target := 165, numerator := 1652815832025053889076804976640 }, some { target := 166, numerator := 42198454211389657105492177059840 }, some { target := 167, numerator := 2703042558624306881094358138880 }, some { target := 168, numerator := 1497864347772705086975854510080 }, some { target := 169, numerator := 2634175232289929635716157931520 }, some { target := 170, numerator := 86084157917971556722750259200 }, some { target := 171, numerator := 2703042558624306881094358138880 }, some { target := 172, numerator := 86084157917971556722750259200 }, some { target := 173, numerator := 2634175232289929635716157931520 }, some { target := 174, numerator := 2754693053375089815128008294400 }, some { target := 175, numerator := 103300989501565868067300311040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 267, numerator := 28718898527586465142265610240 }, some { target := 268, numerator := 416424028650003744562851348480 }, some { target := 269, numerator := 737118395541385938651483996160 }, some { target := 270, numerator := 23932415439655387618554675200 }, some { target := 271, numerator := 459502376441383442276249763840 }, some { target := 272, numerator := 23932415439655387618554675200 }, some { target := 273, numerator := 732331912453454861127773061120 }, some { target := 274, numerator := 765837294068972403793749606400 }, some { target := 275, numerator := 459502376441383442276249763840 }, some { target := 276, numerator := 11731670048519071010615501783040 }, some { target := 277, numerator := 751477844805179171222616801280 }, some { target := 278, numerator := 416424028650003744562851348480 }, some { target := 279, numerator := 732331912453454861127773061120 }, some { target := 280, numerator := 23932415439655387618554675200 }, some { target := 281, numerator := 751477844805179171222616801280 }, some { target := 282, numerator := 23932415439655387618554675200 }, some { target := 283, numerator := 732331912453454861127773061120 }, some { target := 284, numerator := 765837294068972403793749606400 }, some { target := 285, numerator := 28718898527586465142265610240 }]

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

end Slot26

namespace Slot27

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨27, 387, #[3517964091392, 0, 137219541041152, 0, 0, 137219490709504, 0, 0, 0, 0, 0, 0, 3517980868608, 0, 0, 0, 0, 0, 0], #[2130303778816, 2405181685760, 2061584302080, 27144193310720, 2405181685760, 2061584302080, 2405181685760, 2405181685760, 99711960743936, 2473901162496, 27144193310720, 99711960743936, 2130303778816, 2405181685760, 2473901162496, 2405181685760, 0, 0, 0]⟩

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
  [some { target := 80, numerator := 2900306560483341574512574464 }, some { target := 81, numerator := 3274539665061837261546455040 }, some { target := 82, numerator := 2806748284338717652754104320 }, some { target := 83, numerator := 36955519077126449094595706880 }, some { target := 84, numerator := 3274539665061837261546455040 }, some { target := 85, numerator := 2806748284338717652754104320 }, some { target := 86, numerator := 3274539665061837261546455040 }, some { target := 87, numerator := 3274539665061837261546455040 }, some { target := 88, numerator := 135753058685849310471540178944 }, some { target := 89, numerator := 3368097941206461183304925184 }, some { target := 90, numerator := 36955519077126449094595706880 }, some { target := 91, numerator := 135753058685849310471540178944 }, some { target := 92, numerator := 2900306560483341574512574464 }, some { target := 93, numerator := 3274539665061837261546455040 }, some { target := 94, numerator := 3368097941206461183304925184 }, some { target := 95, numerator := 3274539665061837261546455040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 176, numerator := 113127571734449598865430544384 }, some { target := 177, numerator := 127724677764701160009357066240 }, some { target := 178, numerator := 109478295226886708579448913920 }, some { target := 179, numerator := 1441464220487341662962744033280 }, some { target := 180, numerator := 127724677764701160009357066240 }, some { target := 181, numerator := 109478295226886708579448913920 }, some { target := 182, numerator := 127724677764701160009357066240 }, some { target := 183, numerator := 127724677764701160009357066240 }, some { target := 184, numerator := 5295100212473753804959345803264 }, some { target := 185, numerator := 131373954272264050295338696704 }, some { target := 186, numerator := 1441464220487341662962744033280 }, some { target := 187, numerator := 5295100212473753804959345803264 }, some { target := 188, numerator := 113127571734449598865430544384 }, some { target := 189, numerator := 127724677764701160009357066240 }, some { target := 190, numerator := 131373954272264050295338696704 }, some { target := 191, numerator := 127724677764701160009357066240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 286, numerator := 113127530239651726560401031168 }, some { target := 287, numerator := 127724630915735820310130196480 }, some { target := 288, numerator := 109478255070630703122968739840 }, some { target := 289, numerator := 1441463691763304257785755074560 }, some { target := 290, numerator := 127724630915735820310130196480 }, some { target := 291, numerator := 109478255070630703122968739840 }, some { target := 292, numerator := 127724630915735820310130196480 }, some { target := 293, numerator := 127724630915735820310130196480 }, some { target := 294, numerator := 5295098270249505007714254716928 }, some { target := 295, numerator := 131373906084756843747562487808 }, some { target := 296, numerator := 1441463691763304257785755074560 }, some { target := 297, numerator := 5295098270249505007714254716928 }, some { target := 298, numerator := 113127530239651726560401031168 }, some { target := 299, numerator := 127724630915735820310130196480 }, some { target := 300, numerator := 131373906084756843747562487808 }, some { target := 301, numerator := 127724630915735820310130196480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 573, numerator := 2900320392082632342855745536 }, some { target := 574, numerator := 3274555281383617161288744960 }, some { target := 575, numerator := 2806761669757386138247495680 }, some { target := 576, numerator := 36955695318472250820258693120 }, some { target := 577, numerator := 3274555281383617161288744960 }, some { target := 578, numerator := 2806761669757386138247495680 }, some { target := 579, numerator := 3274555281383617161288744960 }, some { target := 580, numerator := 3274555281383617161288744960 }, some { target := 581, numerator := 135753706093932242886570541056 }, some { target := 582, numerator := 3368114003708863365896994816 }, some { target := 583, numerator := 36955695318472250820258693120 }, some { target := 584, numerator := 135753706093932242886570541056 }, some { target := 585, numerator := 2900320392082632342855745536 }, some { target := 586, numerator := 3274555281383617161288744960 }, some { target := 587, numerator := 3368114003708863365896994816 }, some { target := 588, numerator := 3274555281383617161288744960 }]

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

end Slot27

namespace Slot28

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨28, 7, #[412316860416, 6184752906240, 10857677324288, 412316860416, 6871947673600, 412316860416, 10857677324288, 10788957847552, 6871947673600, 166507292131328, 10651518894080, 6184752906240, 10857677324288, 412316860416, 10651518894080, 412316860416, 10857677324288, 10857677324288, 412316860416], #[1649267441664, 34428457844736, 1786706395136, 37039797960704, 55456617725952, 1717986918400, 55456617725952, 57793079934976, 34428457844736, 1717986918400, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 131, numerator := 4760145414732602375405568 }, some { target := 132, numerator := 99368035532543074586591232 }, some { target := 133, numerator := 5156824199293652573356032 }, some { target := 134, numerator := 106904932439203028347650048 }, some { target := 135, numerator := 160059889570383754873012224 }, some { target := 136, numerator := 4958484807013127474380800 }, some { target := 137, numerator := 160059889570383754873012224 }, some { target := 138, numerator := 166803428907921608238170112 }, some { target := 139, numerator := 99368035532543074586591232 }, some { target := 140, numerator := 4958484807013127474380800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 227, numerator := 71402181220989035631083520 }, some { target := 228, numerator := 1490520532988146118798868480 }, some { target := 229, numerator := 77352362989404788600340480 }, some { target := 230, numerator := 1603573986588045425214750720 }, some { target := 231, numerator := 2400898343555756323095183360 }, some { target := 232, numerator := 74377272105196912115712000 }, some { target := 233, numerator := 2400898343555756323095183360 }, some { target := 234, numerator := 2502051433618824123572551680 }, some { target := 235, numerator := 1490520532988146118798868480 }, some { target := 236, numerator := 74377272105196912115712000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 253, numerator := 125350495921291862552346624 }, some { target := 254, numerator := 2616691602356967630780235776 }, some { target := 255, numerator := 135796370581399517765042176 }, some { target := 256, numerator := 2815163220899013079821451264 }, some { target := 257, numerator := 4214910425353438878322655232 }, some { target := 258, numerator := 130573433251345690158694400 }, some { target := 259, numerator := 4214910425353438878322655232 }, some { target := 260, numerator := 4392490294575269016938479616 }, some { target := 261, numerator := 2616691602356967630780235776 }, some { target := 262, numerator := 130573433251345690158694400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 302, numerator := 4760145414732602375405568 }, some { target := 303, numerator := 99368035532543074586591232 }, some { target := 304, numerator := 5156824199293652573356032 }, some { target := 305, numerator := 106904932439203028347650048 }, some { target := 306, numerator := 160059889570383754873012224 }, some { target := 307, numerator := 4958484807013127474380800 }, some { target := 308, numerator := 160059889570383754873012224 }, some { target := 309, numerator := 166803428907921608238170112 }, some { target := 310, numerator := 99368035532543074586591232 }, some { target := 311, numerator := 4958484807013127474380800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 328, numerator := 79335756912210039590092800 }, some { target := 329, numerator := 1656133925542384576443187200 }, some { target := 330, numerator := 85947069988227542889267200 }, some { target := 331, numerator := 1781748873986717139127500800 }, some { target := 332, numerator := 2667664826173062581216870400 }, some { target := 333, numerator := 82641413450218791239680000 }, some { target := 334, numerator := 2667664826173062581216870400 }, some { target := 335, numerator := 2780057148465360137302835200 }, some { target := 336, numerator := 1656133925542384576443187200 }, some { target := 337, numerator := 82641413450218791239680000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 342, numerator := 4760145414732602375405568 }, some { target := 343, numerator := 99368035532543074586591232 }, some { target := 344, numerator := 5156824199293652573356032 }, some { target := 345, numerator := 106904932439203028347650048 }, some { target := 346, numerator := 160059889570383754873012224 }, some { target := 347, numerator := 4958484807013127474380800 }, some { target := 348, numerator := 160059889570383754873012224 }, some { target := 349, numerator := 166803428907921608238170112 }, some { target := 350, numerator := 99368035532543074586591232 }, some { target := 351, numerator := 4958484807013127474380800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 443, numerator := 125350495921291862552346624 }, some { target := 444, numerator := 2616691602356967630780235776 }, some { target := 445, numerator := 135796370581399517765042176 }, some { target := 446, numerator := 2815163220899013079821451264 }, some { target := 447, numerator := 4214910425353438878322655232 }, some { target := 448, numerator := 130573433251345690158694400 }, some { target := 449, numerator := 4214910425353438878322655232 }, some { target := 450, numerator := 4392490294575269016938479616 }, some { target := 451, numerator := 2616691602356967630780235776 }, some { target := 452, numerator := 130573433251345690158694400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 469, numerator := 124557138352169762156445696 }, some { target := 470, numerator := 2600130263101543785015803904 }, some { target := 471, numerator := 134936899881517242336149504 }, some { target := 472, numerator := 2797345732159145908430176256 }, some { target := 473, numerator := 4188233777091708252510486528 }, some { target := 474, numerator := 129747019116843502246297600 }, some { target := 475, numerator := 4188233777091708252510486528 }, some { target := 476, numerator := 4364689723090615415565451264 }, some { target := 477, numerator := 2600130263101543785015803904 }, some { target := 478, numerator := 129747019116843502246297600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 518, numerator := 79335756912210039590092800 }, some { target := 519, numerator := 1656133925542384576443187200 }, some { target := 520, numerator := 85947069988227542889267200 }, some { target := 521, numerator := 1781748873986717139127500800 }, some { target := 522, numerator := 2667664826173062581216870400 }, some { target := 523, numerator := 82641413450218791239680000 }, some { target := 524, numerator := 2667664826173062581216870400 }, some { target := 525, numerator := 2780057148465360137302835200 }, some { target := 526, numerator := 1656133925542384576443187200 }, some { target := 527, numerator := 82641413450218791239680000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 544, numerator := 1922305389982849259267948544 }, some { target := 545, numerator := 40128125015891978287218425856 }, some { target := 546, numerator := 2082497505814753364206944256 }, some { target := 547, numerator := 43171775216698156281059344384 }, some { target := 548, numerator := 64637518738173306342884769792 }, some { target := 549, numerator := 2002401447898801311737446400 }, some { target := 550, numerator := 64637518738173306342884769792 }, some { target := 551, numerator := 67360784707315676126847696896 }, some { target := 552, numerator := 40128125015891978287218425856 }, some { target := 553, numerator := 2002401447898801311737446400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 558, numerator := 122970423213925561364643840 }, some { target := 559, numerator := 2567007584590696093486940160 }, some { target := 560, numerator := 133217958481752691478364160 }, some { target := 561, numerator := 2761710754679411565647626240 }, some { target := 562, numerator := 4134880480568247000886149120 }, some { target := 563, numerator := 128094190847839126421504000 }, some { target := 564, numerator := 4134880480568247000886149120 }, some { target := 565, numerator := 4309088580121308212819394560 }, some { target := 566, numerator := 2567007584590696093486940160 }, some { target := 567, numerator := 128094190847839126421504000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 589, numerator := 71402181220989035631083520 }, some { target := 590, numerator := 1490520532988146118798868480 }, some { target := 591, numerator := 77352362989404788600340480 }, some { target := 592, numerator := 1603573986588045425214750720 }, some { target := 593, numerator := 2400898343555756323095183360 }, some { target := 594, numerator := 74377272105196912115712000 }, some { target := 595, numerator := 2400898343555756323095183360 }, some { target := 596, numerator := 2502051433618824123572551680 }, some { target := 597, numerator := 1490520532988146118798868480 }, some { target := 598, numerator := 74377272105196912115712000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 603, numerator := 125350495921291862552346624 }, some { target := 604, numerator := 2616691602356967630780235776 }, some { target := 605, numerator := 135796370581399517765042176 }, some { target := 606, numerator := 2815163220899013079821451264 }, some { target := 607, numerator := 4214910425353438878322655232 }, some { target := 608, numerator := 130573433251345690158694400 }, some { target := 609, numerator := 4214910425353438878322655232 }, some { target := 610, numerator := 4392490294575269016938479616 }, some { target := 611, numerator := 2616691602356967630780235776 }, some { target := 612, numerator := 130573433251345690158694400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 658, numerator := 4760145414732602375405568 }, some { target := 659, numerator := 99368035532543074586591232 }, some { target := 660, numerator := 5156824199293652573356032 }, some { target := 661, numerator := 106904932439203028347650048 }, some { target := 662, numerator := 160059889570383754873012224 }, some { target := 663, numerator := 4958484807013127474380800 }, some { target := 664, numerator := 160059889570383754873012224 }, some { target := 665, numerator := 166803428907921608238170112 }, some { target := 666, numerator := 99368035532543074586591232 }, some { target := 667, numerator := 4958484807013127474380800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 684, numerator := 122970423213925561364643840 }, some { target := 685, numerator := 2567007584590696093486940160 }, some { target := 686, numerator := 133217958481752691478364160 }, some { target := 687, numerator := 2761710754679411565647626240 }, some { target := 688, numerator := 4134880480568247000886149120 }, some { target := 689, numerator := 128094190847839126421504000 }, some { target := 690, numerator := 4134880480568247000886149120 }, some { target := 691, numerator := 4309088580121308212819394560 }, some { target := 692, numerator := 2567007584590696093486940160 }, some { target := 693, numerator := 128094190847839126421504000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 698, numerator := 4760145414732602375405568 }, some { target := 699, numerator := 99368035532543074586591232 }, some { target := 700, numerator := 5156824199293652573356032 }, some { target := 701, numerator := 106904932439203028347650048 }, some { target := 702, numerator := 160059889570383754873012224 }, some { target := 703, numerator := 4958484807013127474380800 }, some { target := 704, numerator := 160059889570383754873012224 }, some { target := 705, numerator := 166803428907921608238170112 }, some { target := 706, numerator := 99368035532543074586591232 }, some { target := 707, numerator := 4958484807013127474380800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 729, numerator := 125350495921291862552346624 }, some { target := 730, numerator := 2616691602356967630780235776 }, some { target := 731, numerator := 135796370581399517765042176 }, some { target := 732, numerator := 2815163220899013079821451264 }, some { target := 733, numerator := 4214910425353438878322655232 }, some { target := 734, numerator := 130573433251345690158694400 }, some { target := 735, numerator := 4214910425353438878322655232 }, some { target := 736, numerator := 4392490294575269016938479616 }, some { target := 737, numerator := 2616691602356967630780235776 }, some { target := 738, numerator := 130573433251345690158694400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 743, numerator := 125350495921291862552346624 }, some { target := 744, numerator := 2616691602356967630780235776 }, some { target := 745, numerator := 135796370581399517765042176 }, some { target := 746, numerator := 2815163220899013079821451264 }, some { target := 747, numerator := 4214910425353438878322655232 }, some { target := 748, numerator := 130573433251345690158694400 }, some { target := 749, numerator := 4214910425353438878322655232 }, some { target := 750, numerator := 4392490294575269016938479616 }, some { target := 751, numerator := 2616691602356967630780235776 }, some { target := 752, numerator := 130573433251345690158694400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 763, numerator := 4760145414732602375405568 }, some { target := 764, numerator := 99368035532543074586591232 }, some { target := 765, numerator := 5156824199293652573356032 }, some { target := 766, numerator := 106904932439203028347650048 }, some { target := 767, numerator := 160059889570383754873012224 }, some { target := 768, numerator := 4958484807013127474380800 }, some { target := 769, numerator := 160059889570383754873012224 }, some { target := 770, numerator := 166803428907921608238170112 }, some { target := 771, numerator := 99368035532543074586591232 }, some { target := 772, numerator := 4958484807013127474380800 }]

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

end Slot28

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10.Parent2
