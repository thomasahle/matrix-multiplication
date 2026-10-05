import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk7Parent1LocalDataBase

/-! Line-budgeted parent-local routing slots, part 5, for region 1, branch 2,
parent 31; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot19

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨19, 587, #[147035521024, 23473808211968, 0, 234233306021888, 0, 0, 0, 0, 0, 0, 0, 23473808211968, 0, 0, 0, 0, 0, 0, 147018743808], #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 71, numerator := 35587006721770661093572608 }, some { target := 72, numerator := 948986845913884295828602880 }, some { target := 73, numerator := 907468671405151857886101504 }, some { target := 74, numerator := 29655838934808884244643840 }, some { target := 75, numerator := 931193342552998965281816576 }, some { target := 76, numerator := 29655838934808884244643840 }, some { target := 77, numerator := 907468671405151857886101504 }, some { target := 78, numerator := 516011597465674585856802816 }, some { target := 79, numerator := 931193342552998965281816576 }, some { target := 80, numerator := 14537292245843315056724410368 }, some { target := 81, numerator := 569392107548330577497161728 }, some { target := 82, numerator := 948986845913884295828602880 }, some { target := 83, numerator := 907468671405151857886101504 }, some { target := 84, numerator := 29655838934808884244643840 }, some { target := 85, numerator := 569392107548330577497161728 }, some { target := 86, numerator := 29655838934808884244643840 }, some { target := 87, numerator := 913399839192113634735030272 }, some { target := 88, numerator := 516011597465674585856802816 }, some { target := 89, numerator := 35587006721770661093572608 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 146, numerator := 5681365732628021100838649856 }, some { target := 147, numerator := 151503086203413896022363996160 }, some { target := 148, numerator := 144874826182014538071385571328 }, some { target := 149, numerator := 4734471443856684250698874880 }, some { target := 150, numerator := 148662403337099885471944671232 }, some { target := 151, numerator := 4734471443856684250698874880 }, some { target := 152, numerator := 144874826182014538071385571328 }, some { target := 153, numerator := 82379803123106305962160422912 }, some { target := 154, numerator := 148662403337099885471944671232 }, some { target := 155, numerator := 2320837901778546619692588466176 }, some { target := 156, numerator := 90901851722048337613418397696 }, some { target := 157, numerator := 151503086203413896022363996160 }, some { target := 158, numerator := 144874826182014538071385571328 }, some { target := 159, numerator := 4734471443856684250698874880 }, some { target := 160, numerator := 90901851722048337613418397696 }, some { target := 161, numerator := 4734471443856684250698874880 }, some { target := 162, numerator := 145821720470785874921525346304 }, some { target := 163, numerator := 82379803123106305962160422912 }, some { target := 164, numerator := 5681365732628021100838649856 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 242, numerator := 56691486368813538954493034496 }, some { target := 243, numerator := 1511772969835027705453147586560 }, some { target := 244, numerator := 1445632902404745243339572379648 }, some { target := 245, numerator := 47242905307344615795410862080 }, some { target := 246, numerator := 1483427226650620935975901069312 }, some { target := 247, numerator := 47242905307344615795410862080 }, some { target := 248, numerator := 1445632902404745243339572379648 }, some { target := 249, numerator := 822026552347796314840149000192 }, some { target := 250, numerator := 1483427226650620935975901069312 }, some { target := 251, numerator := 23158472181660330662910404591616 }, some { target := 252, numerator := 907063781901016623271888551936 }, some { target := 253, numerator := 1511772969835027705453147586560 }, some { target := 254, numerator := 1445632902404745243339572379648 }, some { target := 255, numerator := 47242905307344615795410862080 }, some { target := 256, numerator := 907063781901016623271888551936 }, some { target := 257, numerator := 47242905307344615795410862080 }, some { target := 258, numerator := 1455081483466214166498654552064 }, some { target := 259, numerator := 822026552347796314840149000192 }, some { target := 260, numerator := 56691486368813538954493034496 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 640, numerator := 5681365732628021100838649856 }, some { target := 641, numerator := 151503086203413896022363996160 }, some { target := 642, numerator := 144874826182014538071385571328 }, some { target := 643, numerator := 4734471443856684250698874880 }, some { target := 644, numerator := 148662403337099885471944671232 }, some { target := 645, numerator := 4734471443856684250698874880 }, some { target := 646, numerator := 144874826182014538071385571328 }, some { target := 647, numerator := 82379803123106305962160422912 }, some { target := 648, numerator := 148662403337099885471944671232 }, some { target := 649, numerator := 2320837901778546619692588466176 }, some { target := 650, numerator := 90901851722048337613418397696 }, some { target := 651, numerator := 151503086203413896022363996160 }, some { target := 652, numerator := 144874826182014538071385571328 }, some { target := 653, numerator := 4734471443856684250698874880 }, some { target := 654, numerator := 90901851722048337613418397696 }, some { target := 655, numerator := 4734471443856684250698874880 }, some { target := 656, numerator := 145821720470785874921525346304 }, some { target := 657, numerator := 82379803123106305962160422912 }, some { target := 658, numerator := 5681365732628021100838649856 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1017, numerator := 35582946132231435778523136 }, some { target := 1018, numerator := 948878563526171620760616960 }, some { target := 1019, numerator := 907365126371901612352339968 }, some { target := 1020, numerator := 29652455110192863148769280 }, some { target := 1021, numerator := 931087090460055902871355392 }, some { target := 1022, numerator := 29652455110192863148769280 }, some { target := 1023, numerator := 907365126371901612352339968 }, some { target := 1024, numerator := 515952718917355818788585472 }, some { target := 1025, numerator := 931087090460055902871355392 }, some { target := 1026, numerator := 14535633495016541515526701056 }, some { target := 1027, numerator := 569327138115702972456370176 }, some { target := 1028, numerator := 948878563526171620760616960 }, some { target := 1029, numerator := 907365126371901612352339968 }, some { target := 1030, numerator := 29652455110192863148769280 }, some { target := 1031, numerator := 569327138115702972456370176 }, some { target := 1032, numerator := 29652455110192863148769280 }, some { target := 1033, numerator := 913295617393940184982093824 }, some { target := 1034, numerator := 515952718917355818788585472 }, some { target := 1035, numerator := 35582946132231435778523136 }]

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

end Slot19

namespace Slot20

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨20, 901, #[3648641826816, 0, 137088846528512, 0, 0, 137078478209024, 0, 0, 0, 0, 0, 0, 3659010146304, 0, 0, 0, 0, 0, 0], #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes

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
        5 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total5.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 29, numerator := 7906857496279933320859484160 }, some { target := 30, numerator := 8132767710459359987169755136 }, some { target := 31, numerator := 7906857496279933320859484160 }, some { target := 32, numerator := 7003216639562226655618400256 }, some { target := 33, numerator := 327795720774348092816203186176 }, some { target := 34, numerator := 89234534600873533192557035520 }, some { target := 35, numerator := 8132767710459359987169755136 }, some { target := 36, numerator := 327795720774348092816203186176 }, some { target := 37, numerator := 7906857496279933320859484160 }, some { target := 38, numerator := 7906857496279933320859484160 }, some { target := 39, numerator := 6777306425382799989308129280 }, some { target := 40, numerator := 7906857496279933320859484160 }, some { target := 41, numerator := 89234534600873533192557035520 }, some { target := 42, numerator := 6777306425382799989308129280 }, some { target := 43, numerator := 7906857496279933320859484160 }, some { target := 44, numerator := 7003216639562226655618400256 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 104, numerator := 297080948276098714874014597120 }, some { target := 105, numerator := 305568975369701535298986442752 }, some { target := 106, numerator := 297080948276098714874014597120 }, some { target := 107, numerator := 263128839901687433174127214592 }, some { target := 108, numerator := 12316127312817692436634148012032 }, some { target := 109, numerator := 3352770701973114067863879024640 }, some { target := 110, numerator := 305568975369701535298986442752 }, some { target := 111, numerator := 12316127312817692436634148012032 }, some { target := 112, numerator := 297080948276098714874014597120 }, some { target := 113, numerator := 297080948276098714874014597120 }, some { target := 114, numerator := 254640812808084612749155368960 }, some { target := 115, numerator := 297080948276098714874014597120 }, some { target := 116, numerator := 3352770701973114067863879024640 }, some { target := 117, numerator := 254640812808084612749155368960 }, some { target := 118, numerator := 297080948276098714874014597120 }, some { target := 119, numerator := 263128839901687433174127214592 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 226, numerator := 297058479415476388737832714240 }, some { target := 227, numerator := 305545864541632856987485077504 }, some { target := 228, numerator := 297058479415476388737832714240 }, some { target := 229, numerator := 263108938910850515739223261184 }, some { target := 230, numerator := 12315195818053035430245579096064 }, some { target := 231, numerator := 3352517124831804958612683489280 }, some { target := 232, numerator := 305545864541632856987485077504 }, some { target := 233, numerator := 12315195818053035430245579096064 }, some { target := 234, numerator := 297058479415476388737832714240 }, some { target := 235, numerator := 297058479415476388737832714240 }, some { target := 236, numerator := 254621553784694047489570897920 }, some { target := 237, numerator := 297058479415476388737832714240 }, some { target := 238, numerator := 3352517124831804958612683489280 }, some { target := 239, numerator := 254621553784694047489570897920 }, some { target := 240, numerator := 297058479415476388737832714240 }, some { target := 241, numerator := 263108938910850515739223261184 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 624, numerator := 7929326356902259457041367040 }, some { target := 625, numerator := 8155878538528038298671120384 }, some { target := 626, numerator := 7929326356902259457041367040 }, some { target := 627, numerator := 7023117630399144090522353664 }, some { target := 628, numerator := 328727215539005099204772102144 }, some { target := 629, numerator := 89488111742182642443752570880 }, some { target := 630, numerator := 8155878538528038298671120384 }, some { target := 631, numerator := 328727215539005099204772102144 }, some { target := 632, numerator := 7929326356902259457041367040 }, some { target := 633, numerator := 7929326356902259457041367040 }, some { target := 634, numerator := 6796565448773365248892600320 }, some { target := 635, numerator := 7929326356902259457041367040 }, some { target := 636, numerator := 89488111742182642443752570880 }, some { target := 637, numerator := 6796565448773365248892600320 }, some { target := 638, numerator := 7929326356902259457041367040 }, some { target := 639, numerator := 7023117630399144090522353664 }]

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

end Slot20

namespace Slot21

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨21, 84, #[51810056273920, 0, 0, 177854864162816, 0, 51810056273920, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

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
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 5, numerator := 7476755909293642195402752000 }, some { target := 6, numerator := 149834188422244589595871150080 }, some { target := 7, numerator := 251518068788638123453348577280 }, some { target := 8, numerator := 241349680751998770067600834560 }, some { target := 9, numerator := 7476755909293642195402752000 }, some { target := 10, numerator := 241349680751998770067600834560 }, some { target := 11, numerator := 161198857404370925732883333120 }, some { target := 12, numerator := 7775826145665387883218862080 }, some { target := 13, numerator := 149834188422244589595871150080 }, some { target := 14, numerator := 7177685672921896507586641920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 94, numerator := 25666395720464255879322009600 }, some { target := 95, numerator := 514354570238103687821613072384 }, some { target := 96, numerator := 863417552036417567780392402944 }, some { target := 97, numerator := 828511253856586179784514469888 }, some { target := 98, numerator := 25666395720464255879322009600 }, some { target := 99, numerator := 828511253856586179784514469888 }, some { target := 100, numerator := 553367491733209356758182526976 }, some { target := 101, numerator := 26693051549282826114494889984 }, some { target := 102, numerator := 514354570238103687821613072384 }, some { target := 103, numerator := 24639739891645685644149129216 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 216, numerator := 7476755909293642195402752000 }, some { target := 217, numerator := 149834188422244589595871150080 }, some { target := 218, numerator := 251518068788638123453348577280 }, some { target := 219, numerator := 241349680751998770067600834560 }, some { target := 220, numerator := 7476755909293642195402752000 }, some { target := 221, numerator := 241349680751998770067600834560 }, some { target := 222, numerator := 161198857404370925732883333120 }, some { target := 223, numerator := 7775826145665387883218862080 }, some { target := 224, numerator := 149834188422244589595871150080 }, some { target := 225, numerator := 7177685672921896507586641920 }]

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

end Slot21

namespace Slot22

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨22, 5, #[140737488355328, 0, 140737488355328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[73529840107520, 67207648247808, 73529840107520, 67207648247808, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

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
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1, numerator := 51742025079506128677424332800 }, some { target := 2, numerator := 47293178063324293314505605120 }, some { target := 3, numerator := 51742025079506128677424332800 }, some { target := 4, numerator := 47293178063324293314505605120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 90, numerator := 51742025079506128677424332800 }, some { target := 91, numerator := 47293178063324293314505605120 }, some { target := 92, numerator := 51742025079506128677424332800 }, some { target := 93, numerator := 47293178063324293314505605120 }]

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
def data : BetaFourLocalSlotData := ⟨23, 0, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot23

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7.Parent1
