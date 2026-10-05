import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk2Parent1LocalDataBase

/-! Line-budgeted parent-local routing slots, part 2, for region 1, branch 1,
parent 10; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2.Parent1

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot7

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨7, 6, #[706035580928, 140031452774400, 0, 0, 0, 0, 140031452774400, 0, 0, 0, 0, 0, 0, 0, 706035580928, 0, 0, 0, 0], #[2130303778816, 52226802319360, 38620345925632, 43087111913472, 2130303778816, 43018392436736, 43774306680832, 2130303778816, 52226802319360, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 17, numerator := 9024421596176809080127488 }, some { target := 18, numerator := 221243884293366932286996480 }, some { target := 19, numerator := 163604030227463442033278976 }, some { target := 20, numerator := 182526204542027719136772096 }, some { target := 21, numerator := 9024421596176809080127488 }, some { target := 22, numerator := 182235094167957499489026048 }, some { target := 23, numerator := 185437308282729915614232576 }, some { target := 24, numerator := 9024421596176809080127488 }, some { target := 25, numerator := 221243884293366932286996480 }, some { target := 26, numerator := 9024421596176809080127488 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 37, numerator := 1789857197990391402882662400 }, some { target := 38, numerator := 43880370015248305360994304000 }, some { target := 39, numerator := 32448378879696773174840524800 }, some { target := 40, numerator := 36201305262579851922820300800 }, some { target := 41, numerator := 1789857197990391402882662400 }, some { target := 42, numerator := 36143567933612419942082150400 }, some { target := 43, numerator := 36778678552254171730201804800 }, some { target := 44, numerator := 1789857197990391402882662400 }, some { target := 45, numerator := 43880370015248305360994304000 }, some { target := 46, numerator := 1789857197990391402882662400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 153, numerator := 1789857197990391402882662400 }, some { target := 154, numerator := 43880370015248305360994304000 }, some { target := 155, numerator := 32448378879696773174840524800 }, some { target := 156, numerator := 36201305262579851922820300800 }, some { target := 157, numerator := 1789857197990391402882662400 }, some { target := 158, numerator := 36143567933612419942082150400 }, some { target := 159, numerator := 36778678552254171730201804800 }, some { target := 160, numerator := 1789857197990391402882662400 }, some { target := 161, numerator := 43880370015248305360994304000 }, some { target := 162, numerator := 1789857197990391402882662400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 382, numerator := 9024421596176809080127488 }, some { target := 383, numerator := 221243884293366932286996480 }, some { target := 384, numerator := 163604030227463442033278976 }, some { target := 385, numerator := 182526204542027719136772096 }, some { target := 386, numerator := 9024421596176809080127488 }, some { target := 387, numerator := 182235094167957499489026048 }, some { target := 388, numerator := 185437308282729915614232576 }, some { target := 389, numerator := 9024421596176809080127488 }, some { target := 390, numerator := 221243884293366932286996480 }, some { target := 391, numerator := 9024421596176809080127488 }]

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

end Slot7

namespace Slot8

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨8, 3, #[5963008442368, 0, 269517133447168, 0, 0, 0, 0, 5994834821120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3229815406592, 2405181685760, 2542620639232, 3298534883328, 44186623541248, 79920751443968, 2405181685760, 44186623541248, 2611340115968, 2611340115968, 2542620639232, 2542620639232, 79920751443968, 2542620639232, 3229815406592, 3298534883328, 0, 0, 0]⟩

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
  [some { target := 61, numerator := 57778249610394991557869568 }, some { target := 62, numerator := 43026356092847334138839040 }, some { target := 63, numerator := 45485005012438610375344128 }, some { target := 64, numerator := 59007574070190629676122112 }, some { target := 65, numerator := 790455627648595310036385792 }, some { target := 66, numerator := 1429704346742327131527708672 }, some { target := 67, numerator := 43026356092847334138839040 }, some { target := 68, numerator := 790455627648595310036385792 }, some { target := 69, numerator := 46714329472234248493596672 }, some { target := 70, numerator := 46714329472234248493596672 }, some { target := 71, numerator := 45485005012438610375344128 }, some { target := 72, numerator := 45485005012438610375344128 }, some { target := 73, numerator := 1429704346742327131527708672 }, some { target := 74, numerator := 45485005012438610375344128 }, some { target := 75, numerator := 57778249610394991557869568 }, some { target := 76, numerator := 59007574070190629676122112 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 177, numerator := 2611471769844525709412794368 }, some { target := 178, numerator := 1944713020096987230413783040 }, some { target := 179, numerator := 2055839478388243643580284928 }, some { target := 180, numerator := 2667034998990153915996045312 }, some { target := 181, numerator := 35727156340638936833030356992 }, some { target := 182, numerator := 64620035496365604256320847872 }, some { target := 183, numerator := 1944713020096987230413783040 }, some { target := 184, numerator := 35727156340638936833030356992 }, some { target := 185, numerator := 2111402707533871850163535872 }, some { target := 186, numerator := 2111402707533871850163535872 }, some { target := 187, numerator := 2055839478388243643580284928 }, some { target := 188, numerator := 2055839478388243643580284928 }, some { target := 189, numerator := 64620035496365604256320847872 }, some { target := 190, numerator := 2055839478388243643580284928 }, some { target := 191, numerator := 2611471769844525709412794368 }, some { target := 192, numerator := 2667034998990153915996045312 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 392, numerator := 58086629595682717166469120 }, some { target := 393, numerator := 43256000762742448953753600 }, some { target := 394, numerator := 45727772234899160322539520 }, some { target := 395, numerator := 59322515331761072850862080 }, some { target := 396, numerator := 794674528298382705064673280 }, some { target := 397, numerator := 1437335111059127660949012480 }, some { target := 398, numerator := 43256000762742448953753600 }, some { target := 399, numerator := 794674528298382705064673280 }, some { target := 400, numerator := 46963657970977516006932480 }, some { target := 401, numerator := 46963657970977516006932480 }, some { target := 402, numerator := 45727772234899160322539520 }, some { target := 403, numerator := 45727772234899160322539520 }, some { target := 404, numerator := 1437335111059127660949012480 }, some { target := 405, numerator := 45727772234899160322539520 }, some { target := 406, numerator := 58086629595682717166469120 }, some { target := 407, numerator := 59322515331761072850862080 }]

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

end Slot8

namespace Slot9

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨9, 1, #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0, 1, 2, 3]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        7 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total7.codes_eq

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
  [some { target := 219, numerator := 29014219670751100192948224 }, some { target := 220, numerator := 420706185225890952797749248 }, some { target := 221, numerator := 744698304882611571619004416 }, some { target := 222, numerator := 24178516392292583494123520 }, some { target := 223, numerator := 464227514732017603087171584 }, some { target := 224, numerator := 24178516392292583494123520 }, some { target := 225, numerator := 739862601604153054920179712 }, some { target := 226, numerator := 773712524553362671811952640 }, some { target := 227, numerator := 464227514732017603087171584 }, some { target := 228, numerator := 11852308735501824428819349504 }, some { target := 229, numerator := 759205414717987121715478528 }, some { target := 230, numerator := 420706185225890952797749248 }, some { target := 231, numerator := 739862601604153054920179712 }, some { target := 232, numerator := 24178516392292583494123520 }, some { target := 233, numerator := 759205414717987121715478528 }, some { target := 234, numerator := 24178516392292583494123520 }, some { target := 235, numerator := 739862601604153054920179712 }, some { target := 236, numerator := 773712524553362671811952640 }, some { target := 237, numerator := 29014219670751100192948224 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 359, numerator := 29014219670751100192948224 }, some { target := 360, numerator := 420706185225890952797749248 }, some { target := 361, numerator := 744698304882611571619004416 }, some { target := 362, numerator := 24178516392292583494123520 }, some { target := 363, numerator := 464227514732017603087171584 }, some { target := 364, numerator := 24178516392292583494123520 }, some { target := 365, numerator := 739862601604153054920179712 }, some { target := 366, numerator := 773712524553362671811952640 }, some { target := 367, numerator := 464227514732017603087171584 }, some { target := 368, numerator := 11852308735501824428819349504 }, some { target := 369, numerator := 759205414717987121715478528 }, some { target := 370, numerator := 420706185225890952797749248 }, some { target := 371, numerator := 739862601604153054920179712 }, some { target := 372, numerator := 24178516392292583494123520 }, some { target := 373, numerator := 759205414717987121715478528 }, some { target := 374, numerator := 24178516392292583494123520 }, some { target := 375, numerator := 739862601604153054920179712 }, some { target := 376, numerator := 773712524553362671811952640 }, some { target := 377, numerator := 29014219670751100192948224 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 434, numerator := 29014219670751100192948224 }, some { target := 435, numerator := 420706185225890952797749248 }, some { target := 436, numerator := 744698304882611571619004416 }, some { target := 437, numerator := 24178516392292583494123520 }, some { target := 438, numerator := 464227514732017603087171584 }, some { target := 439, numerator := 24178516392292583494123520 }, some { target := 440, numerator := 739862601604153054920179712 }, some { target := 441, numerator := 773712524553362671811952640 }, some { target := 442, numerator := 464227514732017603087171584 }, some { target := 443, numerator := 11852308735501824428819349504 }, some { target := 444, numerator := 759205414717987121715478528 }, some { target := 445, numerator := 420706185225890952797749248 }, some { target := 446, numerator := 739862601604153054920179712 }, some { target := 447, numerator := 24178516392292583494123520 }, some { target := 448, numerator := 759205414717987121715478528 }, some { target := 449, numerator := 24178516392292583494123520 }, some { target := 450, numerator := 739862601604153054920179712 }, some { target := 451, numerator := 773712524553362671811952640 }, some { target := 452, numerator := 29014219670751100192948224 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 469, numerator := 29014219670751100192948224 }, some { target := 470, numerator := 420706185225890952797749248 }, some { target := 471, numerator := 744698304882611571619004416 }, some { target := 472, numerator := 24178516392292583494123520 }, some { target := 473, numerator := 464227514732017603087171584 }, some { target := 474, numerator := 24178516392292583494123520 }, some { target := 475, numerator := 739862601604153054920179712 }, some { target := 476, numerator := 773712524553362671811952640 }, some { target := 477, numerator := 464227514732017603087171584 }, some { target := 478, numerator := 11852308735501824428819349504 }, some { target := 479, numerator := 759205414717987121715478528 }, some { target := 480, numerator := 420706185225890952797749248 }, some { target := 481, numerator := 739862601604153054920179712 }, some { target := 482, numerator := 24178516392292583494123520 }, some { target := 483, numerator := 759205414717987121715478528 }, some { target := 484, numerator := 24178516392292583494123520 }, some { target := 485, numerator := 739862601604153054920179712 }, some { target := 486, numerator := 773712524553362671811952640 }, some { target := 487, numerator := 29014219670751100192948224 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected ++ Left1.expected ++ Left2.expected ++ Left3.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq, Left1.routed_eq, Left2.routed_eq, Left3.routed_eq]
  rfl

end Slot9

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2.Parent1
