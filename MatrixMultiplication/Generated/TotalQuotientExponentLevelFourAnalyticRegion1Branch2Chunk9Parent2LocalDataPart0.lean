import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk9Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 0, for region 1, branch 2,
parent 40; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot0

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨0, 5, #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[49931561730048, 0, 0, 181611853250560, 0, 49931561730048, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- Nonzero left symbols, in the order used by the sparse source fold. -/
def leftSymbols : List ℕ := [0]

/-- The serialized left-symbol support is exact. -/
theorem leftSymbols_eq :
    BetaFourLocalSlotData.nonzeroSymbols data.leftNumerators = leftSymbols := by
  rfl

/-- Checked inert support of this slot's left child. -/
def leftSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total8.codes

/-- Checked inert support of this slot's right child. -/
def rightSupport : List ℕ :=
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

/-- The semantic left support is the shared checked table. -/
theorem routedLeftSupport_eq :
    data.routedLeftSupport parent coordinate = leftSupport := by
  unfold BetaFourLocalSlotData.routedLeftSupport leftSupport
  rw [show MatrixMultiplication.BetaFourLocalGeometry.shapeCoordinate
      (MatrixMultiplication.BetaFourLocalGeometry.pairAt parent data.slot).1 coordinate =
        8 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total8.codes_eq

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
  [some { target := 774, numerator := 70272425875459716058384957440 }, some { target := 777, numerator := 255595960820402255850949836800 }, some { target := 779, numerator := 70272425875459716058384957440 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

/-- Routed output of this slot, assembled from independently checked fixed-left rows. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) :=
  Left0.expected

/-- The bounded row checks compose to the exact sparse route for this slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  rw [data.routedContributions_eq_flatMap_forLeftFromSupports_of_ne parent coordinate
    ParentSupport.codes leftSupport rightSupport ParentSupport.routedSupport_eq
    routedLeftSupport_eq routedRightSupport_eq split_ne]
  rw [leftSymbols_eq]
  simp only [leftSymbols, List.flatMap_cons, List.flatMap_nil]
  rw [Left0.routed_eq]
  rfl

end Slot0

namespace Slot1

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨1, 5, #[73529840107520, 67207648247808, 73529840107520, 67207648247808, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3710583308288, 0, 137026905047040, 0, 0, 137026871492608, 0, 0, 0, 0, 0, 0, 3710616862720, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

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
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 411, numerator := 1364192986820246156135628800 }, some { target := 413, numerator := 50377832092685882521288704000 }, some { target := 416, numerator := 50377819756425783228026060800 }, some { target := 423, numerator := 1364205323080345449398272000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 627, numerator := 1246897888888038075421163520 }, some { target := 629, numerator := 46046280174436255239084441600 }, some { target := 632, numerator := 46046268898863940184121016320 }, some { target := 639, numerator := 1246909164460353130384588800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 723, numerator := 1364192986820246156135628800 }, some { target := 725, numerator := 50377832092685882521288704000 }, some { target := 728, numerator := 50377819756425783228026060800 }, some { target := 735, numerator := 1364205323080345449398272000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 758, numerator := 1246897888888038075421163520 }, some { target := 760, numerator := 46046280174436255239084441600 }, some { target := 763, numerator := 46046268898863940184121016320 }, some { target := 770, numerator := 1246909164460353130384588800 }]

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

end Slot1

namespace Slot2

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨2, 8, #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[343597383680, 5772436045824, 12506944765952, 412316860416, 6597069766656, 481036337152, 12506944765952, 12506944765952, 6597069766656, 154343944749056, 12369505812480, 5772436045824, 12506944765952, 481036337152, 12369505812480, 481036337152, 12506944765952, 12506944765952, 412316860416]⟩

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
  [some { target := 142, numerator := 4722366482869645213696000 }, some { target := 143, numerator := 79335756912210039590092800 }, some { target := 144, numerator := 171894139976455085778534400 }, some { target := 145, numerator := 5666839779443574256435200 }, some { target := 146, numerator := 90669436471097188102963200 }, some { target := 147, numerator := 6611313076017503299174400 }, some { target := 148, numerator := 171894139976455085778534400 }, some { target := 149, numerator := 171894139976455085778534400 }, some { target := 150, numerator := 90669436471097188102963200 }, some { target := 151, numerator := 2121287024105044629992243200 }, some { target := 152, numerator := 170005193383307227693056000 }, some { target := 153, numerator := 79335756912210039590092800 }, some { target := 154, numerator := 171894139976455085778534400 }, some { target := 155, numerator := 6611313076017503299174400 }, some { target := 156, numerator := 170005193383307227693056000 }, some { target := 157, numerator := 6611313076017503299174400 }, some { target := 158, numerator := 171894139976455085778534400 }, some { target := 159, numerator := 171894139976455085778534400 }, some { target := 160, numerator := 5666839779443574256435200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 282, numerator := 94636224316707690082467840 }, some { target := 283, numerator := 1589888568520689193385459712 }, some { target := 284, numerator := 3444758565128159919001829376 }, some { target := 285, numerator := 113563469180049228098961408 }, some { target := 286, numerator := 1817015506880787649583382528 }, some { target := 287, numerator := 132490714043390766115454976 }, some { target := 288, numerator := 3444758565128159919001829376 }, some { target := 289, numerator := 3444758565128159919001829376 }, some { target := 290, numerator := 1817015506880787649583382528 }, some { target := 291, numerator := 42510591963065094385044553728 }, some { target := 292, numerator := 3406904075401476842968842240 }, some { target := 293, numerator := 1589888568520689193385459712 }, some { target := 294, numerator := 3444758565128159919001829376 }, some { target := 295, numerator := 132490714043390766115454976 }, some { target := 296, numerator := 3406904075401476842968842240 }, some { target := 297, numerator := 132490714043390766115454976 }, some { target := 298, numerator := 3444758565128159919001829376 }, some { target := 299, numerator := 3444758565128159919001829376 }, some { target := 300, numerator := 113563469180049228098961408 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 357, numerator := 158860408483734864988733440 }, some { target := 358, numerator := 2668854862526745731810721792 }, some { target := 359, numerator := 5782518868807949085589897216 }, some { target := 360, numerator := 190632490180481837986480128 }, some { target := 361, numerator := 3050119842887709407783682048 }, some { target := 362, numerator := 222404571877228810984226816 }, some { target := 363, numerator := 5782518868807949085589897216 }, some { target := 364, numerator := 5782518868807949085589897216 }, some { target := 365, numerator := 3050119842887709407783682048 }, some { target := 366, numerator := 71360095490893701352939061248 }, some { target := 367, numerator := 5718974705414455139594403840 }, some { target := 368, numerator := 2668854862526745731810721792 }, some { target := 369, numerator := 5782518868807949085589897216 }, some { target := 370, numerator := 222404571877228810984226816 }, some { target := 371, numerator := 5718974705414455139594403840 }, some { target := 372, numerator := 222404571877228810984226816 }, some { target := 373, numerator := 5782518868807949085589897216 }, some { target := 374, numerator := 5782518868807949085589897216 }, some { target := 375, numerator := 190632490180481837986480128 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 392, numerator := 152437990067032147498106880 }, some { target := 393, numerator := 2560958233126140077968195584 }, some { target := 394, numerator := 5548742838439970168931090432 }, some { target := 395, numerator := 182925588080438576997728256 }, some { target := 396, numerator := 2926809409287017231963652096 }, some { target := 397, numerator := 213413186093845006497349632 }, some { target := 398, numerator := 5548742838439970168931090432 }, some { target := 399, numerator := 5548742838439970168931090432 }, some { target := 400, numerator := 2926809409287017231963652096 }, some { target := 401, numerator := 68475145138110840656149610496 }, some { target := 402, numerator := 5487767642413157309931847680 }, some { target := 403, numerator := 2560958233126140077968195584 }, some { target := 404, numerator := 5548742838439970168931090432 }, some { target := 405, numerator := 213413186093845006497349632 }, some { target := 406, numerator := 5487767642413157309931847680 }, some { target := 407, numerator := 213413186093845006497349632 }, some { target := 408, numerator := 5548742838439970168931090432 }, some { target := 409, numerator := 5548742838439970168931090432 }, some { target := 410, numerator := 182925588080438576997728256 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 498, numerator := 4722366482869645213696000 }, some { target := 499, numerator := 79335756912210039590092800 }, some { target := 500, numerator := 171894139976455085778534400 }, some { target := 501, numerator := 5666839779443574256435200 }, some { target := 502, numerator := 90669436471097188102963200 }, some { target := 503, numerator := 6611313076017503299174400 }, some { target := 504, numerator := 171894139976455085778534400 }, some { target := 505, numerator := 171894139976455085778534400 }, some { target := 506, numerator := 90669436471097188102963200 }, some { target := 507, numerator := 2121287024105044629992243200 }, some { target := 508, numerator := 170005193383307227693056000 }, some { target := 509, numerator := 79335756912210039590092800 }, some { target := 510, numerator := 171894139976455085778534400 }, some { target := 511, numerator := 6611313076017503299174400 }, some { target := 512, numerator := 170005193383307227693056000 }, some { target := 513, numerator := 6611313076017503299174400 }, some { target := 514, numerator := 171894139976455085778534400 }, some { target := 515, numerator := 171894139976455085778534400 }, some { target := 516, numerator := 5666839779443574256435200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 573, numerator := 152437990067032147498106880 }, some { target := 574, numerator := 2560958233126140077968195584 }, some { target := 575, numerator := 5548742838439970168931090432 }, some { target := 576, numerator := 182925588080438576997728256 }, some { target := 577, numerator := 2926809409287017231963652096 }, some { target := 578, numerator := 213413186093845006497349632 }, some { target := 579, numerator := 5548742838439970168931090432 }, some { target := 580, numerator := 5548742838439970168931090432 }, some { target := 581, numerator := 2926809409287017231963652096 }, some { target := 582, numerator := 68475145138110840656149610496 }, some { target := 583, numerator := 5487767642413157309931847680 }, some { target := 584, numerator := 2560958233126140077968195584 }, some { target := 585, numerator := 5548742838439970168931090432 }, some { target := 586, numerator := 213413186093845006497349632 }, some { target := 587, numerator := 5487767642413157309931847680 }, some { target := 588, numerator := 213413186093845006497349632 }, some { target := 589, numerator := 5548742838439970168931090432 }, some { target := 590, numerator := 5548742838439970168931090432 }, some { target := 591, numerator := 182925588080438576997728256 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 608, numerator := 101814221370669550807285760 }, some { target := 609, numerator := 1710478919027248453562400768 }, some { target := 610, numerator := 3706037657892371649385201664 }, some { target := 611, numerator := 122177065644803460968742912 }, some { target := 612, numerator := 1954833050316855375499886592 }, some { target := 613, numerator := 142539909918937371130200064 }, some { target := 614, numerator := 3706037657892371649385201664 }, some { target := 615, numerator := 3706037657892371649385201664 }, some { target := 616, numerator := 1954833050316855375499886592 }, some { target := 617, numerator := 45734948239704762222632763392 }, some { target := 618, numerator := 3665311969344103829062287360 }, some { target := 619, numerator := 1710478919027248453562400768 }, some { target := 620, numerator := 3706037657892371649385201664 }, some { target := 621, numerator := 142539909918937371130200064 }, some { target := 622, numerator := 3665311969344103829062287360 }, some { target := 623, numerator := 142539909918937371130200064 }, some { target := 624, numerator := 3706037657892371649385201664 }, some { target := 625, numerator := 3706037657892371649385201664 }, some { target := 626, numerator := 122177065644803460968742912 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 669, numerator := 4911261142184431022243840 }, some { target := 670, numerator := 82509187188698441173696512 }, some { target := 671, numerator := 178769905575513289209675776 }, some { target := 672, numerator := 5893513370621317226692608 }, some { target := 673, numerator := 94296213929941075627081728 }, some { target := 674, numerator := 6875765599058203431141376 }, some { target := 675, numerator := 178769905575513289209675776 }, some { target := 676, numerator := 178769905575513289209675776 }, some { target := 677, numerator := 94296213929941075627081728 }, some { target := 678, numerator := 2206138505069246415191932928 }, some { target := 679, numerator := 176805401118639516800778240 }, some { target := 680, numerator := 82509187188698441173696512 }, some { target := 681, numerator := 178769905575513289209675776 }, some { target := 682, numerator := 6875765599058203431141376 }, some { target := 683, numerator := 176805401118639516800778240 }, some { target := 684, numerator := 6875765599058203431141376 }, some { target := 685, numerator := 178769905575513289209675776 }, some { target := 686, numerator := 178769905575513289209675776 }, some { target := 687, numerator := 5893513370621317226692608 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 704, numerator := 94636224316707690082467840 }, some { target := 705, numerator := 1589888568520689193385459712 }, some { target := 706, numerator := 3444758565128159919001829376 }, some { target := 707, numerator := 113563469180049228098961408 }, some { target := 708, numerator := 1817015506880787649583382528 }, some { target := 709, numerator := 132490714043390766115454976 }, some { target := 710, numerator := 3444758565128159919001829376 }, some { target := 711, numerator := 3444758565128159919001829376 }, some { target := 712, numerator := 1817015506880787649583382528 }, some { target := 713, numerator := 42510591963065094385044553728 }, some { target := 714, numerator := 3406904075401476842968842240 }, some { target := 715, numerator := 1589888568520689193385459712 }, some { target := 716, numerator := 3444758565128159919001829376 }, some { target := 717, numerator := 132490714043390766115454976 }, some { target := 718, numerator := 3406904075401476842968842240 }, some { target := 719, numerator := 132490714043390766115454976 }, some { target := 720, numerator := 3444758565128159919001829376 }, some { target := 721, numerator := 3444758565128159919001829376 }, some { target := 722, numerator := 113563469180049228098961408 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 739, numerator := 4533471823554859405148160 }, some { target := 740, numerator := 76162326635721638006489088 }, some { target := 741, numerator := 165018374377396882347393024 }, some { target := 742, numerator := 5440166188265831286177792 }, some { target := 743, numerator := 87042659012253300578844672 }, some { target := 744, numerator := 6346860552976803167207424 }, some { target := 745, numerator := 165018374377396882347393024 }, some { target := 746, numerator := 165018374377396882347393024 }, some { target := 747, numerator := 87042659012253300578844672 }, some { target := 748, numerator := 2036435543140842844792553472 }, some { target := 749, numerator := 163204985647974938585333760 }, some { target := 750, numerator := 76162326635721638006489088 }, some { target := 751, numerator := 165018374377396882347393024 }, some { target := 752, numerator := 6346860552976803167207424 }, some { target := 753, numerator := 163204985647974938585333760 }, some { target := 754, numerator := 6346860552976803167207424 }, some { target := 755, numerator := 165018374377396882347393024 }, some { target := 756, numerator := 165018374377396882347393024 }, some { target := 757, numerator := 5440166188265831286177792 }]

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

end Slot2

namespace Slot3

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨3, 12, #[70368744177664, 70368744177664, 70368744177664, 70368744177664, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3648641826816, 0, 137088846528512, 0, 0, 137078478209024, 0, 0, 0, 0, 0, 0, 3659010146304, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

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
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 411, numerator := 3081004119685676887481253888 }, some { target := 413, numerator := 115761239651710829502834671616 }, some { target := 416, numerator := 115752484384251589180608479232 }, some { target := 423, numerator := 3089759387144917209707446272 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 627, numerator := 3081004119685676887481253888 }, some { target := 629, numerator := 115761239651710829502834671616 }, some { target := 632, numerator := 115752484384251589180608479232 }, some { target := 639, numerator := 3089759387144917209707446272 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 723, numerator := 3081004119685676887481253888 }, some { target := 725, numerator := 115761239651710829502834671616 }, some { target := 728, numerator := 115752484384251589180608479232 }, some { target := 735, numerator := 3089759387144917209707446272 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 758, numerator := 3081004119685676887481253888 }, some { target := 760, numerator := 115761239651710829502834671616 }, some { target := 763, numerator := 115752484384251589180608479232 }, some { target := 770, numerator := 3089759387144917209707446272 }]

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

end Slot3

namespace Slot4

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨4, 39, #[24086361145344, 0, 233302254419968, 0, 0, 0, 0, 24086361145344, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[147035521024, 23473808211968, 0, 234233306021888, 0, 0, 0, 0, 0, 0, 0, 23473808211968, 0, 0, 0, 0, 0, 0, 147018743808]⟩

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
  [some { target := 142, numerator := 138120475762537492836777984 }, some { target := 143, numerator := 22050546259950115019122802688 }, some { target := 145, numerator := 220031292043331882100518289408 }, some { target := 153, numerator := 22050546259950115019122802688 }, some { target := 160, numerator := 138104715781277504533168128 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 357, numerator := 1337845022853838269786882048 }, some { target := 358, numerator := 213583202651289606058395303936 }, some { target := 360, numerator := 2131239175850800735159138123776 }, some { target := 368, numerator := 213583202651289606058395303936 }, some { target := 375, numerator := 1337692370523526330230767616 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 669, numerator := 138120475762537492836777984 }, some { target := 670, numerator := 22050546259950115019122802688 }, some { target := 672, numerator := 220031292043331882100518289408 }, some { target := 680, numerator := 22050546259950115019122802688 }, some { target := 687, numerator := 138104715781277504533168128 }]

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

end Slot4

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9.Parent2
