import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk9Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 3, for region 1, branch 2,
parent 40; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot12

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨12, 8, #[343597383680, 5772436045824, 12506944765952, 412316860416, 6597069766656, 481036337152, 12506944765952, 12506944765952, 6597069766656, 154343944749056, 12369505812480, 5772436045824, 12506944765952, 481036337152, 12369505812480, 481036337152, 12506944765952, 12506944765952, 412316860416], #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes

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
        6 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total6.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 11, numerator := 4722366482869645213696000 }, some { target := 12, numerator := 94636224316707690082467840 }, some { target := 13, numerator := 158860408483734864988733440 }, some { target := 14, numerator := 152437990067032147498106880 }, some { target := 15, numerator := 4722366482869645213696000 }, some { target := 16, numerator := 152437990067032147498106880 }, some { target := 17, numerator := 101814221370669550807285760 }, some { target := 18, numerator := 4911261142184431022243840 }, some { target := 19, numerator := 94636224316707690082467840 }, some { target := 20, numerator := 4533471823554859405148160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 31, numerator := 79335756912210039590092800 }, some { target := 32, numerator := 1589888568520689193385459712 }, some { target := 33, numerator := 2668854862526745731810721792 }, some { target := 34, numerator := 2560958233126140077968195584 }, some { target := 35, numerator := 79335756912210039590092800 }, some { target := 36, numerator := 2560958233126140077968195584 }, some { target := 37, numerator := 1710478919027248453562400768 }, some { target := 38, numerator := 82509187188698441173696512 }, some { target := 39, numerator := 1589888568520689193385459712 }, some { target := 40, numerator := 76162326635721638006489088 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 45, numerator := 171894139976455085778534400 }, some { target := 46, numerator := 3444758565128159919001829376 }, some { target := 47, numerator := 5782518868807949085589897216 }, some { target := 48, numerator := 5548742838439970168931090432 }, some { target := 49, numerator := 171894139976455085778534400 }, some { target := 50, numerator := 5548742838439970168931090432 }, some { target := 51, numerator := 3706037657892371649385201664 }, some { target := 52, numerator := 178769905575513289209675776 }, some { target := 53, numerator := 3444758565128159919001829376 }, some { target := 54, numerator := 165018374377396882347393024 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 76, numerator := 5666839779443574256435200 }, some { target := 77, numerator := 113563469180049228098961408 }, some { target := 78, numerator := 190632490180481837986480128 }, some { target := 79, numerator := 182925588080438576997728256 }, some { target := 80, numerator := 5666839779443574256435200 }, some { target := 81, numerator := 182925588080438576997728256 }, some { target := 82, numerator := 122177065644803460968742912 }, some { target := 83, numerator := 5893513370621317226692608 }, some { target := 84, numerator := 113563469180049228098961408 }, some { target := 85, numerator := 5440166188265831286177792 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 90, numerator := 90669436471097188102963200 }, some { target := 91, numerator := 1817015506880787649583382528 }, some { target := 92, numerator := 3050119842887709407783682048 }, some { target := 93, numerator := 2926809409287017231963652096 }, some { target := 94, numerator := 90669436471097188102963200 }, some { target := 95, numerator := 2926809409287017231963652096 }, some { target := 96, numerator := 1954833050316855375499886592 }, some { target := 97, numerator := 94296213929941075627081728 }, some { target := 98, numerator := 1817015506880787649583382528 }, some { target := 99, numerator := 87042659012253300578844672 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 116, numerator := 6611313076017503299174400 }, some { target := 117, numerator := 132490714043390766115454976 }, some { target := 118, numerator := 222404571877228810984226816 }, some { target := 119, numerator := 213413186093845006497349632 }, some { target := 120, numerator := 6611313076017503299174400 }, some { target := 121, numerator := 213413186093845006497349632 }, some { target := 122, numerator := 142539909918937371130200064 }, some { target := 123, numerator := 6875765599058203431141376 }, some { target := 124, numerator := 132490714043390766115454976 }, some { target := 125, numerator := 6346860552976803167207424 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 171, numerator := 171894139976455085778534400 }, some { target := 172, numerator := 3444758565128159919001829376 }, some { target := 173, numerator := 5782518868807949085589897216 }, some { target := 174, numerator := 5548742838439970168931090432 }, some { target := 175, numerator := 171894139976455085778534400 }, some { target := 176, numerator := 5548742838439970168931090432 }, some { target := 177, numerator := 3706037657892371649385201664 }, some { target := 178, numerator := 178769905575513289209675776 }, some { target := 179, numerator := 3444758565128159919001829376 }, some { target := 180, numerator := 165018374377396882347393024 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 185, numerator := 171894139976455085778534400 }, some { target := 186, numerator := 3444758565128159919001829376 }, some { target := 187, numerator := 5782518868807949085589897216 }, some { target := 188, numerator := 5548742838439970168931090432 }, some { target := 189, numerator := 171894139976455085778534400 }, some { target := 190, numerator := 5548742838439970168931090432 }, some { target := 191, numerator := 3706037657892371649385201664 }, some { target := 192, numerator := 178769905575513289209675776 }, some { target := 193, numerator := 3444758565128159919001829376 }, some { target := 194, numerator := 165018374377396882347393024 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 216, numerator := 90669436471097188102963200 }, some { target := 217, numerator := 1817015506880787649583382528 }, some { target := 218, numerator := 3050119842887709407783682048 }, some { target := 219, numerator := 2926809409287017231963652096 }, some { target := 220, numerator := 90669436471097188102963200 }, some { target := 221, numerator := 2926809409287017231963652096 }, some { target := 222, numerator := 1954833050316855375499886592 }, some { target := 223, numerator := 94296213929941075627081728 }, some { target := 224, numerator := 1817015506880787649583382528 }, some { target := 225, numerator := 87042659012253300578844672 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 230, numerator := 2121287024105044629992243200 }, some { target := 231, numerator := 42510591963065094385044553728 }, some { target := 232, numerator := 71360095490893701352939061248 }, some { target := 233, numerator := 68475145138110840656149610496 }, some { target := 234, numerator := 2121287024105044629992243200 }, some { target := 235, numerator := 68475145138110840656149610496 }, some { target := 236, numerator := 45734948239704762222632763392 }, some { target := 237, numerator := 2206138505069246415191932928 }, some { target := 238, numerator := 42510591963065094385044553728 }, some { target := 239, numerator := 2036435543140842844792553472 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 256, numerator := 170005193383307227693056000 }, some { target := 257, numerator := 3406904075401476842968842240 }, some { target := 258, numerator := 5718974705414455139594403840 }, some { target := 259, numerator := 5487767642413157309931847680 }, some { target := 260, numerator := 170005193383307227693056000 }, some { target := 261, numerator := 5487767642413157309931847680 }, some { target := 262, numerator := 3665311969344103829062287360 }, some { target := 263, numerator := 176805401118639516800778240 }, some { target := 264, numerator := 3406904075401476842968842240 }, some { target := 265, numerator := 163204985647974938585333760 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 305, numerator := 79335756912210039590092800 }, some { target := 306, numerator := 1589888568520689193385459712 }, some { target := 307, numerator := 2668854862526745731810721792 }, some { target := 308, numerator := 2560958233126140077968195584 }, some { target := 309, numerator := 79335756912210039590092800 }, some { target := 310, numerator := 2560958233126140077968195584 }, some { target := 311, numerator := 1710478919027248453562400768 }, some { target := 312, numerator := 82509187188698441173696512 }, some { target := 313, numerator := 1589888568520689193385459712 }, some { target := 314, numerator := 76162326635721638006489088 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 331, numerator := 171894139976455085778534400 }, some { target := 332, numerator := 3444758565128159919001829376 }, some { target := 333, numerator := 5782518868807949085589897216 }, some { target := 334, numerator := 5548742838439970168931090432 }, some { target := 335, numerator := 171894139976455085778534400 }, some { target := 336, numerator := 5548742838439970168931090432 }, some { target := 337, numerator := 3706037657892371649385201664 }, some { target := 338, numerator := 178769905575513289209675776 }, some { target := 339, numerator := 3444758565128159919001829376 }, some { target := 340, numerator := 165018374377396882347393024 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 432, numerator := 6611313076017503299174400 }, some { target := 433, numerator := 132490714043390766115454976 }, some { target := 434, numerator := 222404571877228810984226816 }, some { target := 435, numerator := 213413186093845006497349632 }, some { target := 436, numerator := 6611313076017503299174400 }, some { target := 437, numerator := 213413186093845006497349632 }, some { target := 438, numerator := 142539909918937371130200064 }, some { target := 439, numerator := 6875765599058203431141376 }, some { target := 440, numerator := 132490714043390766115454976 }, some { target := 441, numerator := 6346860552976803167207424 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 446, numerator := 170005193383307227693056000 }, some { target := 447, numerator := 3406904075401476842968842240 }, some { target := 448, numerator := 5718974705414455139594403840 }, some { target := 449, numerator := 5487767642413157309931847680 }, some { target := 450, numerator := 170005193383307227693056000 }, some { target := 451, numerator := 5487767642413157309931847680 }, some { target := 452, numerator := 3665311969344103829062287360 }, some { target := 453, numerator := 176805401118639516800778240 }, some { target := 454, numerator := 3406904075401476842968842240 }, some { target := 455, numerator := 163204985647974938585333760 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 472, numerator := 6611313076017503299174400 }, some { target := 473, numerator := 132490714043390766115454976 }, some { target := 474, numerator := 222404571877228810984226816 }, some { target := 475, numerator := 213413186093845006497349632 }, some { target := 476, numerator := 6611313076017503299174400 }, some { target := 477, numerator := 213413186093845006497349632 }, some { target := 478, numerator := 142539909918937371130200064 }, some { target := 479, numerator := 6875765599058203431141376 }, some { target := 480, numerator := 132490714043390766115454976 }, some { target := 481, numerator := 6346860552976803167207424 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 15 = expected := by
  rfl

end Left15

namespace Left16

/-- Producer-proposed routed output for left symbol 16; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 521, numerator := 171894139976455085778534400 }, some { target := 522, numerator := 3444758565128159919001829376 }, some { target := 523, numerator := 5782518868807949085589897216 }, some { target := 524, numerator := 5548742838439970168931090432 }, some { target := 525, numerator := 171894139976455085778534400 }, some { target := 526, numerator := 5548742838439970168931090432 }, some { target := 527, numerator := 3706037657892371649385201664 }, some { target := 528, numerator := 178769905575513289209675776 }, some { target := 529, numerator := 3444758565128159919001829376 }, some { target := 530, numerator := 165018374377396882347393024 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 16 = expected := by
  rfl

end Left16

namespace Left17

/-- Producer-proposed routed output for left symbol 17; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 547, numerator := 171894139976455085778534400 }, some { target := 548, numerator := 3444758565128159919001829376 }, some { target := 549, numerator := 5782518868807949085589897216 }, some { target := 550, numerator := 5548742838439970168931090432 }, some { target := 551, numerator := 171894139976455085778534400 }, some { target := 552, numerator := 5548742838439970168931090432 }, some { target := 553, numerator := 3706037657892371649385201664 }, some { target := 554, numerator := 178769905575513289209675776 }, some { target := 555, numerator := 3444758565128159919001829376 }, some { target := 556, numerator := 165018374377396882347393024 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 17 = expected := by
  rfl

end Left17

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 643, numerator := 5666839779443574256435200 }, some { target := 644, numerator := 113563469180049228098961408 }, some { target := 645, numerator := 190632490180481837986480128 }, some { target := 646, numerator := 182925588080438576997728256 }, some { target := 647, numerator := 5666839779443574256435200 }, some { target := 648, numerator := 182925588080438576997728256 }, some { target := 649, numerator := 122177065644803460968742912 }, some { target := 650, numerator := 5893513370621317226692608 }, some { target := 651, numerator := 113563469180049228098961408 }, some { target := 652, numerator := 5440166188265831286177792 }]

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

end Slot12

namespace Slot13

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨13, 5, #[3710583308288, 0, 137026905047040, 0, 0, 137026871492608, 0, 0, 0, 0, 0, 0, 3710616862720, 0, 0, 0, 0, 0, 0], #[73529840107520, 67207648247808, 73529840107520, 67207648247808, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 2, numerator := 1364192986820246156135628800 }, some { target := 3, numerator := 1246897888888038075421163520 }, some { target := 4, numerator := 1364192986820246156135628800 }, some { target := 5, numerator := 1246897888888038075421163520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 22, numerator := 50377832092685882521288704000 }, some { target := 23, numerator := 46046280174436255239084441600 }, some { target := 24, numerator := 50377832092685882521288704000 }, some { target := 25, numerator := 46046280174436255239084441600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 72, numerator := 50377819756425783228026060800 }, some { target := 73, numerator := 46046268898863940184121016320 }, some { target := 74, numerator := 50377819756425783228026060800 }, some { target := 75, numerator := 46046268898863940184121016320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 301, numerator := 1364205323080345449398272000 }, some { target := 302, numerator := 1246909164460353130384588800 }, some { target := 303, numerator := 1364205323080345449398272000 }, some { target := 304, numerator := 1246909164460353130384588800 }]

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

end Slot13

namespace Slot14

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨14, 5, #[49931561730048, 0, 0, 181611853250560, 0, 49931561730048, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total8.codes

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
        8 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total8.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 0, numerator := 70272425875459716058384957440 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 21, numerator := 255595960820402255850949836800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 71, numerator := 70272425875459716058384957440 }]

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

end Slot14

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9.Parent2
