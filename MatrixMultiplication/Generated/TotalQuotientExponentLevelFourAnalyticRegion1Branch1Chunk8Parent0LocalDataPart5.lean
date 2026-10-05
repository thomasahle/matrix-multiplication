import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk8Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 5, for region 1, branch 1,
parent 34; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot22

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨22, 775, #[206963736576, 24461784907776, 0, 232137462644736, 0, 0, 0, 0, 0, 0, 0, 24461801684992, 0, 0, 0, 0, 0, 0, 206963736576], #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416]⟩

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
  [some { target := 71, numerator := 66134344515859798976102400 }, some { target := 72, numerator := 958947995479967085153484800 }, some { target := 73, numerator := 1697448175907068173719961600 }, some { target := 74, numerator := 55111953763216499146752000 }, some { target := 75, numerator := 1058149512253756783617638400 }, some { target := 76, numerator := 55111953763216499146752000 }, some { target := 77, numerator := 1686425785154424873890611200 }, some { target := 78, numerator := 1763582520422927972696064000 }, some { target := 79, numerator := 1058149512253756783617638400 }, some { target := 80, numerator := 27015879734728727881737830400 }, some { target := 81, numerator := 1730515348164998073208012800 }, some { target := 82, numerator := 958947995479967085153484800 }, some { target := 83, numerator := 1686425785154424873890611200 }, some { target := 84, numerator := 55111953763216499146752000 }, some { target := 85, numerator := 1730515348164998073208012800 }, some { target := 86, numerator := 55111953763216499146752000 }, some { target := 87, numerator := 1686425785154424873890611200 }, some { target := 88, numerator := 1763582520422927972696064000 }, some { target := 89, numerator := 66134344515859798976102400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 146, numerator := 7816654923842911629370982400 }, some { target := 147, numerator := 113341496395722218625879244800 }, some { target := 148, numerator := 200627476378634731820521881600 }, some { target := 149, numerator := 6513879103202426357809152000 }, some { target := 150, numerator := 125066478781486586069935718400 }, some { target := 151, numerator := 6513879103202426357809152000 }, some { target := 152, numerator := 199324700557994246548960051200 }, some { target := 153, numerator := 208444131302477643449892864000 }, some { target := 154, numerator := 125066478781486586069935718400 }, some { target := 155, numerator := 3193103536389829400598046310400 }, some { target := 156, numerator := 204535803840556187635207372800 }, some { target := 157, numerator := 113341496395722218625879244800 }, some { target := 158, numerator := 199324700557994246548960051200 }, some { target := 159, numerator := 6513879103202426357809152000 }, some { target := 160, numerator := 204535803840556187635207372800 }, some { target := 161, numerator := 6513879103202426357809152000 }, some { target := 162, numerator := 199324700557994246548960051200 }, some { target := 163, numerator := 208444131302477643449892864000 }, some { target := 164, numerator := 7816654923842911629370982400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 242, numerator := 74178497081525871319606886400 }, some { target := 243, numerator := 1075588207682125134134299852800 }, some { target := 244, numerator := 1903914758425830697203243417600 }, some { target := 245, numerator := 61815414234604892766339072000 }, some { target := 246, numerator := 1186855953304413941113710182400 }, some { target := 247, numerator := 61815414234604892766339072000 }, some { target := 248, numerator := 1891551675578909718649975603200 }, some { target := 249, numerator := 1978093255507356568522850304000 }, some { target := 250, numerator := 1186855953304413941113710182400 }, some { target := 251, numerator := 30301916057803318434059413094400 }, some { target := 252, numerator := 1941004006966593632863046860800 }, some { target := 253, numerator := 1075588207682125134134299852800 }, some { target := 254, numerator := 1891551675578909718649975603200 }, some { target := 255, numerator := 61815414234604892766339072000 }, some { target := 256, numerator := 1941004006966593632863046860800 }, some { target := 257, numerator := 61815414234604892766339072000 }, some { target := 258, numerator := 1891551675578909718649975603200 }, some { target := 259, numerator := 1978093255507356568522850304000 }, some { target := 260, numerator := 74178497081525871319606886400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 640, numerator := 7816660284927908051209420800 }, some { target := 641, numerator := 113341574131454666742536601600 }, some { target := 642, numerator := 200627613979816306647708467200 }, some { target := 643, numerator := 6513883570773256709341184000 }, some { target := 644, numerator := 125066564558846528819350732800 }, some { target := 645, numerator := 6513883570773256709341184000 }, some { target := 646, numerator := 199324837265661655305840230400 }, some { target := 647, numerator := 208444274264744214698917888000 }, some { target := 648, numerator := 125066564558846528819350732800 }, some { target := 649, numerator := 3193105726393050438919048396800 }, some { target := 650, numerator := 204535944122280260673313177600 }, some { target := 651, numerator := 113341574131454666742536601600 }, some { target := 652, numerator := 199324837265661655305840230400 }, some { target := 653, numerator := 6513883570773256709341184000 }, some { target := 654, numerator := 204535944122280260673313177600 }, some { target := 655, numerator := 6513883570773256709341184000 }, some { target := 656, numerator := 199324837265661655305840230400 }, some { target := 657, numerator := 208444274264744214698917888000 }, some { target := 658, numerator := 7816660284927908051209420800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1017, numerator := 66134344515859798976102400 }, some { target := 1018, numerator := 958947995479967085153484800 }, some { target := 1019, numerator := 1697448175907068173719961600 }, some { target := 1020, numerator := 55111953763216499146752000 }, some { target := 1021, numerator := 1058149512253756783617638400 }, some { target := 1022, numerator := 55111953763216499146752000 }, some { target := 1023, numerator := 1686425785154424873890611200 }, some { target := 1024, numerator := 1763582520422927972696064000 }, some { target := 1025, numerator := 1058149512253756783617638400 }, some { target := 1026, numerator := 27015879734728727881737830400 }, some { target := 1027, numerator := 1730515348164998073208012800 }, some { target := 1028, numerator := 958947995479967085153484800 }, some { target := 1029, numerator := 1686425785154424873890611200 }, some { target := 1030, numerator := 55111953763216499146752000 }, some { target := 1031, numerator := 1730515348164998073208012800 }, some { target := 1032, numerator := 55111953763216499146752000 }, some { target := 1033, numerator := 1686425785154424873890611200 }, some { target := 1034, numerator := 1763582520422927972696064000 }, some { target := 1035, numerator := 66134344515859798976102400 }]

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

end Slot22

namespace Slot23

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨23, 22, #[3298534883328, 2473901162496, 2611340115968, 3367254360064, 45079976738816, 78821239816192, 2405181685760, 45079976738816, 2542620639232, 2611340115968, 2611340115968, 2542620639232, 78821239816192, 2542620639232, 3298534883328, 3367254360064, 0, 0, 0], #[2130303778816, 2405181685760, 2061584302080, 27144193310720, 2405181685760, 2061584302080, 2405181685760, 2405181685760, 99711960743936, 2473901162496, 27144193310720, 99711960743936, 2130303778816, 2405181685760, 2473901162496, 2405181685760, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

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
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 200, numerator := 154591389183220705715552256 }, some { target := 201, numerator := 174538665206862087098204160 }, some { target := 202, numerator := 149604570177310360369889280 }, some { target := 203, numerator := 1969793507334586411536875520 }, some { target := 204, numerator := 174538665206862087098204160 }, some { target := 205, numerator := 149604570177310360369889280 }, some { target := 206, numerator := 174538665206862087098204160 }, some { target := 207, numerator := 174538665206862087098204160 }, some { target := 208, numerator := 7235874377575911096556978176 }, some { target := 209, numerator := 179525484212772432443867136 }, some { target := 210, numerator := 1969793507334586411536875520 }, some { target := 211, numerator := 7235874377575911096556978176 }, some { target := 212, numerator := 154591389183220705715552256 }, some { target := 213, numerator := 174538665206862087098204160 }, some { target := 214, numerator := 179525484212772432443867136 }, some { target := 215, numerator := 174538665206862087098204160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 296, numerator := 115943541887415529286664192 }, some { target := 297, numerator := 130903998905146565323653120 }, some { target := 298, numerator := 112203427632982770277416960 }, some { target := 299, numerator := 1477345130500939808652656640 }, some { target := 300, numerator := 130903998905146565323653120 }, some { target := 301, numerator := 112203427632982770277416960 }, some { target := 302, numerator := 130903998905146565323653120 }, some { target := 303, numerator := 130903998905146565323653120 }, some { target := 304, numerator := 5426905783181933322417733632 }, some { target := 305, numerator := 134644113159579324332900352 }, some { target := 306, numerator := 1477345130500939808652656640 }, some { target := 307, numerator := 5426905783181933322417733632 }, some { target := 308, numerator := 115943541887415529286664192 }, some { target := 309, numerator := 130903998905146565323653120 }, some { target := 310, numerator := 134644113159579324332900352 }, some { target := 311, numerator := 130903998905146565323653120 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 331, numerator := 122384849770049725358145536 }, some { target := 332, numerator := 138176443288765818952744960 }, some { target := 333, numerator := 118436951390370701959495680 }, some { target := 334, numerator := 1559419859973214242466693120 }, some { target := 335, numerator := 138176443288765818952744960 }, some { target := 336, numerator := 118436951390370701959495680 }, some { target := 337, numerator := 138176443288765818952744960 }, some { target := 338, numerator := 138176443288765818952744960 }, some { target := 339, numerator := 5728400548914262951440941056 }, some { target := 340, numerator := 142124341668444842351394816 }, some { target := 341, numerator := 1559419859973214242466693120 }, some { target := 342, numerator := 5728400548914262951440941056 }, some { target := 343, numerator := 122384849770049725358145536 }, some { target := 344, numerator := 138176443288765818952744960 }, some { target := 345, numerator := 142124341668444842351394816 }, some { target := 346, numerator := 138176443288765818952744960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 467, numerator := 157812043124537803751292928 }, some { target := 468, numerator := 178174887398671713912750080 }, some { target := 469, numerator := 152721332056004326210928640 }, some { target := 470, numerator := 2010830872070723628443893760 }, some { target := 471, numerator := 178174887398671713912750080 }, some { target := 472, numerator := 152721332056004326210928640 }, some { target := 473, numerator := 178174887398671713912750080 }, some { target := 474, numerator := 178174887398671713912750080 }, some { target := 475, numerator := 7386621760442075911068581888 }, some { target := 476, numerator := 183265598467205191453114368 }, some { target := 477, numerator := 2010830872070723628443893760 }, some { target := 478, numerator := 7386621760442075911068581888 }, some { target := 479, numerator := 157812043124537803751292928 }, some { target := 480, numerator := 178174887398671713912750080 }, some { target := 481, numerator := 183265598467205191453114368 }, some { target := 482, numerator := 178174887398671713912750080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left4

/-- Producer-proposed routed output for left symbol 4; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 563, numerator := 2112748985504016311445880832 }, some { target := 564, numerator := 2385361757827115190342123520 }, some { target := 565, numerator := 2044595792423241591721820160 }, some { target := 566, numerator := 26920511266906014291003965440 }, some { target := 567, numerator := 2385361757827115190342123520 }, some { target := 568, numerator := 2044595792423241591721820160 }, some { target := 569, numerator := 2385361757827115190342123520 }, some { target := 570, numerator := 2385361757827115190342123520 }, some { target := 571, numerator := 98890283160204118319612035072 }, some { target := 572, numerator := 2453514950907889910066184192 }, some { target := 573, numerator := 26920511266906014291003965440 }, some { target := 574, numerator := 98890283160204118319612035072 }, some { target := 575, numerator := 2112748985504016311445880832 }, some { target := 576, numerator := 2385361757827115190342123520 }, some { target := 577, numerator := 2453514950907889910066184192 }, some { target := 578, numerator := 2385361757827115190342123520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 4 = expected := by
  rfl

end Left4

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 598, numerator := 3694090070690711446994550784 }, some { target := 599, numerator := 4170746854005641956284170240 }, some { target := 600, numerator := 3574925874861978819672145920 }, some { target := 601, numerator := 47069857352349387792349921280 }, some { target := 602, numerator := 4170746854005641956284170240 }, some { target := 603, numerator := 3574925874861978819672145920 }, some { target := 604, numerator := 4170746854005641956284170240 }, some { target := 605, numerator := 4170746854005641956284170240 }, some { target := 606, numerator := 172907248147491042244809457664 }, some { target := 607, numerator := 4289911049834374583606575104 }, some { target := 608, numerator := 47069857352349387792349921280 }, some { target := 609, numerator := 172907248147491042244809457664 }, some { target := 610, numerator := 3694090070690711446994550784 }, some { target := 611, numerator := 4170746854005641956284170240 }, some { target := 612, numerator := 4289911049834374583606575104 }, some { target := 613, numerator := 4170746854005641956284170240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 659, numerator := 112722887946098431250923520 }, some { target := 660, numerator := 127267776713336938509107200 }, some { target := 661, numerator := 109086665754288804436377600 }, some { target := 662, numerator := 1436307765764802591745638400 }, some { target := 663, numerator := 127267776713336938509107200 }, some { target := 664, numerator := 109086665754288804436377600 }, some { target := 665, numerator := 127267776713336938509107200 }, some { target := 666, numerator := 127267776713336938509107200 }, some { target := 667, numerator := 5276158400315768507906129920 }, some { target := 668, numerator := 130903998905146565323653120 }, some { target := 669, numerator := 1436307765764802591745638400 }, some { target := 670, numerator := 5276158400315768507906129920 }, some { target := 671, numerator := 112722887946098431250923520 }, some { target := 672, numerator := 127267776713336938509107200 }, some { target := 673, numerator := 130903998905146565323653120 }, some { target := 674, numerator := 127267776713336938509107200 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 694, numerator := 2112748985504016311445880832 }, some { target := 695, numerator := 2385361757827115190342123520 }, some { target := 696, numerator := 2044595792423241591721820160 }, some { target := 697, numerator := 26920511266906014291003965440 }, some { target := 698, numerator := 2385361757827115190342123520 }, some { target := 699, numerator := 2044595792423241591721820160 }, some { target := 700, numerator := 2385361757827115190342123520 }, some { target := 701, numerator := 2385361757827115190342123520 }, some { target := 702, numerator := 98890283160204118319612035072 }, some { target := 703, numerator := 2453514950907889910066184192 }, some { target := 704, numerator := 26920511266906014291003965440 }, some { target := 705, numerator := 98890283160204118319612035072 }, some { target := 706, numerator := 2112748985504016311445880832 }, some { target := 707, numerator := 2385361757827115190342123520 }, some { target := 708, numerator := 2453514950907889910066184192 }, some { target := 709, numerator := 2385361757827115190342123520 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 7 = expected := by
  rfl

end Left7

namespace Left8

/-- Producer-proposed routed output for left symbol 8; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 720, numerator := 119164195828732627322404864 }, some { target := 721, numerator := 134540221096956192138199040 }, some { target := 722, numerator := 115320189511676736118456320 }, some { target := 723, numerator := 1518382495237077025559674880 }, some { target := 724, numerator := 134540221096956192138199040 }, some { target := 725, numerator := 115320189511676736118456320 }, some { target := 726, numerator := 134540221096956192138199040 }, some { target := 727, numerator := 134540221096956192138199040 }, some { target := 728, numerator := 5577653166048098136929337344 }, some { target := 729, numerator := 138384227414012083342147584 }, some { target := 730, numerator := 1518382495237077025559674880 }, some { target := 731, numerator := 5577653166048098136929337344 }, some { target := 732, numerator := 119164195828732627322404864 }, some { target := 733, numerator := 134540221096956192138199040 }, some { target := 734, numerator := 138384227414012083342147584 }, some { target := 735, numerator := 134540221096956192138199040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 8 = expected := by
  rfl

end Left8

namespace Left9

/-- Producer-proposed routed output for left symbol 9; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 830, numerator := 122384849770049725358145536 }, some { target := 831, numerator := 138176443288765818952744960 }, some { target := 832, numerator := 118436951390370701959495680 }, some { target := 833, numerator := 1559419859973214242466693120 }, some { target := 834, numerator := 138176443288765818952744960 }, some { target := 835, numerator := 118436951390370701959495680 }, some { target := 836, numerator := 138176443288765818952744960 }, some { target := 837, numerator := 138176443288765818952744960 }, some { target := 838, numerator := 5728400548914262951440941056 }, some { target := 839, numerator := 142124341668444842351394816 }, some { target := 840, numerator := 1559419859973214242466693120 }, some { target := 841, numerator := 5728400548914262951440941056 }, some { target := 842, numerator := 122384849770049725358145536 }, some { target := 843, numerator := 138176443288765818952744960 }, some { target := 844, numerator := 142124341668444842351394816 }, some { target := 845, numerator := 138176443288765818952744960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 9 = expected := by
  rfl

end Left9

namespace Left10

/-- Producer-proposed routed output for left symbol 10; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 865, numerator := 122384849770049725358145536 }, some { target := 866, numerator := 138176443288765818952744960 }, some { target := 867, numerator := 118436951390370701959495680 }, some { target := 868, numerator := 1559419859973214242466693120 }, some { target := 869, numerator := 138176443288765818952744960 }, some { target := 870, numerator := 118436951390370701959495680 }, some { target := 871, numerator := 138176443288765818952744960 }, some { target := 872, numerator := 138176443288765818952744960 }, some { target := 873, numerator := 5728400548914262951440941056 }, some { target := 874, numerator := 142124341668444842351394816 }, some { target := 875, numerator := 1559419859973214242466693120 }, some { target := 876, numerator := 5728400548914262951440941056 }, some { target := 877, numerator := 122384849770049725358145536 }, some { target := 878, numerator := 138176443288765818952744960 }, some { target := 879, numerator := 142124341668444842351394816 }, some { target := 880, numerator := 138176443288765818952744960 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 10 = expected := by
  rfl

end Left10

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 926, numerator := 119164195828732627322404864 }, some { target := 927, numerator := 134540221096956192138199040 }, some { target := 928, numerator := 115320189511676736118456320 }, some { target := 929, numerator := 1518382495237077025559674880 }, some { target := 930, numerator := 134540221096956192138199040 }, some { target := 931, numerator := 115320189511676736118456320 }, some { target := 932, numerator := 134540221096956192138199040 }, some { target := 933, numerator := 134540221096956192138199040 }, some { target := 934, numerator := 5577653166048098136929337344 }, some { target := 935, numerator := 138384227414012083342147584 }, some { target := 936, numerator := 1518382495237077025559674880 }, some { target := 937, numerator := 5577653166048098136929337344 }, some { target := 938, numerator := 119164195828732627322404864 }, some { target := 939, numerator := 134540221096956192138199040 }, some { target := 940, numerator := 138384227414012083342147584 }, some { target := 941, numerator := 134540221096956192138199040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 961, numerator := 3694090070690711446994550784 }, some { target := 962, numerator := 4170746854005641956284170240 }, some { target := 963, numerator := 3574925874861978819672145920 }, some { target := 964, numerator := 47069857352349387792349921280 }, some { target := 965, numerator := 4170746854005641956284170240 }, some { target := 966, numerator := 3574925874861978819672145920 }, some { target := 967, numerator := 4170746854005641956284170240 }, some { target := 968, numerator := 4170746854005641956284170240 }, some { target := 969, numerator := 172907248147491042244809457664 }, some { target := 970, numerator := 4289911049834374583606575104 }, some { target := 971, numerator := 47069857352349387792349921280 }, some { target := 972, numerator := 172907248147491042244809457664 }, some { target := 973, numerator := 3694090070690711446994550784 }, some { target := 974, numerator := 4170746854005641956284170240 }, some { target := 975, numerator := 4289911049834374583606575104 }, some { target := 976, numerator := 4170746854005641956284170240 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 12 = expected := by
  rfl

end Left12

namespace Left13

/-- Producer-proposed routed output for left symbol 13; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 987, numerator := 119164195828732627322404864 }, some { target := 988, numerator := 134540221096956192138199040 }, some { target := 989, numerator := 115320189511676736118456320 }, some { target := 990, numerator := 1518382495237077025559674880 }, some { target := 991, numerator := 134540221096956192138199040 }, some { target := 992, numerator := 115320189511676736118456320 }, some { target := 993, numerator := 134540221096956192138199040 }, some { target := 994, numerator := 134540221096956192138199040 }, some { target := 995, numerator := 5577653166048098136929337344 }, some { target := 996, numerator := 138384227414012083342147584 }, some { target := 997, numerator := 1518382495237077025559674880 }, some { target := 998, numerator := 5577653166048098136929337344 }, some { target := 999, numerator := 119164195828732627322404864 }, some { target := 1000, numerator := 134540221096956192138199040 }, some { target := 1001, numerator := 138384227414012083342147584 }, some { target := 1002, numerator := 134540221096956192138199040 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 13 = expected := by
  rfl

end Left13

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1036, numerator := 154591389183220705715552256 }, some { target := 1037, numerator := 174538665206862087098204160 }, some { target := 1038, numerator := 149604570177310360369889280 }, some { target := 1039, numerator := 1969793507334586411536875520 }, some { target := 1040, numerator := 174538665206862087098204160 }, some { target := 1041, numerator := 149604570177310360369889280 }, some { target := 1042, numerator := 174538665206862087098204160 }, some { target := 1043, numerator := 174538665206862087098204160 }, some { target := 1044, numerator := 7235874377575911096556978176 }, some { target := 1045, numerator := 179525484212772432443867136 }, some { target := 1046, numerator := 1969793507334586411536875520 }, some { target := 1047, numerator := 7235874377575911096556978176 }, some { target := 1048, numerator := 154591389183220705715552256 }, some { target := 1049, numerator := 174538665206862087098204160 }, some { target := 1050, numerator := 179525484212772432443867136 }, some { target := 1051, numerator := 174538665206862087098204160 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 14 = expected := by
  rfl

end Left14

namespace Left15

/-- Producer-proposed routed output for left symbol 15; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 1062, numerator := 157812043124537803751292928 }, some { target := 1063, numerator := 178174887398671713912750080 }, some { target := 1064, numerator := 152721332056004326210928640 }, some { target := 1065, numerator := 2010830872070723628443893760 }, some { target := 1066, numerator := 178174887398671713912750080 }, some { target := 1067, numerator := 152721332056004326210928640 }, some { target := 1068, numerator := 178174887398671713912750080 }, some { target := 1069, numerator := 178174887398671713912750080 }, some { target := 1070, numerator := 7386621760442075911068581888 }, some { target := 1071, numerator := 183265598467205191453114368 }, some { target := 1072, numerator := 2010830872070723628443893760 }, some { target := 1073, numerator := 7386621760442075911068581888 }, some { target := 1074, numerator := 157812043124537803751292928 }, some { target := 1075, numerator := 178174887398671713912750080 }, some { target := 1076, numerator := 183265598467205191453114368 }, some { target := 1077, numerator := 178174887398671713912750080 }]

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

end Slot23

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8.Parent0
