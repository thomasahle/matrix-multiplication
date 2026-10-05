import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk1Parent0LocalDataBase

/-! Line-budgeted parent-local routing slots, part 2, for region 1, branch 2,
parent 5; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot8

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨8, 4, #[24086361145344, 0, 233302254419968, 0, 0, 0, 0, 24086361145344, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[3298534883328, 3229815406592, 2542620639232, 79920751443968, 2542620639232, 2542620639232, 2611340115968, 2611340115968, 44186623541248, 2405181685760, 79920751443968, 44186623541248, 3298534883328, 2542620639232, 2405181685760, 3229815406592, 0, 0, 0]⟩

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
  [some { target := 250, numerator := 317798809801413373961699328 }, some { target := 251, numerator := 311178001263883928670830592 }, some { target := 252, numerator := 244969915888589475762143232 }, some { target := 253, numerator := 7700000329146744873280339968 }, some { target := 254, numerator := 244969915888589475762143232 }, some { target := 255, numerator := 244969915888589475762143232 }, some { target := 256, numerator := 251590724426118921053011968 }, some { target := 257, numerator := 251590724426118921053011968 }, some { target := 258, numerator := 4257179889631433322028597248 }, some { target := 259, numerator := 231728298813530585180405760 }, some { target := 260, numerator := 7700000329146744873280339968 }, some { target := 261, numerator := 4257179889631433322028597248 }, some { target := 262, numerator := 317798809801413373961699328 }, some { target := 263, numerator := 244969915888589475762143232 }, some { target := 264, numerator := 231728298813530585180405760 }, some { target := 265, numerator := 311178001263883928670830592 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 562, numerator := 3078222498253314076773974016 }, some { target := 563, numerator := 3014092862873036700174516224 }, some { target := 564, numerator := 2372796509070262934179938304 }, some { target := 565, numerator := 74582765947262588985169412096 }, some { target := 566, numerator := 2372796509070262934179938304 }, some { target := 567, numerator := 2372796509070262934179938304 }, some { target := 568, numerator := 2436926144450540310779396096 }, some { target := 569, numerator := 2436926144450540310779396096 }, some { target := 570, numerator := 41235355549518353153451360256 }, some { target := 571, numerator := 2244537238309708180981022720 }, some { target := 572, numerator := 74582765947262588985169412096 }, some { target := 573, numerator := 41235355549518353153451360256 }, some { target := 574, numerator := 3078222498253314076773974016 }, some { target := 575, numerator := 2372796509070262934179938304 }, some { target := 576, numerator := 2244537238309708180981022720 }, some { target := 577, numerator := 3014092862873036700174516224 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left7

/-- Producer-proposed routed output for left symbol 7; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 925, numerator := 317798809801413373961699328 }, some { target := 926, numerator := 311178001263883928670830592 }, some { target := 927, numerator := 244969915888589475762143232 }, some { target := 928, numerator := 7700000329146744873280339968 }, some { target := 929, numerator := 244969915888589475762143232 }, some { target := 930, numerator := 244969915888589475762143232 }, some { target := 931, numerator := 251590724426118921053011968 }, some { target := 932, numerator := 251590724426118921053011968 }, some { target := 933, numerator := 4257179889631433322028597248 }, some { target := 934, numerator := 231728298813530585180405760 }, some { target := 935, numerator := 7700000329146744873280339968 }, some { target := 936, numerator := 4257179889631433322028597248 }, some { target := 937, numerator := 317798809801413373961699328 }, some { target := 938, numerator := 244969915888589475762143232 }, some { target := 939, numerator := 231728298813530585180405760 }, some { target := 940, numerator := 311178001263883928670830592 }]

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
def data : BetaFourLocalSlotData := ⟨9, 126, #[1661028270080, 139076460085248, 0, 0, 0, 0, 139076510416896, 0, 0, 0, 0, 0, 0, 0, 1660977938432, 0, 0, 0, 0], #[412316860416, 10995116277760, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 5978594476032, 10788957847552, 168431437479936, 6597069766656, 10995116277760, 10514079940608, 343597383680, 6597069766656, 343597383680, 10582799417344, 5978594476032, 412316860416]⟩

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
  [some { target := 121, numerator := 86293615134082268953313280 }, some { target := 122, numerator := 2301163070242193838755020800 }, some { target := 123, numerator := 2200487185919097858309488640 }, some { target := 124, numerator := 71911345945068557461094400 }, some { target := 125, numerator := 2258016262675152704278364160 }, some { target := 126, numerator := 71911345945068557461094400 }, some { target := 127, numerator := 2200487185919097858309488640 }, some { target := 128, numerator := 1251257419444192899823042560 }, some { target := 129, numerator := 2258016262675152704278364160 }, some { target := 130, numerator := 35250941782272606867428474880 }, some { target := 131, numerator := 1380697842145316303253012480 }, some { target := 132, numerator := 2301163070242193838755020800 }, some { target := 133, numerator := 2200487185919097858309488640 }, some { target := 134, numerator := 71911345945068557461094400 }, some { target := 135, numerator := 1380697842145316303253012480 }, some { target := 136, numerator := 71911345945068557461094400 }, some { target := 137, numerator := 2214869455108111569801707520 }, some { target := 138, numerator := 1251257419444192899823042560 }, some { target := 139, numerator := 86293615134082268953313280 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 196, numerator := 7225289741895194979669639168 }, some { target := 197, numerator := 192674393117205199457857044480 }, some { target := 198, numerator := 184244888418327471981575798784 }, some { target := 199, numerator := 6021074784912662483058032640 }, some { target := 200, numerator := 189061748246257601968022224896 }, some { target := 201, numerator := 6021074784912662483058032640 }, some { target := 202, numerator := 184244888418327471981575798784 }, some { target := 203, numerator := 104766701257480327205209767936 }, some { target := 204, numerator := 189061748246257601968022224896 }, some { target := 205, numerator := 2951530859564187149195047600128 }, some { target := 206, numerator := 115604635870323119674714226688 }, some { target := 207, numerator := 192674393117205199457857044480 }, some { target := 208, numerator := 184244888418327471981575798784 }, some { target := 209, numerator := 6021074784912662483058032640 }, some { target := 210, numerator := 115604635870323119674714226688 }, some { target := 211, numerator := 6021074784912662483058032640 }, some { target := 212, numerator := 185449103375310004478187405312 }, some { target := 213, numerator := 104766701257480327205209767936 }, some { target := 214, numerator := 7225289741895194979669639168 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 508, numerator := 7225292356721167427998580736 }, some { target := 509, numerator := 192674462845897798079962152960 }, some { target := 510, numerator := 184244955096389769413963808768 }, some { target := 511, numerator := 6021076963934306189998817280 }, some { target := 512, numerator := 189061816667537214365962862592 }, some { target := 513, numerator := 6021076963934306189998817280 }, some { target := 514, numerator := 184244955096389769413963808768 }, some { target := 515, numerator := 104766739172456927705979420672 }, some { target := 516, numerator := 189061816667537214365962862592 }, some { target := 517, numerator := 2951531927720596894337420230656 }, some { target := 518, numerator := 115604677707538678847977291776 }, some { target := 519, numerator := 192674462845897798079962152960 }, some { target := 520, numerator := 184244955096389769413963808768 }, some { target := 521, numerator := 6021076963934306189998817280 }, some { target := 522, numerator := 115604677707538678847977291776 }, some { target := 523, numerator := 6021076963934306189998817280 }, some { target := 524, numerator := 185449170489176630651963572224 }, some { target := 525, numerator := 104766739172456927705979420672 }, some { target := 526, numerator := 7225292356721167427998580736 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 906, numerator := 86291000308109820624371712 }, some { target := 907, numerator := 2301093341549595216649912320 }, some { target := 908, numerator := 2200420507856800425921478656 }, some { target := 909, numerator := 71909166923424850520309760 }, some { target := 910, numerator := 2257947841395540306337726464 }, some { target := 911, numerator := 71909166923424850520309760 }, some { target := 912, numerator := 2200420507856800425921478656 }, some { target := 913, numerator := 1251219504467592399053389824 }, some { target := 914, numerator := 2257947841395540306337726464 }, some { target := 915, numerator := 35249873625862861725055844352 }, some { target := 916, numerator := 1380656004929757129989947392 }, some { target := 917, numerator := 2301093341549595216649912320 }, some { target := 918, numerator := 2200420507856800425921478656 }, some { target := 919, numerator := 71909166923424850520309760 }, some { target := 920, numerator := 1380656004929757129989947392 }, some { target := 921, numerator := 71909166923424850520309760 }, some { target := 922, numerator := 2214802341241485396025540608 }, some { target := 923, numerator := 1251219504467592399053389824 }, some { target := 924, numerator := 86291000308109820624371712 }]

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
def data : BetaFourLocalSlotData := ⟨10, 240, #[209765531648, 21993537667072, 0, 237068353536000, 0, 0, 0, 0, 0, 0, 0, 21993554444288, 0, 0, 0, 0, 0, 0, 209765531648], #[2405181685760, 2473901162496, 2405181685760, 2130303778816, 99711960743936, 27144193310720, 2473901162496, 99711960743936, 2405181685760, 2405181685760, 2061584302080, 2405181685760, 27144193310720, 2061584302080, 2405181685760, 2130303778816, 0, 0, 0]⟩

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
  [some { target := 34, numerator := 121085811605635025023795200 }, some { target := 35, numerator := 124545406222938882881617920 }, some { target := 36, numerator := 121085811605635025023795200 }, some { target := 37, numerator := 107247433136419593592504320 }, some { target := 38, numerator := 5019871789707897751700766720 }, some { target := 39, numerator := 1366539873835023853839974400 }, some { target := 40, numerator := 124545406222938882881617920 }, some { target := 41, numerator := 5019871789707897751700766720 }, some { target := 42, numerator := 121085811605635025023795200 }, some { target := 43, numerator := 121085811605635025023795200 }, some { target := 44, numerator := 103787838519115735734681600 }, some { target := 45, numerator := 121085811605635025023795200 }, some { target := 46, numerator := 1366539873835023853839974400 }, some { target := 47, numerator := 103787838519115735734681600 }, some { target := 48, numerator := 121085811605635025023795200 }, some { target := 49, numerator := 107247433136419593592504320 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 79, numerator := 12695628960459429744790732800 }, some { target := 80, numerator := 13058361216472556308927610880 }, some { target := 81, numerator := 12695628960459429744790732800 }, some { target := 82, numerator := 11244699936406923488243220480 }, some { target := 83, numerator := 526324503475046644562610094080 }, some { target := 84, numerator := 143279241125184992834066841600 }, some { target := 85, numerator := 13058361216472556308927610880 }, some { target := 86, numerator := 526324503475046644562610094080 }, some { target := 87, numerator := 12695628960459429744790732800 }, some { target := 88, numerator := 12695628960459429744790732800 }, some { target := 89, numerator := 10881967680393796924106342400 }, some { target := 90, numerator := 12695628960459429744790732800 }, some { target := 91, numerator := 143279241125184992834066841600 }, some { target := 92, numerator := 10881967680393796924106342400 }, some { target := 93, numerator := 12695628960459429744790732800 }, some { target := 94, numerator := 11244699936406923488243220480 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 154, numerator := 136846190927535392843366400000 }, some { target := 155, numerator := 140756082096893546924605440000 }, some { target := 156, numerator := 136846190927535392843366400000 }, some { target := 157, numerator := 121206626250102776518410240000 }, some { target := 158, numerator := 5673252086738681571877847040000 }, some { target := 159, numerator := 1544407011896470862089420800000 }, some { target := 160, numerator := 140756082096893546924605440000 }, some { target := 161, numerator := 5673252086738681571877847040000 }, some { target := 162, numerator := 136846190927535392843366400000 }, some { target := 163, numerator := 136846190927535392843366400000 }, some { target := 164, numerator := 117296735080744622437171200000 }, some { target := 165, numerator := 136846190927535392843366400000 }, some { target := 166, numerator := 1544407011896470862089420800000 }, some { target := 167, numerator := 117296735080744622437171200000 }, some { target := 168, numerator := 136846190927535392843366400000 }, some { target := 169, numerator := 121206626250102776518410240000 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 492, numerator := 12695638645000068442305331200 }, some { target := 493, numerator := 13058371177714356112085483520 }, some { target := 494, numerator := 12695638645000068442305331200 }, some { target := 495, numerator := 11244708514142917763184721920 }, some { target := 496, numerator := 526324904968431408851001016320 }, some { target := 497, numerator := 143279350422143629563160166400 }, some { target := 498, numerator := 13058371177714356112085483520 }, some { target := 499, numerator := 526324904968431408851001016320 }, some { target := 500, numerator := 12695638645000068442305331200 }, some { target := 501, numerator := 12695638645000068442305331200 }, some { target := 502, numerator := 10881975981428630093404569600 }, some { target := 503, numerator := 12695638645000068442305331200 }, some { target := 504, numerator := 143279350422143629563160166400 }, some { target := 505, numerator := 10881975981428630093404569600 }, some { target := 506, numerator := 12695638645000068442305331200 }, some { target := 507, numerator := 11244708514142917763184721920 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 890, numerator := 121085811605635025023795200 }, some { target := 891, numerator := 124545406222938882881617920 }, some { target := 892, numerator := 121085811605635025023795200 }, some { target := 893, numerator := 107247433136419593592504320 }, some { target := 894, numerator := 5019871789707897751700766720 }, some { target := 895, numerator := 1366539873835023853839974400 }, some { target := 896, numerator := 124545406222938882881617920 }, some { target := 897, numerator := 5019871789707897751700766720 }, some { target := 898, numerator := 121085811605635025023795200 }, some { target := 899, numerator := 121085811605635025023795200 }, some { target := 900, numerator := 103787838519115735734681600 }, some { target := 901, numerator := 121085811605635025023795200 }, some { target := 902, numerator := 1366539873835023853839974400 }, some { target := 903, numerator := 103787838519115735734681600 }, some { target := 904, numerator := 121085811605635025023795200 }, some { target := 905, numerator := 107247433136419593592504320 }]

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
def data : BetaFourLocalSlotData := ⟨11, 29, #[3909644976128, 0, 136827826601984, 0, 0, 136827893710848, 0, 0, 0, 0, 0, 0, 3909611421696, 0, 0, 0, 0, 0, 0], #[1717986918400, 34428457844736, 57793079934976, 55456617725952, 1717986918400, 55456617725952, 37039797960704, 1786706395136, 34428457844736, 1649267441664, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 10, numerator := 194784848812709344234700800 }, some { target := 11, numerator := 3903488370206695258463404032 }, some { target := 12, numerator := 6552562314059542340055334912 }, some { target := 13, numerator := 6287654919674257631896141824 }, some { target := 14, numerator := 194784848812709344234700800 }, some { target := 15, numerator := 6287654919674257631896141824 }, some { target := 16, numerator := 4199561340402013461700149248 }, some { target := 17, numerator := 202576242765217718004088832 }, some { target := 18, numerator := 3903488370206695258463404032 }, some { target := 19, numerator := 186993454860200970465312768 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 55, numerator := 6816984069084049029097062400 }, some { target := 56, numerator := 136612360744444342543105130496 }, some { target := 57, numerator := 229323344083987409338825179136 }, some { target := 58, numerator := 220052245750033102659253174272 }, some { target := 59, numerator := 6816984069084049029097062400 }, some { target := 60, numerator := 220052245750033102659253174272 }, some { target := 61, numerator := 146974176529452097067332665344 }, some { target := 62, numerator := 7089663431847410990260944896 }, some { target := 63, numerator := 136612360744444342543105130496 }, some { target := 64, numerator := 6544304706320687067933179904 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 144, numerator := 6816987412556412388953292800 }, some { target := 145, numerator := 136612427747630504274623987712 }, some { target := 146, numerator := 229323456558397712764388769792 }, some { target := 147, numerator := 220052353677320991915412291584 }, some { target := 148, numerator := 6816987412556412388953292800 }, some { target := 149, numerator := 220052353677320991915412291584 }, some { target := 150, numerator := 146974248614716251105832992768 }, some { target := 151, numerator := 7089666909058668884511424512 }, some { target := 152, numerator := 136612427747630504274623987712 }, some { target := 153, numerator := 6544307916054155893395161088 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 482, numerator := 194783177076527664306585600 }, some { target := 483, numerator := 3903454868613614392703975424 }, some { target := 484, numerator := 6552506076854390627273539584 }, some { target := 485, numerator := 6287600956030313003816583168 }, some { target := 486, numerator := 194783177076527664306585600 }, some { target := 487, numerator := 6287600956030313003816583168 }, some { target := 488, numerator := 4199525297769936442449985536 }, some { target := 489, numerator := 202574504159588770878849024 }, some { target := 490, numerator := 3903454868613614392703975424 }, some { target := 491, numerator := 186991849993466557734322176 }]

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

end Slot11

namespace Slot12

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨12, 1, #[51941589647360, 0, 0, 177591814193152, 0, 51941572870144, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[73529840107520, 67207648247808, 73529840107520, 67207648247808, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  [some { target := 1, numerator := 3819256781700796941284147200 }, some { target := 2, numerator := 3490872086451756456612986880 }, some { target := 3, numerator := 3819256781700796941284147200 }, some { target := 4, numerator := 3490872086451756456612986880 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 51, numerator := 13058297702026867517727703040 }, some { target := 52, numerator := 11935528179983435918072610816 }, some { target := 53, numerator := 13058297702026867517727703040 }, some { target := 54, numerator := 11935528179983435918072610816 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 140, numerator := 3819255548074787011957882880 }, some { target := 141, numerator := 3490870958894524951116644352 }, some { target := 142, numerator := 3819255548074787011957882880 }, some { target := 143, numerator := 3490870958894524951116644352 }]

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

end Slot12

namespace Slot13

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨13, 0, #[140769314734080, 0, 140705661976576, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[281474976710656, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1.Parent0
