import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch1Chunk4Parent2LocalDataBase

/-! Line-budgeted parent-local routing slots, part 4, for region 1, branch 1,
parent 20; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4.Parent2

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Slot18

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨18, 1772, #[3506505252864, 0, 137230932770816, 0, 0, 137230983102464, 0, 0, 0, 0, 0, 0, 3506555584512, 0, 0, 0, 0, 0, 0], #[412316860416, 5978594476032, 10582799417344, 343597383680, 6597069766656, 343597383680, 10514079940608, 10995116277760, 6597069766656, 168431437479936, 10788957847552, 5978594476032, 10514079940608, 343597383680, 10788957847552, 343597383680, 10514079940608, 10995116277760, 412316860416]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes

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
        4 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total4.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 56, numerator := 2561942071774567303194083328 }, some { target := 57, numerator := 37148160040731225896314208256 }, some { target := 58, numerator := 65756513175547227448648138752 }, some { target := 59, numerator := 2134951726478806085995069440 }, some { target := 60, numerator := 40991073148393076851105333248 }, some { target := 61, numerator := 2134951726478806085995069440 }, some { target := 62, numerator := 65329522830251466231449124864 }, some { target := 63, numerator := 68318455247321794751842222080 }, some { target := 64, numerator := 40991073148393076851105333248 }, some { target := 65, numerator := 1046553336319910743354783039488 }, some { target := 66, numerator := 67037484211434511100245180416 }, some { target := 67, numerator := 37148160040731225896314208256 }, some { target := 68, numerator := 65329522830251466231449124864 }, some { target := 69, numerator := 2134951726478806085995069440 }, some { target := 70, numerator := 67037484211434511100245180416 }, some { target := 71, numerator := 2134951726478806085995069440 }, some { target := 72, numerator := 65329522830251466231449124864 }, some { target := 73, numerator := 68318455247321794751842222080 }, some { target := 74, numerator := 2561942071774567303194083328 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left2

/-- Producer-proposed routed output for left symbol 2; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 152, numerator := 100264415667783020840623276032 }, some { target := 153, numerator := 1453834027182853802189037502464 }, some { target := 154, numerator := 2573453335473097534909330751488 }, some { target := 155, numerator := 83553679723152517367186063360 }, some { target := 156, numerator := 1604230650684528333449972416512 }, some { target := 157, numerator := 83553679723152517367186063360 }, some { target := 158, numerator := 2556742599528467031435893538816 }, some { target := 159, numerator := 2673717751140880555749954027520 }, some { target := 160, numerator := 1604230650684528333449972416512 }, some { target := 161, numerator := 40958013800289364013394608259072 }, some { target := 162, numerator := 2623585543306989045329642389504 }, some { target := 163, numerator := 1453834027182853802189037502464 }, some { target := 164, numerator := 2556742599528467031435893538816 }, some { target := 165, numerator := 83553679723152517367186063360 }, some { target := 166, numerator := 2623585543306989045329642389504 }, some { target := 167, numerator := 83553679723152517367186063360 }, some { target := 168, numerator := 2556742599528467031435893538816 }, some { target := 169, numerator := 2673717751140880555749954027520 }, some { target := 170, numerator := 100264415667783020840623276032 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 2 = expected := by
  rfl

end Left2

namespace Left5

/-- Producer-proposed routed output for left symbol 5; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 283, numerator := 100264452441367331780614422528 }, some { target := 284, numerator := 1453834560399826310818909126656 }, some { target := 285, numerator := 2573454279328428182369103511552 }, some { target := 286, numerator := 83553710367806109817178685440 }, some { target := 287, numerator := 1604231239061877308489830760448 }, some { target := 288, numerator := 83553710367806109817178685440 }, some { target := 289, numerator := 2556743537254866960405667774464 }, some { target := 290, numerator := 2673718731769795514149717934080 }, some { target := 291, numerator := 1604231239061877308489830760448 }, some { target := 292, numerator := 40958028822298555032380991602688 }, some { target := 293, numerator := 2623586505549111848259410722816 }, some { target := 294, numerator := 1453834560399826310818909126656 }, some { target := 295, numerator := 2556743537254866960405667774464 }, some { target := 296, numerator := 83553710367806109817178685440 }, some { target := 297, numerator := 2623586505549111848259410722816 }, some { target := 298, numerator := 83553710367806109817178685440 }, some { target := 299, numerator := 2556743537254866960405667774464 }, some { target := 300, numerator := 2673718731769795514149717934080 }, some { target := 301, numerator := 100264452441367331780614422528 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 5 = expected := by
  rfl

end Left5

namespace Left12

/-- Producer-proposed routed output for left symbol 12; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 660, numerator := 2561978845358878243185229824 }, some { target := 661, numerator := 37148693257703734526185832448 }, some { target := 662, numerator := 65757457030877874908420898816 }, some { target := 663, numerator := 2134982371132398535987691520 }, some { target := 664, numerator := 40991661525742051890963677184 }, some { target := 665, numerator := 2134982371132398535987691520 }, some { target := 666, numerator := 65330460556651395201223360512 }, some { target := 667, numerator := 68319435876236753151606128640 }, some { target := 668, numerator := 40991661525742051890963677184 }, some { target := 669, numerator := 1046568358329101762341166383104 }, some { target := 670, numerator := 67038446453557314030013513728 }, some { target := 671, numerator := 37148693257703734526185832448 }, some { target := 672, numerator := 65330460556651395201223360512 }, some { target := 673, numerator := 2134982371132398535987691520 }, some { target := 674, numerator := 67038446453557314030013513728 }, some { target := 675, numerator := 2134982371132398535987691520 }, some { target := 676, numerator := 65330460556651395201223360512 }, some { target := 677, numerator := 68319435876236753151606128640 }, some { target := 678, numerator := 2561978845358878243185229824 }]

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

end Slot18

namespace Slot19

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨19, 452, #[69122129920, 22265714442240, 0, 236805236457472, 0, 0, 0, 0, 0, 0, 0, 22265781551104, 0, 0, 0, 0, 0, 0, 69122129920], #[2130303778816, 2405181685760, 2061584302080, 27144193310720, 2405181685760, 2061584302080, 2405181685760, 2405181685760, 99711960743936, 2473901162496, 27144193310720, 99711960743936, 2130303778816, 2405181685760, 2473901162496, 2405181685760, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes

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
        3 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total3.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 110, numerator := 66557512824910696090173440 }, some { target := 111, numerator := 75145578995866914940518400 }, some { target := 112, numerator := 64410496282171641377587200 }, some { target := 113, numerator := 848071534381926611471564800 }, some { target := 114, numerator := 75145578995866914940518400 }, some { target := 115, numerator := 64410496282171641377587200 }, some { target := 116, numerator := 75145578995866914940518400 }, some { target := 117, numerator := 75145578995866914940518400 }, some { target := 118, numerator := 3115321003514368387962634240 }, some { target := 119, numerator := 77292595538605969653104640 }, some { target := 120, numerator := 848071534381926611471564800 }, some { target := 121, numerator := 3115321003514368387962634240 }, some { target := 122, numerator := 66557512824910696090173440 }, some { target := 123, numerator := 75145578995866914940518400 }, some { target := 124, numerator := 77292595538605969653104640 }, some { target := 125, numerator := 75145578995866914940518400 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 206, numerator := 21439596497682519710949703680 }, some { target := 207, numerator := 24205996045770586770427084800 }, some { target := 208, numerator := 20747996610660502946080358400 }, some { target := 209, numerator := 273181955373696622123391385600 }, some { target := 210, numerator := 24205996045770586770427084800 }, some { target := 211, numerator := 20747996610660502946080358400 }, some { target := 212, numerator := 24205996045770586770427084800 }, some { target := 213, numerator := 24205996045770586770427084800 }, some { target := 214, numerator := 1003511436068946325825420001280 }, some { target := 215, numerator := 24897595932792603535296430080 }, some { target := 216, numerator := 273181955373696622123391385600 }, some { target := 217, numerator := 1003511436068946325825420001280 }, some { target := 218, numerator := 21439596497682519710949703680 }, some { target := 219, numerator := 24205996045770586770427084800 }, some { target := 220, numerator := 24897595932792603535296430080 }, some { target := 221, numerator := 24205996045770586770427084800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left3

/-- Producer-proposed routed output for left symbol 3; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 302, numerator := 228019124711083592917087944704 }, some { target := 303, numerator := 257440947254449217809615421440 }, some { target := 304, numerator := 220663669075242186693956075520 }, some { target := 305, numerator := 2905404976157355458137088327680 }, some { target := 306, numerator := 257440947254449217809615421440 }, some { target := 307, numerator := 220663669075242186693956075520 }, some { target := 308, numerator := 257440947254449217809615421440 }, some { target := 309, numerator := 257440947254449217809615421440 }, some { target := 310, numerator := 10672766127605880429764342185984 }, some { target := 311, numerator := 264796402890290624032747290624 }, some { target := 312, numerator := 2905404976157355458137088327680 }, some { target := 313, numerator := 10672766127605880429764342185984 }, some { target := 314, numerator := 228019124711083592917087944704 }, some { target := 315, numerator := 257440947254449217809615421440 }, some { target := 316, numerator := 264796402890290624032747290624 }, some { target := 317, numerator := 257440947254449217809615421440 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 3 = expected := by
  rfl

end Left3

namespace Left11

/-- Producer-proposed routed output for left symbol 11; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 679, numerator := 21439661116627009915509014528 }, some { target := 680, numerator := 24206069002643398291703726080 }, some { target := 681, numerator := 20748059145122912821460336640 }, some { target := 682, numerator := 273182778744118352149227765760 }, some { target := 683, numerator := 24206069002643398291703726080 }, some { target := 684, numerator := 20748059145122912821460336640 }, some { target := 685, numerator := 24206069002643398291703726080 }, some { target := 686, numerator := 24206069002643398291703726080 }, some { target := 687, numerator := 1003514460652444883464631615488 }, some { target := 688, numerator := 24897670974147495385752403968 }, some { target := 689, numerator := 273182778744118352149227765760 }, some { target := 690, numerator := 1003514460652444883464631615488 }, some { target := 691, numerator := 21439661116627009915509014528 }, some { target := 692, numerator := 24206069002643398291703726080 }, some { target := 693, numerator := 24897670974147495385752403968 }, some { target := 694, numerator := 24206069002643398291703726080 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 11 = expected := by
  rfl

end Left11

namespace Left18

/-- Producer-proposed routed output for left symbol 18; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 966, numerator := 66557512824910696090173440 }, some { target := 967, numerator := 75145578995866914940518400 }, some { target := 968, numerator := 64410496282171641377587200 }, some { target := 969, numerator := 848071534381926611471564800 }, some { target := 970, numerator := 75145578995866914940518400 }, some { target := 971, numerator := 64410496282171641377587200 }, some { target := 972, numerator := 75145578995866914940518400 }, some { target := 973, numerator := 75145578995866914940518400 }, some { target := 974, numerator := 3115321003514368387962634240 }, some { target := 975, numerator := 77292595538605969653104640 }, some { target := 976, numerator := 848071534381926611471564800 }, some { target := 977, numerator := 3115321003514368387962634240 }, some { target := 978, numerator := 66557512824910696090173440 }, some { target := 979, numerator := 75145578995866914940518400 }, some { target := 980, numerator := 77292595538605969653104640 }, some { target := 981, numerator := 75145578995866914940518400 }]

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
def data : BetaFourLocalSlotData := ⟨20, 7, #[797874061312, 139939614294016, 0, 0, 0, 0, 139939631071232, 0, 0, 0, 0, 0, 0, 0, 797857284096, 0, 0, 0, 0], #[1649267441664, 34428457844736, 1786706395136, 37039797960704, 55456617725952, 1717986918400, 55456617725952, 57793079934976, 34428457844736, 1717986918400, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

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
  MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes

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
        2 by rfl]
  exact MatrixMultiplication.Generated.TotalQuotientExponentLevelFourTernarySupportData.Length4.Total2.codes_eq

/-- This serialized slot has positive split weight. -/
theorem split_ne : data.splitNumerator ≠ 0 := by
  simp [data]

namespace Left0

/-- Producer-proposed routed output for left symbol 0; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 257, numerator := 9211353983090754035122176 }, some { target := 258, numerator := 192287014397019490483175424 }, some { target := 259, numerator := 9978966815014983538049024 }, some { target := 260, numerator := 206871658203579851038785536 }, some { target := 261, numerator := 309731777681426604430983168 }, some { target := 262, numerator := 9595160399052868786585600 }, some { target := 263, numerator := 309731777681426604430983168 }, some { target := 264, numerator := 322781195824138505980739584 }, some { target := 265, numerator := 192287014397019490483175424 }, some { target := 266, numerator := 9595160399052868786585600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 0 = expected := by
  rfl

end Left0

namespace Left1

/-- Producer-proposed routed output for left symbol 1; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 353, numerator := 1615584947578970856769978368 }, some { target := 354, numerator := 33725335780711016635073298432 }, some { target := 355, numerator := 1750217026543885094834143232 }, some { target := 356, numerator := 36283345281044387158292430848 }, some { target := 357, numerator := 54324043862342895058890522624 }, some { target := 358, numerator := 1682900987061427975802060800 }, some { target := 359, numerator := 54324043862342895058890522624 }, some { target := 360, numerator := 56612789204746437105981325312 }, some { target := 361, numerator := 33725335780711016635073298432 }, some { target := 362, numerator := 1682900987061427975802060800 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 1 = expected := by
  rfl

end Left1

namespace Left6

/-- Producer-proposed routed output for left symbol 6; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 695, numerator := 1615585141269783630720270336 }, some { target := 696, numerator := 33725339824006733291285643264 }, some { target := 697, numerator := 1750217236375598933280292864 }, some { target := 698, numerator := 36283349631017224039926071296 }, some { target := 699, numerator := 54324050375196474582969090048 }, some { target := 700, numerator := 1682901188822691282000281600 }, some { target := 701, numerator := 54324050375196474582969090048 }, some { target := 702, numerator := 56612795991995334726489473024 }, some { target := 703, numerator := 33725339824006733291285643264 }, some { target := 704, numerator := 1682901188822691282000281600 }]

/-- Kernel reduction checks this bounded fixed-left routing row. -/
theorem routed_eq :
    data.routedContributionsForLeftFromSupports
        ParentSupport.codes leftSupport rightSupport 6 = expected := by
  rfl

end Left6

namespace Left14

/-- Producer-proposed routed output for left symbol 14; at most nineteen entries. -/
def expected : List (Option BetaFourRoutedContribution) :=
  [some { target := 982, numerator := 9211160292277980084830208 }, some { target := 983, numerator := 192282971101302834270830592 }, some { target := 984, numerator := 9978756983301145091899392 }, some { target := 985, numerator := 206867308230742969405145088 }, some { target := 986, numerator := 309725264827847080352415744 }, some { target := 987, numerator := 9594958637789562588364800 }, some { target := 988, numerator := 309725264827847080352415744 }, some { target := 989, numerator := 322774408575240885472591872 }, some { target := 990, numerator := 192282971101302834270830592 }, some { target := 991, numerator := 9594958637789562588364800 }]

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

end Slot20

namespace Slot21

/-- Exact source data for this parent-local slot. -/
def data : BetaFourLocalSlotData := ⟨21, 0, #[2130303778816, 51608327028736, 39101382262784, 43568148250624, 2130303778816, 43568148250624, 43499428773888, 2130303778816, 51608327028736, 2130303778816, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[67207648247808, 73529840107520, 67207648247808, 73529840107520, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

/-- This zero-weight slot has no routed output. -/
def expectedRoutedContributions : List (Option BetaFourRoutedContribution) := []

/-- This serialized slot has zero split weight. -/
theorem split_eq : data.splitNumerator = 0 := by
  simp [data]

/-- Kernel reduction checks that the zero split suppresses the whole slot. -/
theorem routedContributions_eq :
    data.routedContributions parent coordinate = expectedRoutedContributions := by
  exact data.routedContributions_eq_nil_of_split_eq_zero parent coordinate split_eq

end Slot21

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4.Parent2
